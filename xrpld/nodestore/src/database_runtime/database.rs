use crate::database_runtime::node_object_cache::NodeObjectCache;
use crate::{
    Backend, FetchReport, FetchType, JournalLevel, NodeObject, NodeObjectType, NodeStoreJournal,
    Scheduler, Task, batch_write_preallocation_size,
};
use basics::base_uint::Uint256;
use basics::basic_config::{Section, get};
use basics::blob::Blob;
use protocol::JsonValue;
use std::any::Any;
use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

const XRP_LEDGER_EARLIEST_SEQ: u32 = 32_570;
/// Rust adaptation envelope for one fixed-size `AsyncReadWork` owner. This is
/// deliberately separate from the queue record so the default byte budget can
/// admit the configured callback count without accepting arbitrary closures.
const DEFAULT_ASYNC_READ_WORK_BYTES: usize = 256;
/// Derive one default asynchronous-read ownership budget from the existing
/// NodeStore worker and `rq_bundle` resource contracts. Rippled batches by
/// hash (`Database::asyncFetch`) but does not publish an admission number, so
/// this is a bounded Rust adaptation rather than numeric parity.
fn default_read_queue_budget(read_threads: usize, request_bundle: usize) -> Result<usize, String> {
    read_threads
        .checked_mul(request_bundle)
        .ok_or_else(|| "NodeStore async read queue budget overflow".to_owned())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReadQueueSnapshot {
    pub queued_keys: usize,
    pub outstanding_callbacks: usize,
    pub outstanding_bytes: usize,
    pub key_limit: usize,
    pub callback_limit: usize,
    pub byte_limit: usize,
    pub rejected: u64,
    pub cancelled: u64,
}

/// Typed terminal work retained by the NodeStore async-read queue.
///
/// This intentionally replaces an erased callback closure. The runtime measures
/// the concrete boxed work object with `size_of_val` at admission and mints the
/// accompanying [`ReadWorkPermit`] itself; callers cannot declare an arbitrary
/// closure size. Implementations must keep all retained ownership in their
/// concrete fixed-size fields. Indirect `Arc` ownership is allowed only for a
/// separately bounded owner, never for an unbounded callback capture.
pub trait AsyncReadWork: Send + 'static {
    fn complete(&mut self, result: Option<Arc<NodeObject>>);
}

/// Runtime-owned byte reservation for one accepted async-read work item.
/// It has no public constructor and releases exactly once when the queued,
/// faulted, stopped, rejected, or completed request is consumed.
struct ReadWorkPermit {
    inner: Arc<DatabaseInner>,
    bytes: usize,
}

impl Drop for ReadWorkPermit {
    fn drop(&mut self) {
        self.inner
            .outstanding_read_bytes
            .fetch_sub(self.bytes, Ordering::AcqRel);
    }
}

/// Immutable storage-side identity carried across scheduler ownership. The
/// acquisition actor supplies its ID; storage supplies the observed monotonic
/// store generation. No actor state is retained by this handoff.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PersistenceIdentity {
    pub acquisition_id: u64,
    pub persistence_generation: u64,
    pub store_generation: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PersistenceOutcome {
    Durable,
    Fault(Arc<str>),
    Cancelled,
}

/// Concrete persistence work admitted by the NodeStore scheduler.
///
/// This replaces the erased `FnOnce` write callback boundary. Implementors
/// retain only named, inspectable fields and report the capacity of their
/// actual write payload (vectors and byte buffers), never a trait-object or
/// closure shell. The scheduler owns the resulting reservation until this
/// item runs, panics, is rejected, or is dropped during stop.
pub trait PersistenceWork: Send + 'static {
    /// Exact retained write-payload capacity, including every vector record
    /// and byte buffer owned by this item. Fixed identity/state fields are
    /// accounted by the concrete task record itself.
    fn retained_payload_bytes(&self) -> usize;

    /// Consume the one admitted work record.
    fn run(self: Box<Self>);
}

/// Backward-compatible name for the typed NodeStore persistence handoff.
pub type ScheduledWrite = Box<dyn PersistenceWork>;

struct ScheduledWriteTask {
    work: Mutex<Option<ScheduledWrite>>,
    payload_bytes: usize,
}

impl ScheduledWriteTask {
    fn new(work: ScheduledWrite) -> Self {
        let payload_bytes = work.retained_payload_bytes();
        Self {
            work: Mutex::new(Some(work)),
            payload_bytes,
        }
    }
}

impl Task for ScheduledWriteTask {
    fn perform_scheduled_task(&self) {
        if let Some(work) = self
            .work
            .lock()
            .expect("scheduled NodeStore write task mutex must not be poisoned")
            .take()
        {
            work.run();
        }
    }

    fn retained_bytes(&self) -> usize {
        self.payload_bytes
    }
}

pub trait DatabaseSource: Send + Sync + 'static {
    fn for_each(&self, callback: &mut dyn FnMut(Arc<NodeObject>));
}

pub trait DatabaseImporter: Send + Sync + 'static {
    fn import_database(&self, source: &dyn DatabaseSource);
}

/// reference-style owner surface shared by the concrete Database wrappers.
pub trait Database: DatabaseSource + DatabaseImporter + Send + Sync + 'static {
    fn get_name(&self) -> String;

    fn get_write_load(&self) -> i32;

    fn store(
        &self,
        object_type: NodeObjectType,
        data: Blob,
        hash: Uint256,
        ledger_seq: u32,
    ) -> Result<(), String>;

    fn store_batch(&self, objects: Vec<(NodeObjectType, Blob, Uint256, u32)>)
    -> Result<(), String>;

    fn is_same_db(&self, first: u32, second: u32) -> bool;

    fn sync(&self);

    /// Checked durability barrier. The default preserves legacy databases;
    /// concrete fallible backends override through their database adapter.
    fn sync_result(&self) -> Result<(), String> {
        self.sync();
        Ok(())
    }

    /// Queue one write-owner task on the NodeStore scheduler. Callers use this
    /// for bounded write batches; it deliberately does not expose an
    /// acquisition-worker execution path.
    fn schedule_write(&self, write: ScheduledWrite) {
        write.run();
    }

    /// Stable nonzero identity for cache/read ownership. Rotating stores
    /// advance it before exposing a new writable/archive pairing; consumers
    /// must key asynchronous work by the value observed at admission.
    fn store_generation(&self) -> u64 {
        1
    }

    fn fetch_node_object(
        &self,
        hash: &Uint256,
        ledger_seq: u32,
        fetch_type: FetchType,
        duplicate: bool,
    ) -> Option<Arc<NodeObject>>;

    fn async_fetch(&self, hash: Uint256, ledger_seq: u32, work: Box<dyn AsyncReadWork>);

    fn stop(&self);

    fn is_stopping(&self) -> bool;

    fn earliest_ledger_seq(&self) -> u32;

    fn get_store_count(&self) -> u64;

    fn get_fetch_total_count(&self) -> u64;

    fn get_fetch_hit_count(&self) -> u64;

    fn get_store_size(&self) -> u64;

    fn get_fetch_size(&self) -> u64;

    fn add_counts_json(&self, obj: &mut BTreeMap<String, JsonValue>);

    fn get_counts_json(&self) -> JsonValue;

    fn fd_required(&self) -> i32;

    /// Returns the primary backend for snapshot export.
    fn export_backend(&self) -> Option<Arc<dyn Backend>> {
        None
    }
}

/// reference-style rotating owner extension.
pub trait DatabaseRotating: Database {
    /// Enable archive-read copy-forward for the complete rotation exposure
    /// window, from cache freshening until `rotate` returns.
    fn set_rotation_in_flight(&self, in_flight: bool);

    /// Copy archive-resident objects into the current writable generation as
    /// one bounded maintenance batch. Implementations must complete the write
    /// synchronously before returning so online deletion can safely rotate the
    /// archive afterward. The return value is the number of archive objects
    /// submitted to the writable backend; hashes already present there and
    /// hashes missing from both backends are not counted.
    fn copy_to_writable_batch(&self, hashes: &[Uint256]) -> Result<usize, String>;

    fn copy_to_writable_batch_detailed(
        &self,
        hashes: &[Uint256],
    ) -> Result<(usize, Vec<Uint256>), String>;

    fn store_account_nodes(&self, nodes: Vec<(Uint256, Blob)>) -> Result<(), String>;

    fn rotate(&self, new_backend: Box<dyn Backend>, callback: &mut dyn FnMut(&str, &str));
}

/// Backward-compatible alias while older Rust modules migrate to the direct
/// `Database` trait name.
pub trait DatabaseSurface: Database {}

impl<T> DatabaseSurface for T where T: Database + ?Sized {}

pub trait DatabaseDelegate: Send + Sync + 'static {
    fn is_same_db(&self, first: u32, second: u32) -> bool;

    /// Whether this request may be satisfied by the encoded-object cache.
    /// Copy-on-read (`duplicate`) requests are durable side-effect operations,
    /// so they always bypass the cache by default.
    fn cache_read_allowed(&self, duplicate: bool) -> bool {
        !duplicate
    }

    fn fetch_node_object(
        &self,
        hash: &Uint256,
        ledger_seq: u32,
        fetch_report: &mut FetchReport,
        duplicate: bool,
        journal: &dyn NodeStoreJournal,
    ) -> Option<Arc<NodeObject>>;
}

struct AsyncReadRequest {
    ledger_seq: u32,
    work: Box<dyn AsyncReadWork>,
    _permit: ReadWorkPermit,
}

/// Fixed queue-record bytes charged in addition to the concrete typed work
/// object. This is a measured Rust-layout handoff, not a caller estimate.
pub const ASYNC_READ_WORK_QUEUE_OVERHEAD_BYTES: usize = std::mem::size_of::<AsyncReadRequest>();

#[derive(Default)]
struct ReadState {
    queue: BTreeMap<Uint256, Vec<AsyncReadRequest>>,
}

/// Decrements the one logical callback slot exactly once, including when a
/// callback panics. The callback itself is invoked outside every queue lock.
struct AsyncCallbackGuard {
    inner: Arc<DatabaseInner>,
}

impl Drop for AsyncCallbackGuard {
    fn drop(&mut self) {
        self.inner
            .outstanding_read_callbacks
            .fetch_sub(1, Ordering::AcqRel);
    }
}

struct DatabaseInner {
    delegate: Arc<dyn DatabaseDelegate>,
    scheduler: Arc<dyn Scheduler>,
    journal: Arc<dyn NodeStoreJournal>,
    earliest_ledger_seq: u32,
    request_bundle: usize,
    read_queue_key_limit: usize,
    read_queue_callback_limit: usize,
    read_queue_byte_limit: usize,
    node_object_cache: NodeObjectCache,
    read_state: Mutex<ReadState>,
    /// Queued plus worker-owned logical work items. It is reserved before a
    /// request enters the BTreeMap and released only after terminal delivery.
    outstanding_read_callbacks: AtomicUsize,
    /// Reservation for the concrete work-object allocation plus its queue
    /// record. It is paired one-for-one with `ReadWorkPermit`, not inferred
    /// from the callback count.
    outstanding_read_bytes: AtomicUsize,
    read_queue_rejected: AtomicU64,
    read_callbacks_cancelled: AtomicU64,
    store_generation: AtomicU64,
    read_condvar: Condvar,
    read_stopping: AtomicBool,
    live_threads: AtomicUsize,
    running_threads: AtomicUsize,
    store_count: AtomicU64,
    store_size: AtomicU64,
    fetch_total_count: AtomicU64,
    fetch_hit_count: AtomicU64,
    fetch_size: AtomicU64,
    fetch_duration_us: AtomicU64,
    store_duration_us: AtomicU64,
}

struct WorkerExitGuard {
    inner: Arc<DatabaseInner>,
}

impl WorkerExitGuard {
    fn new(inner: &Arc<DatabaseInner>) -> Self {
        Self {
            inner: Arc::clone(inner),
        }
    }
}

impl Drop for WorkerExitGuard {
    fn drop(&mut self) {
        self.inner.live_threads.fetch_sub(1, Ordering::Relaxed);
    }
}

impl DatabaseInner {
    fn is_stopping(&self) -> bool {
        self.read_stopping.load(Ordering::Relaxed)
    }

    fn store_stats(&self, count: u64, size: u64) {
        assert!(
            count <= size,
            "xrpl::NodeStore::Database::store_stats : valid inputs"
        );
        self.store_count.fetch_add(count, Ordering::Relaxed);
        self.store_size.fetch_add(size, Ordering::Relaxed);
    }

    fn fetch_node_object_from_delegate(
        &self,
        hash: &Uint256,
        ledger_seq: u32,
        fetch_report: &mut FetchReport,
        duplicate: bool,
    ) -> Option<Arc<NodeObject>> {
        self.delegate.fetch_node_object(
            hash,
            ledger_seq,
            fetch_report,
            duplicate,
            self.journal.as_ref(),
        )
    }

    fn fetch_node_object(
        &self,
        hash: &Uint256,
        ledger_seq: u32,
        fetch_type: FetchType,
        duplicate: bool,
    ) -> Option<Arc<NodeObject>> {
        let mut fetch_report = FetchReport::new(fetch_type);
        let begin = Instant::now();
        let node_object = if self.delegate.cache_read_allowed(duplicate) {
            let cache_generation = self.node_object_cache.generation();
            let cached = self.node_object_cache.get_or_load(*hash, || {
                self.fetch_node_object_from_delegate(hash, ledger_seq, &mut fetch_report, duplicate)
            });

            // A rotation can start after this request accepted a cacheable
            // read. Do not return an archive-sourced hit across that fence:
            // retry through the delegate so its copy-forward path runs.
            if self.node_object_cache.generation() == cache_generation
                && self.delegate.cache_read_allowed(duplicate)
            {
                cached
            } else {
                let node_object = self.fetch_node_object_from_delegate(
                    hash,
                    ledger_seq,
                    &mut fetch_report,
                    duplicate,
                );
                if let Some(object) = &node_object {
                    self.node_object_cache
                        .promote_for_hash(hash, Arc::clone(object));
                }
                node_object
            }
        } else {
            let node_object = self.fetch_node_object_from_delegate(
                hash,
                ledger_seq,
                &mut fetch_report,
                duplicate,
            );
            if let Some(object) = &node_object {
                self.node_object_cache
                    .promote_for_hash(hash, Arc::clone(object));
            }
            node_object
        };
        let elapsed = begin.elapsed();
        let elapsed_us = elapsed.as_micros() as u64;

        self.fetch_duration_us
            .fetch_add(elapsed_us, Ordering::Relaxed);
        if let Some(node_object) = &node_object {
            self.fetch_hit_count.fetch_add(1, Ordering::Relaxed);
            self.fetch_size
                .fetch_add(node_object.data().len() as u64, Ordering::Relaxed);
            fetch_report.was_found = true;
        }
        self.fetch_total_count.fetch_add(1, Ordering::Relaxed);
        fetch_report.elapsed = Duration::from_millis(elapsed.as_millis() as u64);
        self.scheduler.on_fetch(fetch_report);
        node_object
    }
}

/// Shared async-read runtime used by the concrete public database owners.
pub struct DatabaseRuntime {
    inner: Arc<DatabaseInner>,
    read_handles: Mutex<Vec<JoinHandle<()>>>,
}

impl DatabaseRuntime {
    pub fn new(
        delegate: Arc<dyn DatabaseDelegate>,
        scheduler: Arc<dyn Scheduler>,
        read_threads: usize,
        config: &Section,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Self, String> {
        assert!(
            read_threads != 0,
            "xrpl::NodeStore::Database::new : nonzero threads input"
        );

        let earliest_ledger_seq = get(config, "earliest_seq", XRP_LEDGER_EARLIEST_SEQ);
        if earliest_ledger_seq < 1 {
            return Err("Invalid earliest_seq".to_owned());
        }

        let request_bundle = get(config, "rq_bundle", 4i32);
        if !(1..=64).contains(&request_bundle) {
            return Err("Invalid rq_bundle".to_owned());
        }

        let node_object_cache = NodeObjectCache::from_config(config)?;
        let default_read_queue_budget =
            default_read_queue_budget(read_threads, request_bundle as usize)?;
        // Explicit operator settings may narrow or expand this shared logical
        // budget. Without them, queued keys and logical callbacks are both
        // bounded by worker concurrency times the configured request bundle.
        let read_queue_key_limit = get(config, "read_queue_max_keys", default_read_queue_budget);
        let read_queue_callback_limit = get(
            config,
            "read_queue_max_callbacks",
            default_read_queue_budget,
        );
        let default_read_queue_byte_limit = read_queue_callback_limit
            .checked_mul(std::mem::size_of::<AsyncReadRequest>() + DEFAULT_ASYNC_READ_WORK_BYTES)
            .ok_or_else(|| "NodeStore async read queue byte budget overflow".to_owned())?;
        let read_queue_byte_limit = get(
            config,
            "read_queue_max_bytes",
            default_read_queue_byte_limit,
        );
        if read_queue_key_limit == 0 || read_queue_callback_limit == 0 || read_queue_byte_limit == 0
        {
            return Err("NodeStore async read queue limits must be nonzero".to_owned());
        }

        let inner = Arc::new(DatabaseInner {
            delegate,
            scheduler,
            journal,
            earliest_ledger_seq,
            request_bundle: request_bundle as usize,
            read_queue_key_limit,
            read_queue_callback_limit,
            read_queue_byte_limit,
            node_object_cache,
            read_state: Mutex::new(ReadState::default()),
            outstanding_read_callbacks: AtomicUsize::new(0),
            outstanding_read_bytes: AtomicUsize::new(0),
            read_queue_rejected: AtomicU64::new(0),
            read_callbacks_cancelled: AtomicU64::new(0),
            // Generation zero remains reserved for legacy/unwired callers;
            // all storage handoff consumers observe a real nonzero value.
            store_generation: AtomicU64::new(1),
            read_condvar: Condvar::new(),
            read_stopping: AtomicBool::new(false),
            live_threads: AtomicUsize::new(read_threads.max(1)),
            running_threads: AtomicUsize::new(0),
            store_count: AtomicU64::new(0),
            store_size: AtomicU64::new(0),
            fetch_total_count: AtomicU64::new(0),
            fetch_hit_count: AtomicU64::new(0),
            fetch_size: AtomicU64::new(0),
            fetch_duration_us: AtomicU64::new(0),
            store_duration_us: AtomicU64::new(0),
        });

        let mut read_handles: Vec<JoinHandle<()>> = Vec::with_capacity(read_threads.max(1));
        for index in 1..=read_threads.max(1) {
            let worker_inner = inner.clone();
            let handle = match thread::Builder::new()
                .name(format!("db prefetch #{index}"))
                .spawn(move || worker_loop(worker_inner))
            {
                Ok(handle) => handle,
                Err(error) => {
                    inner.read_stopping.store(true, Ordering::Relaxed);
                    inner.read_condvar.notify_all();
                    for handle in read_handles.drain(..) {
                        let _ = handle.join();
                    }
                    return Err(format!("failed to spawn NodeStore read thread: {error}"));
                }
            };
            read_handles.push(handle);
        }

        Ok(Self {
            inner,
            read_handles: Mutex::new(read_handles),
        })
    }

    pub fn fetch_node_object(
        &self,
        hash: &Uint256,
        ledger_seq: u32,
        fetch_type: FetchType,
        duplicate: bool,
    ) -> Option<Arc<NodeObject>> {
        self.inner
            .fetch_node_object(hash, ledger_seq, fetch_type, duplicate)
    }

    pub fn schedule_write(&self, write: ScheduledWrite) {
        // Reject after stop instead of leaving an accepted persistence ticket
        // in an executor that can no longer run it. Dropping `write` invokes
        // the caller's completion guard exactly once.
        if self.inner.is_stopping() {
            return;
        }
        let task: Arc<dyn Task> = Arc::new(ScheduledWriteTask::new(write));
        if !self.inner.scheduler.try_schedule_task(Arc::clone(&task)) {
            // Dropping the sole task Arc settles its write closure/guard.
            drop(task);
        }
    }

    pub fn async_fetch(&self, hash: Uint256, ledger_seq: u32, work: Box<dyn AsyncReadWork>) {
        // This is measured from the concrete erased object, rather than a
        // caller-supplied estimate. `AsyncReadWork` is the stable agent-facing
        // handoff: the only retained completion payload must be its fixed-size
        // typed owner plus a NodeStore-issued permit.
        let work_bytes = std::mem::size_of_val(work.as_ref())
            .saturating_add(std::mem::size_of::<AsyncReadRequest>());
        let rejected = {
            let mut read_state = self
                .inner
                .read_state
                .lock()
                .expect("nodestore read queue mutex must not be poisoned");
            let new_hash = !read_state.queue.contains_key(&hash);
            let full = new_hash && read_state.queue.len() >= self.inner.read_queue_key_limit;
            let callbacks_full = self
                .inner
                .outstanding_read_callbacks
                .load(Ordering::Acquire)
                >= self.inner.read_queue_callback_limit;
            let bytes_full = self
                .inner
                .outstanding_read_bytes
                .load(Ordering::Acquire)
                .checked_add(work_bytes)
                .is_none_or(|total| total > self.inner.read_queue_byte_limit);
            if self.inner.is_stopping() || full || callbacks_full || bytes_full {
                self.inner
                    .read_queue_rejected
                    .fetch_add(1, Ordering::Relaxed);
                Some(work)
            } else {
                self.inner
                    .outstanding_read_callbacks
                    .fetch_add(1, Ordering::AcqRel);
                self.inner
                    .outstanding_read_bytes
                    .fetch_add(work_bytes, Ordering::AcqRel);
                read_state
                    .queue
                    .entry(hash)
                    .or_default()
                    .push(AsyncReadRequest {
                        ledger_seq,
                        work,
                        _permit: ReadWorkPermit {
                            inner: Arc::clone(&self.inner),
                            bytes: work_bytes,
                        },
                    });
                self.inner.read_condvar.notify_one();
                None
            }
        };
        if let Some(work) = rejected {
            self.inner
                .read_callbacks_cancelled
                .fetch_add(1, Ordering::Relaxed);
            deliver_rejected_async_work(&self.inner, work);
        }
    }

    pub fn import_internal(&self, dst_backend: &dyn Backend, src_db: &dyn DatabaseSource) {
        let mut batch = Vec::with_capacity(batch_write_preallocation_size);
        let store_batch = |batch: &mut Vec<Arc<NodeObject>>| {
            let begin = Instant::now();
            let result = catch_unwind(AssertUnwindSafe(|| dst_backend.store_batch_result(batch)));
            match result {
                Ok(Ok(())) => {
                    let size = batch
                        .iter()
                        .map(|node_object| node_object.data().len() as u64)
                        .sum();
                    self.inner.store_stats(batch.len() as u64, size);
                    for node_object in batch.iter() {
                        self.inner
                            .node_object_cache
                            .promote(Arc::clone(node_object));
                    }
                    self.inner
                        .store_duration_us
                        .fetch_add(begin.elapsed().as_micros() as u64, Ordering::Relaxed);
                    batch.clear();
                }
                Ok(Err(error)) => {
                    // Preserve the batch so callers that retry the import do
                    // not silently skip objects rejected by the destination.
                    self.inner.journal.log(
                        JournalLevel::Error,
                        &format!("import_internal batch write failed: {error}"),
                    );
                }
                Err(payload) => {
                    // Mirror reference importInternal: keep the batch intact when the
                    // destination write fails so a later retry still sees the
                    // full accumulated batch.
                    self.inner.journal.log(
                        JournalLevel::Error,
                        &format!(
                            "Exception caught in function import_internal. Error: {}",
                            panic_message(payload.as_ref())
                        ),
                    );
                }
            }
        };

        src_db.for_each(&mut |node_object| {
            batch.push(node_object);
            if batch.len() >= batch_write_preallocation_size {
                store_batch(&mut batch);
            }
        });

        if !batch.is_empty() {
            store_batch(&mut batch);
        }
    }

    pub fn stop(&self) {
        let first_stop = {
            let mut read_state = self
                .inner
                .read_state
                .lock()
                .expect("nodestore read queue mutex must not be poisoned");
            let first_stop = !self.inner.read_stopping.swap(true, Ordering::Relaxed);
            if first_stop {
                self.inner.journal.log(
                    JournalLevel::Debug,
                    "Clearing read queue because of stop request",
                );
                let callbacks = std::mem::take(&mut read_state.queue)
                    .into_values()
                    .flatten()
                    .collect::<Vec<_>>();
                (first_stop, callbacks)
            } else {
                (first_stop, Vec::new())
            }
        };

        if first_stop.0 {
            self.inner.read_condvar.notify_all();
            for request in first_stop.1 {
                self.inner
                    .read_callbacks_cancelled
                    .fetch_add(1, Ordering::Relaxed);
                deliver_async_work(&self.inner, request, None);
            }
        }

        self.inner.journal.log(
            JournalLevel::Debug,
            "Waiting for stop request to complete...",
        );

        let start = Instant::now();
        while self.inner.live_threads.load(Ordering::Acquire) != 0 {
            assert!(
                start.elapsed() < Duration::from_secs(30),
                "xrpl::NodeStore::Database::stop : maximum stop duration"
            );
            thread::yield_now();
        }

        let mut handles = self
            .read_handles
            .lock()
            .expect("nodestore thread handle mutex must not be poisoned");
        for handle in handles.drain(..) {
            let _ = handle.join();
        }

        self.inner.journal.log(
            JournalLevel::Debug,
            &format!(
                "Stop request completed in {} milliseconds",
                start.elapsed().as_millis()
            ),
        );
    }

    pub fn is_stopping(&self) -> bool {
        self.inner.is_stopping()
    }

    pub fn earliest_ledger_seq(&self) -> u32 {
        self.inner.earliest_ledger_seq
    }

    pub fn get_store_count(&self) -> u64 {
        self.inner.store_count.load(Ordering::Relaxed)
    }

    pub fn get_fetch_total_count(&self) -> u64 {
        self.inner.fetch_total_count.load(Ordering::Relaxed)
    }

    pub fn get_fetch_hit_count(&self) -> u64 {
        self.inner.fetch_hit_count.load(Ordering::Relaxed)
    }

    pub fn get_store_size(&self) -> u64 {
        self.inner.store_size.load(Ordering::Relaxed)
    }

    pub fn get_fetch_size(&self) -> u64 {
        self.inner.fetch_size.load(Ordering::Relaxed)
    }

    pub fn add_counts_json(&self, obj: &mut BTreeMap<String, JsonValue>) {
        let read_queue = self
            .inner
            .read_state
            .lock()
            .expect("nodestore read queue mutex must not be poisoned")
            .queue
            .len() as u64;

        obj.insert("read_queue".to_owned(), JsonValue::Unsigned(read_queue));
        obj.insert(
            "read_threads_total".to_owned(),
            JsonValue::Signed(self.inner.live_threads.load(Ordering::Relaxed) as i64),
        );
        obj.insert(
            "read_threads_running".to_owned(),
            JsonValue::Signed(self.inner.running_threads.load(Ordering::Relaxed) as i64),
        );
        obj.insert(
            "read_request_bundle".to_owned(),
            JsonValue::Signed(self.inner.request_bundle as i64),
        );
        obj.insert(
            "node_writes".to_owned(),
            JsonValue::String(self.get_store_count().to_string()),
        );
        obj.insert(
            "node_reads_total".to_owned(),
            JsonValue::String(self.get_fetch_total_count().to_string()),
        );
        obj.insert(
            "node_reads_hit".to_owned(),
            JsonValue::String(self.get_fetch_hit_count().to_string()),
        );
        obj.insert(
            "node_written_bytes".to_owned(),
            JsonValue::String(self.get_store_size().to_string()),
        );
        obj.insert(
            "node_read_bytes".to_owned(),
            JsonValue::String(self.get_fetch_size().to_string()),
        );
        obj.insert(
            "node_reads_duration_us".to_owned(),
            JsonValue::String(
                self.inner
                    .fetch_duration_us
                    .load(Ordering::Relaxed)
                    .to_string(),
            ),
        );
        self.inner.node_object_cache.add_counts_json(obj);
    }

    pub fn get_counts_json(&self) -> JsonValue {
        let mut obj = BTreeMap::new();
        self.add_counts_json(&mut obj);
        JsonValue::Object(obj)
    }

    pub fn read_queue_snapshot(&self) -> ReadQueueSnapshot {
        let queued_keys = self
            .inner
            .read_state
            .lock()
            .expect("nodestore read queue mutex must not be poisoned")
            .queue
            .len();
        ReadQueueSnapshot {
            queued_keys,
            outstanding_callbacks: self
                .inner
                .outstanding_read_callbacks
                .load(Ordering::Acquire),
            outstanding_bytes: self.inner.outstanding_read_bytes.load(Ordering::Acquire),
            key_limit: self.inner.read_queue_key_limit,
            callback_limit: self.inner.read_queue_callback_limit,
            byte_limit: self.inner.read_queue_byte_limit,
            rejected: self.inner.read_queue_rejected.load(Ordering::Relaxed),
            cancelled: self.inner.read_callbacks_cancelled.load(Ordering::Relaxed),
        }
    }

    pub(crate) fn store_stats(&self, count: u64, size: u64) {
        self.inner.store_stats(count, size);
    }

    pub(crate) fn promote_node_object(&self, object: Arc<NodeObject>) {
        self.inner.node_object_cache.promote(object);
    }

    pub(crate) fn invalidate_node_object_cache(&self) {
        self.inner.node_object_cache.invalidate_all();
    }

    /// Advance before a rotation changes which durable backend pairing owns a
    /// read. The returned value is never zero and is safe to retain in a
    /// `ReadKey` or persistence acknowledgement identity.
    pub(crate) fn advance_store_generation(&self) -> u64 {
        let mut observed = self.inner.store_generation.load(Ordering::Acquire);
        loop {
            let next = observed
                .checked_add(1)
                .expect("NodeStore storage generation overflow");
            match self.inner.store_generation.compare_exchange_weak(
                observed,
                next,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return next,
                Err(current) => observed = current,
            }
        }
    }

    pub fn store_generation(&self) -> u64 {
        self.inner.store_generation.load(Ordering::Acquire)
    }

    pub fn journal(&self) -> Arc<dyn NodeStoreJournal> {
        Arc::clone(&self.inner.journal)
    }
}

impl Drop for DatabaseRuntime {
    fn drop(&mut self) {
        self.stop();
    }
}

fn worker_loop(inner: Arc<DatabaseInner>) {
    let _exit_guard = WorkerExitGuard::new(&inner);
    inner.running_threads.fetch_add(1, Ordering::Relaxed);
    let mut read = BTreeMap::<Uint256, Vec<AsyncReadRequest>>::new();

    loop {
        {
            let mut read_state = inner
                .read_state
                .lock()
                .expect("nodestore read queue mutex must not be poisoned");

            if inner.is_stopping() {
                break;
            }

            if read_state.queue.is_empty() {
                inner.running_threads.fetch_sub(1, Ordering::Relaxed);
                while read_state.queue.is_empty() && !inner.is_stopping() {
                    read_state = inner
                        .read_condvar
                        .wait(read_state)
                        .expect("nodestore read queue mutex must not be poisoned");
                }
                inner.running_threads.fetch_add(1, Ordering::Relaxed);
            }

            if inner.is_stopping() {
                break;
            }

            for _ in 0..inner.request_bundle {
                let Some((hash, requests)) = read_state.queue.pop_first() else {
                    break;
                };
                read.insert(hash, requests);
            }
        }

        for (hash, requests) in std::mem::take(&mut read) {
            if requests.is_empty() {
                continue;
            }

            let seqn = requests[0].ledger_seq;
            let first = if inner.is_stopping() {
                None
            } else {
                catch_unwind(AssertUnwindSafe(|| {
                    inner.fetch_node_object(&hash, seqn, FetchType::Async, false)
                }))
                .unwrap_or_else(|_| {
                    inner.journal.log(
                        JournalLevel::Error,
                        "NodeStore async read fault; cancelling logical callbacks",
                    );
                    None
                })
            };
            for request in requests {
                let result = if inner.is_stopping() {
                    None
                } else if request.ledger_seq == seqn
                    || inner.delegate.is_same_db(request.ledger_seq, seqn)
                {
                    first.clone()
                } else {
                    catch_unwind(AssertUnwindSafe(|| {
                        inner.fetch_node_object(&hash, request.ledger_seq, FetchType::Async, false)
                    }))
                    .unwrap_or(None)
                };
                if result.is_none() && inner.is_stopping() {
                    inner
                        .read_callbacks_cancelled
                        .fetch_add(1, Ordering::Relaxed);
                }
                deliver_async_work(&inner, request, result);
            }
        }
    }

    inner.running_threads.fetch_sub(1, Ordering::Relaxed);
}

fn deliver_rejected_async_work(inner: &Arc<DatabaseInner>, mut work: Box<dyn AsyncReadWork>) {
    if catch_unwind(AssertUnwindSafe(|| work.complete(None))).is_err() {
        inner.journal.log(
            JournalLevel::Error,
            "NodeStore rejected async read work panicked after terminal delivery",
        );
    }
}

fn deliver_async_work(
    inner: &Arc<DatabaseInner>,
    mut request: AsyncReadRequest,
    result: Option<Arc<NodeObject>>,
) {
    let _guard = AsyncCallbackGuard {
        inner: Arc::clone(inner),
    };
    if catch_unwind(AssertUnwindSafe(|| request.work.complete(result))).is_err() {
        inner.journal.log(
            JournalLevel::Error,
            "NodeStore async read work panicked after terminal delivery",
        );
    }
}

fn panic_message(payload: &(dyn Any + Send)) -> String {
    if let Some(message) = payload.downcast_ref::<&'static str>() {
        (*message).to_owned()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "unknown panic payload".to_owned()
    }
}

#[cfg(test)]
mod tests {
    use super::{DatabaseDelegate, DatabaseRuntime, DatabaseSource, FetchType};
    use crate::{
        DummyScheduler, FetchReport, NodeObject, NodeObjectType, NodeStoreJournal, NullJournal,
    };
    use basics::{base_uint::Uint256, basic_config::Section};
    use protocol::JsonValue;
    use std::collections::BTreeMap;
    use std::sync::Arc;

    struct TestDelegate {
        objects: BTreeMap<Uint256, Arc<NodeObject>>,
    }

    impl DatabaseDelegate for TestDelegate {
        fn is_same_db(&self, _first: u32, _second: u32) -> bool {
            true
        }

        fn fetch_node_object(
            &self,
            hash: &Uint256,
            _ledger_seq: u32,
            fetch_report: &mut FetchReport,
            _duplicate: bool,
            _journal: &dyn NodeStoreJournal,
        ) -> Option<Arc<NodeObject>> {
            let object = self.objects.get(hash).cloned();
            if object.is_some() {
                fetch_report.was_found = true;
            }
            object
        }
    }

    #[test]
    fn get_counts_json_includes_node_object_cache_metrics() {
        let hash = Uint256::from_array([0xA5; 32]);
        let object = Arc::new(NodeObject::new(NodeObjectType::Ledger, vec![1, 2, 3], hash));
        let delegate = Arc::new(TestDelegate {
            objects: BTreeMap::from([(hash, Arc::clone(&object))]),
        });
        let scheduler = Arc::new(DummyScheduler);
        let journal: Arc<dyn NodeStoreJournal> = Arc::new(NullJournal);
        let config = Section::new("node_db");
        let database =
            DatabaseRuntime::new(delegate, scheduler, 1, &config, journal).expect("database");

        database.store_stats(1, object.data().len() as u64);
        let fetched = database.fetch_node_object(&hash, 1, FetchType::Synchronous, false);
        assert_eq!(fetched.expect("stored object").data(), object.data());

        let JsonValue::Object(counts) = database.get_counts_json() else {
            panic!("counts json should be an object");
        };

        let keys: Vec<_> = counts.keys().cloned().collect();
        assert_eq!(
            keys,
            vec![
                "node_object_cache_capacity_bytes",
                "node_object_cache_capacity_bytes_is_estimate",
                "node_object_cache_capacity_entries",
                "node_object_cache_durable_loads",
                "node_object_cache_entries",
                "node_object_cache_eviction_policy",
                "node_object_cache_hits",
                "node_object_cache_idle_seconds",
                "node_object_cache_invalidations",
                "node_object_cache_misses",
                "node_object_cache_oversized",
                "node_object_cache_promotions",
                "node_object_cache_rejected",
                "node_object_cache_ttl_seconds",
                "node_object_cache_weighted_capacity_bytes",
                "node_object_cache_weighted_size_bytes",
                "node_read_bytes",
                "node_reads_duration_us",
                "node_reads_hit",
                "node_reads_total",
                "node_writes",
                "node_written_bytes",
                "read_queue",
                "read_request_bundle",
                "read_threads_running",
                "read_threads_total",
            ]
        );
        assert_eq!(counts.get("read_queue"), Some(&JsonValue::Unsigned(0)));
        assert_eq!(
            counts.get("node_object_cache_eviction_policy"),
            Some(&JsonValue::String("lru".to_owned()))
        );
        assert_eq!(
            counts.get("node_object_cache_capacity_entries"),
            Some(&JsonValue::String("1000000".to_owned()))
        );
        assert_eq!(
            counts.get("node_object_cache_capacity_bytes_is_estimate"),
            Some(&JsonValue::Bool(true))
        );
        assert!(matches!(
            counts.get("node_object_cache_weighted_size_bytes"),
            Some(JsonValue::String(value)) if value.parse::<u64>().is_ok()
        ));
        assert!(matches!(
            counts.get("read_threads_total"),
            Some(JsonValue::Signed(value)) if *value >= 1
        ));
        assert!(matches!(
            counts.get("read_threads_running"),
            Some(JsonValue::Signed(value)) if *value >= 0
        ));
        assert_eq!(
            counts.get("read_request_bundle"),
            Some(&JsonValue::Signed(4))
        );
        assert_eq!(
            counts.get("node_writes"),
            Some(&JsonValue::String("1".to_owned()))
        );
        assert_eq!(
            counts.get("node_reads_total"),
            Some(&JsonValue::String("1".to_owned()))
        );
        assert_eq!(
            counts.get("node_reads_hit"),
            Some(&JsonValue::String("1".to_owned()))
        );
        assert_eq!(
            counts.get("node_written_bytes"),
            Some(&JsonValue::String("3".to_owned()))
        );
        assert_eq!(
            counts.get("node_read_bytes"),
            Some(&JsonValue::String("3".to_owned()))
        );
        assert!(matches!(
            counts.get("node_reads_duration_us"),
            Some(JsonValue::String(value)) if value.parse::<u64>().is_ok()
        ));

        database.stop();
    }

    struct CountingDelegate {
        object: Option<Arc<NodeObject>>,
        calls: std::sync::atomic::AtomicUsize,
        delay: std::time::Duration,
    }

    impl DatabaseDelegate for CountingDelegate {
        fn is_same_db(&self, _first: u32, _second: u32) -> bool {
            true
        }

        fn fetch_node_object(
            &self,
            _hash: &Uint256,
            _ledger_seq: u32,
            _fetch_report: &mut FetchReport,
            _duplicate: bool,
            _journal: &dyn NodeStoreJournal,
        ) -> Option<Arc<NodeObject>> {
            self.calls
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if !self.delay.is_zero() {
                std::thread::sleep(self.delay);
            }
            self.object.clone()
        }
    }

    #[test]
    fn node_object_cache_serves_repeated_reads_without_a_second_delegate_fetch() {
        let hash = Uint256::from_array([0xC1; 32]);
        let delegate = Arc::new(CountingDelegate {
            object: Some(Arc::new(NodeObject::new(
                NodeObjectType::AccountNode,
                vec![1, 2, 3],
                hash,
            ))),
            calls: std::sync::atomic::AtomicUsize::new(0),
            delay: std::time::Duration::ZERO,
        });
        let database = DatabaseRuntime::new(
            Arc::clone(&delegate) as Arc<dyn DatabaseDelegate>,
            Arc::new(DummyScheduler),
            1,
            &Section::new("node_db"),
            Arc::new(NullJournal),
        )
        .expect("database");

        assert!(
            database
                .fetch_node_object(&hash, 1, FetchType::Synchronous, false)
                .is_some()
        );
        assert!(
            database
                .fetch_node_object(&hash, 1, FetchType::Synchronous, false)
                .is_some()
        );
        assert_eq!(delegate.calls.load(std::sync::atomic::Ordering::Relaxed), 1);

        database.stop();
    }

    #[test]
    fn node_object_cache_coalesces_concurrent_same_hash_misses() {
        let hash = Uint256::from_array([0xC2; 32]);
        let delegate = Arc::new(CountingDelegate {
            object: Some(Arc::new(NodeObject::new(
                NodeObjectType::AccountNode,
                vec![4, 5, 6],
                hash,
            ))),
            calls: std::sync::atomic::AtomicUsize::new(0),
            delay: std::time::Duration::from_millis(25),
        });
        let database = Arc::new(
            DatabaseRuntime::new(
                Arc::clone(&delegate) as Arc<dyn DatabaseDelegate>,
                Arc::new(DummyScheduler),
                1,
                &Section::new("node_db"),
                Arc::new(NullJournal),
            )
            .expect("database"),
        );
        let start = Arc::new(std::sync::Barrier::new(9));
        let mut workers = Vec::new();
        for _ in 0..8 {
            let database = Arc::clone(&database);
            let start = Arc::clone(&start);
            workers.push(std::thread::spawn(move || {
                start.wait();
                assert!(
                    database
                        .fetch_node_object(&hash, 1, FetchType::Synchronous, false)
                        .is_some()
                );
            }));
        }
        start.wait();
        for worker in workers {
            worker.join().expect("cache worker must not panic");
        }
        assert_eq!(delegate.calls.load(std::sync::atomic::Ordering::Relaxed), 1);

        database.stop();
    }

    #[test]
    fn node_object_cache_does_not_negative_cache_untyped_misses() {
        let hash = Uint256::from_array([0xC3; 32]);
        let delegate = Arc::new(CountingDelegate {
            object: None,
            calls: std::sync::atomic::AtomicUsize::new(0),
            delay: std::time::Duration::ZERO,
        });
        let database = DatabaseRuntime::new(
            Arc::clone(&delegate) as Arc<dyn DatabaseDelegate>,
            Arc::new(DummyScheduler),
            1,
            &Section::new("node_db"),
            Arc::new(NullJournal),
        )
        .expect("database");

        assert!(
            database
                .fetch_node_object(&hash, 1, FetchType::Synchronous, false)
                .is_none()
        );
        assert!(
            database
                .fetch_node_object(&hash, 1, FetchType::Synchronous, false)
                .is_none()
        );
        assert_eq!(delegate.calls.load(std::sync::atomic::Ordering::Relaxed), 2);

        database.stop();
    }

    struct PanicOnceDelegate {
        object: Arc<NodeObject>,
        panics: std::sync::atomic::AtomicBool,
        calls: std::sync::atomic::AtomicUsize,
    }

    impl DatabaseDelegate for PanicOnceDelegate {
        fn is_same_db(&self, _first: u32, _second: u32) -> bool {
            true
        }

        fn fetch_node_object(
            &self,
            _hash: &Uint256,
            _ledger_seq: u32,
            _fetch_report: &mut FetchReport,
            _duplicate: bool,
            _journal: &dyn NodeStoreJournal,
        ) -> Option<Arc<NodeObject>> {
            self.calls
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if self.panics.swap(false, std::sync::atomic::Ordering::AcqRel) {
                panic!("test durable fetch panic");
            }
            Some(Arc::clone(&self.object))
        }
    }

    #[test]
    fn node_object_cache_releases_single_flight_after_loader_panic() {
        let hash = Uint256::from_array([0xC4; 32]);
        let delegate = Arc::new(PanicOnceDelegate {
            object: Arc::new(NodeObject::new(NodeObjectType::AccountNode, vec![7], hash)),
            panics: std::sync::atomic::AtomicBool::new(true),
            calls: std::sync::atomic::AtomicUsize::new(0),
        });
        let database = DatabaseRuntime::new(
            Arc::clone(&delegate) as Arc<dyn DatabaseDelegate>,
            Arc::new(DummyScheduler),
            1,
            &Section::new("node_db"),
            Arc::new(NullJournal),
        )
        .expect("database");

        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                database.fetch_node_object(&hash, 1, FetchType::Synchronous, false)
            }))
            .is_err()
        );
        assert!(
            database
                .fetch_node_object(&hash, 1, FetchType::Synchronous, false)
                .is_some()
        );
        assert_eq!(delegate.calls.load(std::sync::atomic::Ordering::Relaxed), 2);

        database.stop();
    }

    struct VecSource(Vec<Arc<NodeObject>>);

    impl DatabaseSource for VecSource {
        fn for_each(&self, callback: &mut dyn FnMut(Arc<NodeObject>)) {
            for object in &self.0 {
                callback(Arc::clone(object));
            }
        }
    }

    #[test]
    fn import_internal_batches_every_source_object() {
        use crate::Backend;
        use crate::Status;
        use std::sync::Mutex;

        struct RecordingBackend {
            imported: Mutex<Vec<Arc<NodeObject>>>,
        }

        impl Backend for RecordingBackend {
            fn get_name(&self) -> String {
                "recording".to_owned()
            }

            fn open(&self, _create_if_missing: bool) -> Result<(), String> {
                Ok(())
            }

            fn is_open(&self) -> bool {
                true
            }

            fn close(&self) -> Result<(), String> {
                Ok(())
            }

            fn fetch(&self, _hash: &Uint256) -> (Option<Arc<NodeObject>>, Status) {
                (None, Status::NotFound)
            }

            fn fetch_batch(&self, _hashes: &[Uint256]) -> (Vec<Option<Arc<NodeObject>>>, Status) {
                (Vec::new(), Status::Ok)
            }

            fn store(&self, object: Arc<NodeObject>) -> Result<(), String> {
                self.imported
                    .lock()
                    .expect("recording backend mutex must not be poisoned")
                    .push(object);
                Ok(())
            }

            fn store_batch(&self, batch: &crate::Batch) {
                self.imported
                    .lock()
                    .expect("recording backend mutex must not be poisoned")
                    .extend(batch.iter().cloned());
            }

            fn sync(&self) {}

            fn for_each(&self, _callback: &mut dyn FnMut(Arc<NodeObject>)) {}

            fn get_write_load(&self) -> i32 {
                0
            }

            fn set_delete_path(&self) {}

            fn fd_required(&self) -> i32 {
                0
            }
        }

        let scheduler = Arc::new(DummyScheduler);
        let journal: Arc<dyn NodeStoreJournal> = Arc::new(NullJournal);
        let database = DatabaseRuntime::new(
            Arc::new(TestDelegate {
                objects: BTreeMap::new(),
            }),
            scheduler,
            1,
            &Section::new("node_db"),
            journal,
        )
        .expect("database");
        let backend = RecordingBackend {
            imported: Mutex::new(Vec::new()),
        };
        let source = VecSource(vec![
            Arc::new(NodeObject::new(
                NodeObjectType::Ledger,
                vec![1],
                Uint256::from_array([0x01; 32]),
            )),
            Arc::new(NodeObject::new(
                NodeObjectType::TransactionNode,
                vec![2, 3],
                Uint256::from_array([0x02; 32]),
            )),
        ]);

        database.import_internal(&backend, &source);

        let imported = backend
            .imported
            .lock()
            .expect("recording backend mutex must not be poisoned");
        assert_eq!(imported.len(), 2);
        assert_eq!(database.get_store_count(), 2);
        assert_eq!(database.get_store_size(), 3);

        drop(imported);
        database.stop();
    }
}
