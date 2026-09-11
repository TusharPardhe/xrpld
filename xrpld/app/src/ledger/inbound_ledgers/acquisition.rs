//! Per-hash inbound-ledger lifecycle.
//!
//! The structure follows rippled's `InboundLedger` and `TimeoutCounter`:
//! `init` checks local storage, adds peers, queues an immediate timeout job,
//! and every timeout job re-arms only its own three-second timer.

use basics::base_uint::Uint256;
use basics::hardened_hash::HardenedHashBuilder;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::MonotonicClock;
#[cfg(test)]
use ledger::uses_aggressive_by_hash_timeout;
use ledger::{
    FetchPackCache, FetchPackContainer, FetchPackStore, InboundLedgerDataType,
    InboundLedgerJournal, InboundLedgerLocal, InboundLedgerObjectType, InboundLedgerPacket,
    InboundLedgerPacketError, InboundLedgerPeerScore, InboundLedgerReason,
    InboundLedgerRequestTrigger, InboundLedgerStore, InboundLedgerTimerResult, Ledger, TreeAdvance,
    TreeKind, TreePlan, TreePlanId, make_get_ledger_with_node_ids,
    make_inbound_needed_by_hash_request, select_inbound_ledger_reply_peers,
};
use nodestore::database::{PersistenceIdentity, PersistenceOutcome, PersistenceWork};
use overlay::{Peer, PeerSet as _};
use shamap::family::{FullBelowCache, FullBelowCacheImpl, NullMissingNodeReporter, SHAMapFamily};
use shamap::sync::{
    DEFAULT_MAX_DEFERRED_MISSING_NODE_READS, MissingNodeReadApply, MissingNodeReadOutcome,
    MissingNodeResidentLookup, ReadNeed, SHAMapAddNode,
};
use shamap::tree_node_cache::TreeNodeCache;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::panic::{AssertUnwindSafe, catch_unwind};
#[cfg(test)]
use std::sync::Condvar;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU32, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::{Duration, Instant};

use crate::shamap::shamap_store_backend::SHAMapStoreNodeStore;

use super::read_broker::{
    NodeReadBroker, ReadAdmission, ReadKey, ReadOutcome, ReadReady, ReadReadySink,
    ReadRejectReason, ReadTicket,
};
use super::registry::{AcquireReason, AcquisitionLifecycleCounters, CompletedInboundLedger};
use super::scheduler::{AcquisitionKey, AcquisitionReadyScheduler, ReadyCause};
use super::worker_pool::WorkerPool;

const PEER_COUNT_START: usize = 5;
const PEER_COUNT_ADD: usize = 3;
const ACQUIRE_TIMEOUT: Duration = Duration::from_secs(3);
const LOCAL_PROBE_PLAN_ID: u64 = 0;

/// A brokered local probe precedes peer traffic for the header and both roots.
/// Descendant/full-tree local discovery is then performed by the same brokered
/// TreePlan continuation, not a detached synchronous scan.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum LocalProbeKind {
    Header,
    StateRoot,
    TransactionRoot,
}

#[derive(Clone)]
struct LocalProbe {
    /// Every accepted broker subscription stays actor-owned until its one
    /// completion is reduced or terminal teardown explicitly cancels it.
    ticket: ReadTicket,
    kind: LocalProbeKind,
    /// Deferred broker admission retains the one local-read subscription, but
    /// the normal peer-recovery path must not treat it as an in-flight probe.
    suppresses_network: bool,
    reason: InboundLedgerRequestTrigger,
    peer: Option<Arc<dyn Peer>>,
}

/// Match rippled `SHAMap::getMissingNodes()`' retained deferred-read pass.
/// The broker owns the single global physical-read boundary; this is not an
/// actor-local per-turn or per-acquisition cap.
const ACQ_DEFERRED_READS_PER_PASS: usize = DEFAULT_MAX_DEFERRED_MISSING_NODE_READS;
/// Fixed Rust actor-admission adaptation, not a rippled numeric-parity value
/// and not a configurable or wire-protocol limit. The acquisition mailbox
/// owns at most this many queued packets plus unconsumed transport leases.
/// `Deferred` transfers no packet ownership and is never a cancelled reply;
/// Worker 1 retains or terminally discards its transport frame. Accepted
/// leases transfer once to `enqueue_packet_with_admission`; `Drop` releases
/// only an unconsumed reservation. `clear_terminal_work` clears every queued
/// packet and reservation during terminal cancellation, sweep, failure, or
/// stop, so later lease drops are stale no-ops.
pub const ACQ_MAILBOX_PACKET_CAPACITY: usize = 128;
/// Fixed Rust actor-admission adaptation paired with
/// `ACQ_MAILBOX_PACKET_CAPACITY`, not a rippled numeric-parity value and not
/// a configurable or wire-protocol limit. It bounds decoded node-id and
/// node-data bytes owned by queued packets and unconsumed leases.
pub const ACQ_MAILBOX_BYTE_CAPACITY: usize = 4 * 1024 * 1024;

#[cfg(test)]
#[derive(Default)]
struct StateScanAfterAdvancePauseState {
    entered: bool,
    released: bool,
}

/// Per-acquisition test seam placed after a bounded state-scan advance and
/// before the production terminal guard. It is compiled only for the private
/// module tests, so independent tests cannot pause an unrelated acquisition.
#[cfg(test)]
#[derive(Default)]
struct StateScanAfterAdvancePause {
    state: Mutex<StateScanAfterAdvancePauseState>,
    wake: Condvar,
}

#[cfg(test)]
impl StateScanAfterAdvancePause {
    fn wait_until_entered(&self) {
        let state = self.state.lock().expect("state scan pause lock");
        let (state, timeout) = self
            .wake
            .wait_timeout_while(state, Duration::from_secs(5), |state| !state.entered)
            .expect("state scan pause wait");
        assert!(
            state.entered,
            "state scan did not reach its post-advance pause"
        );
        assert!(
            !timeout.timed_out(),
            "state scan post-advance pause timed out"
        );
    }

    fn pause_after_advance(&self) {
        let mut state = self.state.lock().expect("state scan pause lock");
        state.entered = true;
        self.wake.notify_all();
        while !state.released {
            state = self.wake.wait(state).expect("state scan pause wait");
        }
    }

    fn release(&self) {
        let mut state = self.state.lock().expect("state scan pause lock");
        state.released = true;
        self.wake.notify_all();
    }
}

/// Test-only rendezvous inside the sequence gate, after a route has validated
/// its response and before it can enqueue that packet.
#[cfg(test)]
#[derive(Default)]
pub(crate) struct SequenceRoutePause {
    state: Mutex<SequenceRoutePauseState>,
    wake: Condvar,
}

#[cfg(test)]
#[derive(Default)]
struct SequenceRoutePauseState {
    entered: bool,
    released: bool,
}

#[cfg(test)]
impl SequenceRoutePause {
    pub(crate) fn wait_until_entered(&self) {
        let state = self.state.lock().expect("sequence route pause lock");
        let (state, timeout) = self
            .wake
            .wait_timeout_while(state, Duration::from_secs(5), |state| !state.entered)
            .expect("sequence route pause wait");
        assert!(state.entered, "route did not reach sequence gate pause");
        assert!(!timeout.timed_out(), "sequence route pause timed out");
    }

    fn pause_after_validation(&self) {
        let mut state = self.state.lock().expect("sequence route pause lock");
        state.entered = true;
        self.wake.notify_all();
        while !state.released {
            state = self.wake.wait(state).expect("sequence route pause wait");
        }
    }

    pub(crate) fn release(&self) {
        let mut state = self.state.lock().expect("sequence route pause lock");
        state.released = true;
        self.wake.notify_all();
    }
}

/// Test-only proof that a promotion has reached the sequence-gate boundary.
#[cfg(test)]
#[derive(Default)]
pub(crate) struct SequencePromotionAttempt {
    attempted: Mutex<bool>,
    wake: Condvar,
}

#[cfg(test)]
impl SequencePromotionAttempt {
    pub(crate) fn wait_until_attempted(&self) {
        let attempted = self
            .attempted
            .lock()
            .expect("sequence promotion attempt lock");
        let (attempted, timeout) = self
            .wake
            .wait_timeout_while(attempted, Duration::from_secs(5), |attempted| !*attempted)
            .expect("sequence promotion attempt wait");
        assert!(*attempted, "promotion did not reach sequence gate");
        assert!(!timeout.timed_out(), "sequence promotion attempt timed out");
    }

    fn mark_attempted(&self) {
        *self
            .attempted
            .lock()
            .expect("sequence promotion attempt lock") = true;
        self.wake.notify_all();
    }
}

pub(crate) struct WorkerJournal;

impl InboundLedgerJournal for WorkerJournal {
    fn trace(&self, message: &str) {
        tracing::trace!(target: "inbound_ledger", "{message}");
    }

    fn debug(&self, message: &str) {
        tracing::debug!(target: "inbound_ledger", "{message}");
    }

    fn warn(&self, message: &str) {
        tracing::warn!(target: "inbound_ledger", "{message}");
    }

    fn fatal(&self, message: &str) {
        tracing::error!(target: "inbound_ledger", "{message}");
    }
}

#[derive(Clone)]
pub(crate) struct WorkerFetchPack {
    cache: Arc<FetchPackCache>,
}

impl WorkerFetchPack {
    pub(crate) fn new(cache: Arc<FetchPackCache>) -> Self {
        Self { cache }
    }

    /// The shared fetch-pack cache, used by the coordinator engine's resident
    /// lookup to resolve by-hash node data.
    pub(crate) fn cache(&self) -> &Arc<FetchPackCache> {
        &self.cache
    }
}

impl FetchPackContainer for WorkerFetchPack {
    fn get_fetch_pack(&mut self, hash: Uint256) -> Option<Vec<u8>> {
        self.cache.get_fetch_pack(hash)
    }
}

impl FetchPackStore for WorkerFetchPack {
    fn add_fetch_pack(&mut self, hash: Uint256, data: Vec<u8>) {
        self.cache.add_fetch_pack(hash, data);
    }
}

/// Live-overlay source used to mirror rippled `PeerSetImpl::addPeers`, which
/// enumerates the overlay at every peer-add turn rather than keeping the
/// construction-time peer list.
pub(crate) type AcquisitionPeerProvider =
    Arc<dyn Fn() -> Vec<Arc<dyn Peer>> + Send + Sync + 'static>;

/// Registry-owned callback invoked exactly once when this acquisition fails.
/// Mirrors rippled's deferred `InboundLedgers::logFailure` lifecycle while
/// making the five-minute failure cooldown visible before the next sweep.
pub(crate) type AcquisitionFailureRecorder = Arc<dyn Fn(Uint256) + Send + Sync + 'static>;

/// Registry-owned callback that promotes the exact live entry from an
/// initially hash-only request to the verified header sequence.
pub(crate) type AcquisitionSequencePromoter = Arc<dyn Fn(u32) + Send + Sync + 'static>;

/// Immutable ownership token for an early resolver-visible ledger. It lets
/// later failure handling revoke only the acquisition that published it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ProvisionalLedgerIdentity {
    pub acquisition_id: u64,
    pub target_hash: Uint256,
    pub ledger_hash: Uint256,
    pub ledger_seq: u32,
    /// The NodeStore generation captured by the final fence. This prevents a
    /// replacement store from being mistaken for the resolver-visible result.
    pub store_generation: u64,
    /// The per-acquisition FIFO generation of the final durability barrier.
    pub persistence_generation: u64,
}

/// Registry-owned callback invoked exactly once after a successful terminal
/// acquisition has made its completed ledger visible. This mirrors
/// `InboundLedger::done()` calling `touch()` before it dispatches `AcqDone`,
/// preserving the completed entry for its normal sweep lifetime.
pub(crate) type AcquisitionCompletionRecorder =
    Arc<dyn Fn(ProvisionalLedgerIdentity, Arc<Ledger>) -> bool + Send + Sync + 'static>;

/// Registry-owned callback that makes an already resolver-visible entry ready
/// for the single AcqDone-equivalent consumer only after its NodeStore fence.
pub(crate) type AcquisitionDurableCompletionRecorder =
    Arc<dyn Fn(ProvisionalLedgerIdentity) + Send + Sync + 'static>;

/// Application-owned `LedgerMaster::storeLedger` equivalent for completed
/// non-history acquisitions. It must run before the registry-ready handoff,
/// matching rippled `InboundLedger::done()`.
pub(crate) type AcquisitionLedgerStore = Arc<dyn Fn(Arc<Ledger>) + Send + Sync + 'static>;

#[derive(Debug)]
struct AcquisitionStats {
    started_at: Instant,
    first_header_at: Mutex<Option<Instant>>,
    packets: AtomicU64,
    useful_packets: AtomicU64,
    useful_nodes: AtomicU64,
    state_packets: AtomicU64,
    state_useful_nodes: AtomicU64,
    state_duplicate_nodes: AtomicU64,
    malformed_packets: AtomicU64,
    state_scan_runs: AtomicU64,
    state_missing_nodes: AtomicU64,
    tx_missing_nodes: AtomicU64,
    state_scan_us: AtomicU64,
    state_scan_branch_steps: AtomicU64,
    state_scan_missing_nodes_recorded: AtomicU64,
    state_scan_positive_progress_slices: AtomicU64,
    state_scan_branch_budget_yields: AtomicU64,
    state_scan_deferred_read_budget_yields: AtomicU64,
    state_scan_deferred_read_resume_yields: AtomicU64,
    state_scan_missing_node_limit_yields: AtomicU64,
    state_scan_completed_slices: AtomicU64,
    state_scan_last_outcome: AtomicU8,
    state_scan_last_branch_steps: AtomicU64,
    state_scan_last_deferred_reads: AtomicU64,
    state_scan_last_deferred_resumes: AtomicU64,
    state_scan_last_missing_nodes: AtomicU64,
    state_scan_branches_seen: AtomicU64,
    state_scan_duplicate_missing_hashes: AtomicU64,
    state_scan_full_below_hits: AtomicU64,
    state_scan_loaded_or_cached_children: AtomicU64,
    state_scan_pending_reads: AtomicU64,
    state_scan_read_slot_full: AtomicU64,
    state_scan_read_admission_accepted: AtomicU64,
    state_scan_read_admission_deferred: AtomicU64,
    state_scan_read_admission_attached: AtomicU64,
    state_scan_read_broker_rejected: AtomicU64,
    state_scan_max_pending_reads: AtomicU64,
    state_scan_pending_hits: AtomicU64,
    state_scan_pending_misses: AtomicU64,
    state_scan_deferred_resumes: AtomicU64,
    state_scan_yields: AtomicU64,
    state_scan_continuations: AtomicU64,
    timeout_dispatches: AtomicU64,
    state_scan_max_buffered_packets: AtomicU64,
    data_drain_runs: AtomicU64,
    data_drain_us: AtomicU64,
    data_drain_max_us: AtomicU64,
    data_drain_max_packets: AtomicU64,
    tx_scan_us: AtomicU64,
    worker_jobs: AtomicU64,
    worker_queue_wait_us: AtomicU64,
    node_store_fetch_hits: AtomicU64,
    node_store_fetch_misses: AtomicU64,
    last_diagnostic_at: Mutex<Instant>,
}

impl AcquisitionStats {
    fn new() -> Self {
        Self {
            started_at: Instant::now(),
            first_header_at: Mutex::new(None),
            packets: AtomicU64::new(0),
            useful_packets: AtomicU64::new(0),
            useful_nodes: AtomicU64::new(0),
            state_packets: AtomicU64::new(0),
            state_useful_nodes: AtomicU64::new(0),
            state_duplicate_nodes: AtomicU64::new(0),
            malformed_packets: AtomicU64::new(0),
            state_scan_runs: AtomicU64::new(0),
            state_missing_nodes: AtomicU64::new(0),
            tx_missing_nodes: AtomicU64::new(0),
            state_scan_us: AtomicU64::new(0),
            state_scan_branch_steps: AtomicU64::new(0),
            state_scan_missing_nodes_recorded: AtomicU64::new(0),
            state_scan_positive_progress_slices: AtomicU64::new(0),
            state_scan_branch_budget_yields: AtomicU64::new(0),
            state_scan_deferred_read_budget_yields: AtomicU64::new(0),
            state_scan_deferred_read_resume_yields: AtomicU64::new(0),
            state_scan_missing_node_limit_yields: AtomicU64::new(0),
            state_scan_completed_slices: AtomicU64::new(0),
            state_scan_last_outcome: AtomicU8::new(0),
            state_scan_last_branch_steps: AtomicU64::new(0),
            state_scan_last_deferred_reads: AtomicU64::new(0),
            state_scan_last_deferred_resumes: AtomicU64::new(0),
            state_scan_last_missing_nodes: AtomicU64::new(0),
            state_scan_branches_seen: AtomicU64::new(0),
            state_scan_duplicate_missing_hashes: AtomicU64::new(0),
            state_scan_full_below_hits: AtomicU64::new(0),
            state_scan_loaded_or_cached_children: AtomicU64::new(0),
            state_scan_pending_reads: AtomicU64::new(0),
            state_scan_read_slot_full: AtomicU64::new(0),
            state_scan_read_admission_accepted: AtomicU64::new(0),
            state_scan_read_admission_deferred: AtomicU64::new(0),
            state_scan_read_admission_attached: AtomicU64::new(0),
            state_scan_read_broker_rejected: AtomicU64::new(0),
            state_scan_max_pending_reads: AtomicU64::new(0),
            state_scan_pending_hits: AtomicU64::new(0),
            state_scan_pending_misses: AtomicU64::new(0),
            state_scan_deferred_resumes: AtomicU64::new(0),
            state_scan_yields: AtomicU64::new(0),
            state_scan_continuations: AtomicU64::new(0),
            timeout_dispatches: AtomicU64::new(0),
            state_scan_max_buffered_packets: AtomicU64::new(0),
            data_drain_runs: AtomicU64::new(0),
            data_drain_us: AtomicU64::new(0),
            data_drain_max_us: AtomicU64::new(0),
            data_drain_max_packets: AtomicU64::new(0),
            tx_scan_us: AtomicU64::new(0),
            worker_jobs: AtomicU64::new(0),
            worker_queue_wait_us: AtomicU64::new(0),
            node_store_fetch_hits: AtomicU64::new(0),
            node_store_fetch_misses: AtomicU64::new(0),
            last_diagnostic_at: Mutex::new(Instant::now()),
        }
    }

    fn mark_header_received(&self) {
        let mut first_header_at = self
            .first_header_at
            .lock()
            .expect("acquisition first_header_at lock");
        if first_header_at.is_none() {
            *first_header_at = Some(Instant::now());
        }
    }

    fn record_data_drain(&self, elapsed_us: u64, packets: usize) {
        self.data_drain_runs.fetch_add(1, Ordering::Relaxed);
        self.data_drain_us.fetch_add(elapsed_us, Ordering::Relaxed);
        self.data_drain_max_us
            .fetch_max(elapsed_us, Ordering::Relaxed);
        self.data_drain_max_packets
            .fetch_max(packets as u64, Ordering::Relaxed);
    }

    fn should_emit_sampled_diagnostic(&self) -> bool {
        if !tracing::enabled!(target: "inbound_ledger", tracing::Level::DEBUG) {
            return false;
        }

        let now = Instant::now();
        let mut last = self
            .last_diagnostic_at
            .lock()
            .expect("acquisition diagnostic sampling lock");
        if now.duration_since(*last) >= Duration::from_secs(5) {
            *last = now;
            return true;
        }
        false
    }
}

/// Lightweight per-acquisition state used by `fetch_info`. All counts are
/// bounded counters or last-observed values; producing this snapshot never
/// walks a SHAMap or performs a NodeStore read.
#[derive(Debug, Clone)]
pub(crate) struct AcquisitionSnapshot {
    pub age_ms: u64,
    pub header_after_ms: Option<u64>,
    pub seq: u32,
    pub have_header: bool,
    pub have_state: bool,
    pub have_transactions: bool,
    pub timeouts: u32,
    pub packets: u64,
    pub useful_packets: u64,
    pub useful_nodes: u64,
    pub state_packets: u64,
    pub state_useful_nodes: u64,
    pub state_duplicate_nodes: u64,
    pub malformed_packets: u64,
    pub state_scan_runs: u64,
    pub state_missing_nodes: u64,
    pub tx_missing_nodes: u64,
    pub state_scan_us: u64,
    pub state_scan_branch_steps: u64,
    pub state_scan_missing_nodes_recorded: u64,
    pub state_scan_positive_progress_slices: u64,
    pub state_scan_branch_budget_yields: u64,
    pub state_scan_deferred_read_budget_yields: u64,
    pub state_scan_deferred_read_resume_yields: u64,
    pub state_scan_missing_node_limit_yields: u64,
    pub state_scan_completed_slices: u64,
    pub state_scan_last_yield: &'static str,
    pub state_scan_last_branch_steps: u64,
    pub state_scan_last_deferred_reads: u64,
    pub state_scan_last_deferred_resumes: u64,
    pub state_scan_last_missing_nodes: u64,
    pub state_scan_branches_seen: u64,
    pub state_scan_duplicate_missing_hashes: u64,
    pub state_scan_full_below_hits: u64,
    pub state_scan_loaded_or_cached_children: u64,
    pub state_scan_pending_reads: u64,
    pub state_scan_read_slot_full: u64,
    pub state_scan_read_admission_accepted: u64,
    pub state_scan_read_admission_deferred: u64,
    pub state_scan_read_admission_attached: u64,
    pub state_scan_read_broker_rejected: u64,
    pub state_scan_max_pending_reads: u64,
    pub state_scan_pending_hits: u64,
    pub state_scan_pending_misses: u64,
    pub state_scan_deferred_resumes: u64,
    pub state_scan_yields: u64,
    pub state_scan_continuations: u64,
    pub timeout_dispatches: u64,
    pub state_scan_max_buffered_packets: u64,
    pub data_drain_runs: u64,
    pub data_drain_us: u64,
    pub data_drain_max_us: u64,
    pub data_drain_max_packets: u64,
    pub tx_scan_us: u64,
    pub worker_jobs: u64,
    pub worker_queue_wait_us: u64,
    pub node_store_fetch_hits: u64,
    pub node_store_fetch_misses: u64,
    pub tracked_peers: usize,
    pub buffered_packets: usize,
    pub buffered_packets_high_water: usize,
    pub mailbox_token: &'static str,
    pub scan_continuation_pending: bool,
    pub pending_admitted_timeouts: u32,
}

/// One idempotent accepted-node persistence command. Commands are collected
/// while packet validation owns the actor, but are dispatched only after that
/// ownership is released. The key gives duplicate packet data one durable
/// command and one terminal acknowledgement.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct PersistenceKey {
    hash: Uint256,
    ledger_seq: u32,
    object_type: u8,
}

#[derive(Clone)]
struct PersistenceWrite {
    key: PersistenceKey,
    object_type: nodestore::NodeObjectType,
    data: Vec<u8>,
}

#[derive(Clone, Copy)]
struct PersistenceTiming {
    enqueued_at: Instant,
    dispatched_at: Instant,
}

#[derive(Clone)]
enum PersistenceCommand {
    /// One bounded packet/scan batch owned by the NodeStore write scheduler.
    /// A single immutable storage identity settles every accepted key in this
    /// batch, even if a callback arrives after cancellation or rotation.
    WriteBatch {
        identity: PersistenceIdentity,
        timing: PersistenceTiming,
        writes: Vec<PersistenceWrite>,
    },
    DurabilityBarrier {
        identity: PersistenceIdentity,
        timing: PersistenceTiming,
    },
}

impl PersistenceCommand {
    fn identity(&self) -> PersistenceIdentity {
        match self {
            Self::WriteBatch { identity, .. } | Self::DurabilityBarrier { identity, .. } => {
                *identity
            }
        }
    }

    fn timing(&self) -> PersistenceTiming {
        match self {
            Self::WriteBatch { timing, .. } | Self::DurabilityBarrier { timing, .. } => *timing,
        }
    }

    fn is_durability_barrier(&self) -> bool {
        matches!(self, Self::DurabilityBarrier { .. })
    }
}

#[derive(Clone)]
struct PersistenceReady {
    identity: PersistenceIdentity,
    outcome: PersistenceOutcome,
    durability_barrier: bool,
}

/// A scheduled NodeStore callback owns exactly one persistence ticket. If an
/// executor rejects, drops, or unwinds that callback, `Drop` delivers the
/// terminal failure that lets the acquisition release its final barrier.
struct PersistenceCompletionGuard {
    state: Arc<AcquisitionState>,
    ready: Option<PersistenceReady>,
}

impl PersistenceCompletionGuard {
    fn new(
        state: Arc<AcquisitionState>,
        identity: PersistenceIdentity,
        durability_barrier: bool,
    ) -> Self {
        Self {
            state,
            ready: Some(PersistenceReady {
                identity,
                outcome: PersistenceOutcome::Fault(Arc::from(
                    "NodeStore persistence callback dropped",
                )),
                durability_barrier,
            }),
        }
    }

    fn settle(&mut self, outcome: PersistenceOutcome) {
        let Some(mut ready) = self.ready.take() else {
            return;
        };
        ready.outcome = outcome;
        self.state.enqueue_persistence_ready(ready);
    }
}

impl Drop for PersistenceCompletionGuard {
    fn drop(&mut self) {
        if let Some(ready) = self.ready.take() {
            self.state.enqueue_persistence_ready(ready);
        }
    }
}

/// Typed NodeStore work owned after an acquisition actor releases its mutable
/// packet state. Its reservation is the actual `Vec<PersistenceWrite>` record
/// capacity plus every retained `data` buffer capacity; `Arc` identities and
/// fixed enum/key fields live in this fixed-size record and are accounted by
/// the scheduler task itself. No erased closure shell participates in this
/// accounting.
struct AcquisitionPersistenceWork {
    node_store: SHAMapStoreNodeStore,
    command: PersistenceCommand,
    completion: PersistenceCompletionGuard,
}

impl AcquisitionPersistenceWork {
    fn payload_bytes(command: &PersistenceCommand) -> usize {
        match command {
            PersistenceCommand::WriteBatch { writes, .. } => writes
                .capacity()
                .saturating_mul(std::mem::size_of::<PersistenceWrite>())
                .saturating_add(
                    writes
                        .iter()
                        .map(|write| write.data.capacity())
                        .sum::<usize>(),
                ),
            PersistenceCommand::DurabilityBarrier { .. } => 0,
        }
    }
}

impl PersistenceWork for AcquisitionPersistenceWork {
    fn retained_payload_bytes(&self) -> usize {
        Self::payload_bytes(&self.command)
    }

    fn run(self: Box<Self>) {
        let Self {
            node_store,
            command,
            mut completion,
        } = *self;
        let identity = command.identity();
        let timing = command.timing();
        let (target_hash, ledger_hash, ledger_seq) = completion
            .state
            .completed_ledger
            .lock()
            .expect("acquisition completed ledger lock")
            .as_ref()
            .map(|ledger| {
                (
                    *completion.state.hash.as_uint256(),
                    *ledger.header().hash.as_uint256(),
                    ledger.header().seq,
                )
            })
            .unwrap_or((
                *completion.state.hash.as_uint256(),
                *completion.state.hash.as_uint256(),
                completion.state.seq(),
            ));
        if command.is_durability_barrier() {
            tracing::debug!(
                target: "inbound_ledger",
                event = "durability_scheduler_start",
                target_hash = %target_hash,
                ledger_hash = %ledger_hash,
                ledger_seq,
                acquisition_id = identity.acquisition_id,
                store_generation = identity.store_generation,
                persistence_generation = identity.persistence_generation,
                scheduler_dispatch_to_start_us = timing.dispatched_at.elapsed().as_micros() as u64,
                queue_elapsed_us = timing.enqueued_at.elapsed().as_micros() as u64,
                "inbound durability barrier started by NodeStore scheduler"
            );
        }
        let is_durability_barrier = command.is_durability_barrier();
        let write_bytes = Self::payload_bytes(&command) as u64;
        let outcome = if node_store.store_generation() != identity.store_generation {
            PersistenceOutcome::Cancelled
        } else {
            let started = Instant::now();
            let result = match command {
                PersistenceCommand::WriteBatch { writes, .. } => {
                    writes.into_iter().try_for_each(|write| match &node_store {
                        SHAMapStoreNodeStore::Single(database) => database.store(
                            write.object_type,
                            write.data,
                            write.key.hash,
                            write.key.ledger_seq,
                        ),
                        SHAMapStoreNodeStore::Rotating(database) => database.store(
                            write.object_type,
                            write.data,
                            write.key.hash,
                            write.key.ledger_seq,
                        ),
                    })
                }
                PersistenceCommand::DurabilityBarrier { .. } => match &node_store {
                    SHAMapStoreNodeStore::Single(database) => database.sync_result(),
                    SHAMapStoreNodeStore::Rotating(database) => database.sync_result(),
                },
            };
            let elapsed_seconds = started.elapsed().as_secs_f64();
            if is_durability_barrier {
                quaxar_metrics::acquisition::record_nodestore_fence_duration(elapsed_seconds);
            } else {
                quaxar_metrics::acquisition::record_nodestore_write_duration(elapsed_seconds);
                quaxar_metrics::acquisition::record_nodestore_write_bytes(write_bytes);
            }
            match result {
                Ok(()) if node_store.store_generation() == identity.store_generation => {
                    PersistenceOutcome::Durable
                }
                Ok(()) => PersistenceOutcome::Cancelled,
                Err(error) => PersistenceOutcome::Fault(Arc::from(error)),
            }
        };
        completion.settle(outcome);
    }
}

/// Actor-external, per-acquisition FIFO persistence owner. Exactly one command
/// is in flight, so a successful durability barrier is ordered after every
/// accepted write. The actor observes the acknowledgement before the next
/// command is dispatched.
struct PersistenceQueue {
    next_generation: u64,
    queued: VecDeque<PersistenceCommand>,
    in_flight: Option<PersistenceCommand>,
    accepted: BTreeSet<PersistenceKey>,
    barrier_enqueued: bool,
    barrier_identity: Option<PersistenceIdentity>,
    barrier_acknowledged: bool,
    failed: Option<Arc<str>>,
}

impl Default for PersistenceQueue {
    fn default() -> Self {
        Self {
            next_generation: 1,
            queued: VecDeque::new(),
            in_flight: None,
            accepted: BTreeSet::new(),
            barrier_enqueued: false,
            barrier_identity: None,
            barrier_acknowledged: false,
            failed: None,
        }
    }
}

impl PersistenceQueue {
    fn next_identity(&mut self, acquisition_id: u64, store_generation: u64) -> PersistenceIdentity {
        let persistence_generation = self.next_generation;
        self.next_generation = self
            .next_generation
            .checked_add(1)
            .expect("persistence generation overflow");
        PersistenceIdentity {
            acquisition_id,
            persistence_generation,
            store_generation,
        }
    }

    fn enqueue_writes(
        &mut self,
        acquisition_id: u64,
        store_generation: u64,
        writes: Vec<PersistenceWrite>,
    ) {
        let mut accepted = Vec::with_capacity(writes.len());
        for write in writes {
            if self.accepted.insert(write.key) {
                accepted.push(write);
            }
        }
        if accepted.is_empty() {
            return;
        }
        let identity = self.next_identity(acquisition_id, store_generation);
        let now = Instant::now();
        self.queued.push_back(PersistenceCommand::WriteBatch {
            identity,
            timing: PersistenceTiming {
                enqueued_at: now,
                dispatched_at: now,
            },
            writes: accepted,
        });
    }

    fn enqueue_barrier(
        &mut self,
        acquisition_id: u64,
        store_generation: u64,
    ) -> PersistenceIdentity {
        if self.barrier_enqueued {
            return self
                .barrier_identity
                .expect("enqueued durability barrier must retain its identity");
        }
        self.barrier_enqueued = true;
        let identity = self.next_identity(acquisition_id, store_generation);
        self.barrier_identity = Some(identity);
        let now = Instant::now();
        self.queued
            .push_back(PersistenceCommand::DurabilityBarrier {
                identity,
                timing: PersistenceTiming {
                    enqueued_at: now,
                    dispatched_at: now,
                },
            });
        identity
    }

    /// Transition at most one queued command into the one in-flight slot.
    /// An already dispatched command is never returned a second time.
    fn take_next(&mut self) -> Option<PersistenceCommand> {
        if self.in_flight.is_some() {
            return None;
        }
        let mut command = self.queued.pop_front()?;
        match &mut command {
            PersistenceCommand::WriteBatch { timing, .. }
            | PersistenceCommand::DurabilityBarrier { timing, .. } => {
                timing.dispatched_at = Instant::now();
            }
        }
        self.in_flight = Some(command.clone());
        Some(command)
    }

    fn acknowledge(&mut self, ready: &PersistenceReady) -> Option<PersistenceTiming> {
        let command = self.in_flight.take()?;
        if command.identity() != ready.identity
            || command.is_durability_barrier() != ready.durability_barrier
        {
            self.in_flight = Some(command);
            return None;
        }
        let timing = command.timing();
        match &ready.outcome {
            PersistenceOutcome::Durable => {
                if ready.durability_barrier {
                    self.barrier_acknowledged = true;
                }
            }
            PersistenceOutcome::Fault(error) => self.failed = Some(Arc::clone(error)),
            PersistenceOutcome::Cancelled => {
                self.failed = Some(Arc::from("NodeStore persistence cancelled"));
            }
        }
        Some(timing)
    }

    fn provisional_identity(
        &self,
        target_hash: Uint256,
        ledger_hash: Uint256,
        ledger_seq: u32,
    ) -> Option<ProvisionalLedgerIdentity> {
        self.barrier_identity
            .map(|identity| ProvisionalLedgerIdentity {
                acquisition_id: identity.acquisition_id,
                target_hash,
                ledger_hash,
                ledger_seq,
                store_generation: identity.store_generation,
                persistence_generation: identity.persistence_generation,
            })
    }

    /// Drop all still-owned commands during a terminal transition. A late
    /// worker completion is stale because its in-flight slot no longer exists.
    fn cancel(&mut self) {
        self.in_flight.take();
        self.queued.clear();
    }
}

/// The acquisition family is intentionally read-through disabled. Every
/// NodeStore acquisition read belongs to `NodeReadBroker`; packet and planner
/// code may use only resident cache/fetch-pack data. `WorkerStore` is a pure
/// command collector: it never calls `Database::store` or `sync_result`.
#[derive(Default)]
pub struct WorkerStore {
    pending_writes: Vec<PersistenceWrite>,
    pending_keys: BTreeSet<PersistenceKey>,
}

impl WorkerStore {
    /// True while this session owns NodeStore writes that have not yet crossed
    /// the coordinator write port. FullBelow publication uses this to
    /// distinguish already-durable NodeStore reads from newly received nodes
    /// that still require the asynchronous durability barrier.
    pub(crate) fn has_pending_write_nodes(&self) -> bool {
        !self.pending_writes.is_empty()
    }

    fn take_pending_writes(&mut self) -> Vec<PersistenceWrite> {
        self.pending_keys.clear();
        std::mem::take(&mut self.pending_writes)
    }

    /// Drains accepted node writes as coordinator [`acquisition::PersistNode`]
    /// records for the M4.2 durable handoff. The worker store keeps its exact
    /// command semantics; only the transport type changes at the boundary. The
    /// NodeStore object classification is preserved so the write adapter stores
    /// the same object types the legacy path stored.
    pub(crate) fn take_pending_write_nodes(&mut self) -> Vec<acquisition::PersistNode> {
        self.pending_keys.clear();
        self.pending_writes
            .drain(..)
            .map(|write| {
                let object_kind = match write.object_type {
                    nodestore::NodeObjectType::Ledger => acquisition::StoredObjectKind::Ledger,
                    nodestore::NodeObjectType::AccountNode => {
                        acquisition::StoredObjectKind::AccountNode
                    }
                    nodestore::NodeObjectType::TransactionNode => {
                        acquisition::StoredObjectKind::TransactionNode
                    }
                    _ => acquisition::StoredObjectKind::Unknown,
                };
                acquisition::PersistNode::new(
                    SHAMapHash::new(write.key.hash),
                    bytes::Bytes::from(write.data),
                    object_kind,
                )
            })
            .collect()
    }

    /// Canonical resident/fetch-pack nodes follow the same durable write path
    /// as nodes accepted by the packet filter. This mirrors rippled's
    /// `checkFilter` calling `gotNode(true, ...)` for backed filter hits.
    pub(crate) fn store_resident_shamap_node(
        &mut self,
        kind: TreeKind,
        node: &shamap::tree_node::SHAMapTreeNode,
        seq: u32,
    ) -> bool {
        let Ok(data) = node.serialize_with_prefix() else {
            return false;
        };
        let object_type = match kind {
            TreeKind::State => nodestore::NodeObjectType::AccountNode,
            TreeKind::Transaction => nodestore::NodeObjectType::TransactionNode,
        };
        self.store_object(object_type, data, *node.get_hash().as_uint256(), seq);
        true
    }

    fn store_object(
        &mut self,
        object_type: nodestore::NodeObjectType,
        data: Vec<u8>,
        hash: Uint256,
        seq: u32,
    ) {
        let object_type_key = match object_type {
            nodestore::NodeObjectType::AccountNode => 1,
            nodestore::NodeObjectType::TransactionNode => 2,
            nodestore::NodeObjectType::Ledger => 3,
            _ => 0,
        };
        let key = PersistenceKey {
            hash,
            ledger_seq: seq,
            object_type: object_type_key,
        };
        if self.pending_keys.insert(key) {
            self.pending_writes.push(PersistenceWrite {
                key,
                object_type,
                data,
            });
        }
    }
}

impl InboundLedgerStore for WorkerStore {
    fn fetch_ledger_header(&mut self, _hash: SHAMapHash, _seq: u32) -> Option<Vec<u8>> {
        // Header lookup is also broker/packet driven. Returning a synchronous
        // NodeStore result here would reintroduce I/O under actor ownership.
        None
    }

    fn store_ledger_header(&mut self, data: Vec<u8>, hash: SHAMapHash, seq: u32) {
        self.store_object(
            nodestore::NodeObjectType::Ledger,
            data,
            *hash.as_uint256(),
            seq,
        );
    }

    fn store_shamap_node(
        &mut self,
        object_type: shamap::storage::NodeObjectType,
        data: Vec<u8>,
        hash: Uint256,
        seq: u32,
    ) {
        let object_type = match object_type {
            shamap::storage::NodeObjectType::AccountNode => nodestore::NodeObjectType::AccountNode,
            shamap::storage::NodeObjectType::TransactionNode => {
                nodestore::NodeObjectType::TransactionNode
            }
            shamap::storage::NodeObjectType::Ledger => nodestore::NodeObjectType::Ledger,
            _ => nodestore::NodeObjectType::Unknown,
        };
        self.store_object(object_type, data, hash, seq);
    }

    fn should_store_hash(&mut self, _hash: Uint256) -> bool {
        true
    }

    fn fetch_node_data(&self, _hash: Uint256) -> Option<basics::blob::Blob> {
        // See `fetch_ledger_header`: local reads are brokered, never direct.
        None
    }
}

pub struct AcqMutableState {
    pub inbound: InboundLedgerLocal,
    pub store: WorkerStore,
    pub(crate) fetch_pack: WorkerFetchPack,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AcquisitionWorkToken {
    Idle,
    Queued,
    Running,
}

impl AcquisitionWorkToken {
    fn name(self) -> &'static str {
        match self {
            Self::Idle => "idle",
            Self::Queued => "queued",
            Self::Running => "running",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PacketEnqueue {
    Accepted,
    Terminal,
    Full,
    InvalidLease,
}

#[derive(Debug)]
pub(crate) enum PacketAdmissionReservation {
    Terminal,
    Deferred,
}

/// Byte accounting shared by lease reservation and the consuming enqueue so a
/// caller cannot reserve one payload size and insert another.
fn packet_bytes(packet: &InboundLedgerPacket) -> usize {
    packet
        .nodes
        .iter()
        .map(|node| node.node_data.len() + node.node_id.as_ref().map_or(0, Vec::len))
        .sum()
}

/// Opaque actor-owned reservation for one decoded matching reply. Transport
/// owns this token only until it hands the packet to the matching acquisition;
/// terminal teardown clears the mailbox reservation and a later drop becomes a
/// harmless stale release. The token never takes an overlay lock.
pub struct InboundPacketAdmissionLease {
    state: Arc<AcquisitionState>,
    acquisition_id: u64,
    reservation_id: u64,
    bytes: usize,
}

impl InboundPacketAdmissionLease {
    fn belongs_to(&self, state: &AcquisitionState) -> bool {
        self.acquisition_id == state.acquisition_id
    }
}

impl Drop for InboundPacketAdmissionLease {
    fn drop(&mut self) {
        self.state.release_packet_admission(self.reservation_id);
    }
}

/// One packet remains exclusively owned by this acquisition until all of its
/// 128-node application steps have settled. It is never silently dropped on a
/// full mailbox; ingress receives an explicit rejection instead.
struct PacketWork {
    peer_id: u64,
    packet: InboundLedgerPacket,
    bytes: usize,
    /// Admission time; sampled as mailbox age when a bounded turn consumes it.
    enqueued_at: Instant,
}

struct ActorTreePlan {
    plan: TreePlan,
    reason: InboundLedgerRequestTrigger,
    peer: Option<Arc<dyn Peer>>,
    tickets: BTreeMap<SHAMapHash, ReadTicket>,
    /// Read needs removed from TreePlan's unannounced set but not yet admitted
    /// to the broker. This FIFO is the actor-owned admission backlog: it
    /// prevents a full completion mailbox from reannouncing the same hashes
    /// and repeatedly re-entering `TreePlan::advance` with zero branch work.
    read_admission_backlog: VecDeque<ReadNeed>,
    /// A plan is runnable only when it has retained CPU frontier. Pending
    /// broker/network work is deliberately waiting, not self-rescheduling.
    runnable: bool,
    /// Timeout retargeting may use `TMGetObjectByHash` only after the planner's
    /// existing aggressive threshold has been crossed.
    aggressive_by_hash: bool,
}

impl ActorTreePlan {
    /// A local deferred batch is an atomic `getMissingNodes()` boundary: peer
    /// candidates are considered only after every admitted read settles.
    fn awaiting_local_read_batch(&self) -> bool {
        !self.read_admission_backlog.is_empty() || !self.tickets.is_empty()
    }

    fn retarget(
        &mut self,
        reason: InboundLedgerRequestTrigger,
        peer: Option<Arc<dyn Peer>>,
        aggressive_by_hash: bool,
    ) {
        let priority = |trigger| match trigger {
            InboundLedgerRequestTrigger::Timeout => 4,
            InboundLedgerRequestTrigger::ReplyHighLatency => 3,
            InboundLedgerRequestTrigger::Reply => 2,
            InboundLedgerRequestTrigger::Added => 1,
            InboundLedgerRequestTrigger::Blind => 0,
        };
        if reason == InboundLedgerRequestTrigger::Timeout {
            self.reason = reason;
            self.peer = None;
            self.plan.clear_recent_requests();
            let admission_backlog_waiting = !self.read_admission_backlog.is_empty();
            let retried = if !admission_backlog_waiting {
                self.plan
                    .network_candidates()
                    .into_iter()
                    .filter(|(_, hash)| self.plan.retry_network_candidate(SHAMapHash::new(*hash)))
                    .count()
            } else {
                0
            };
            // A lost peer reply wakes only the retained verified network
            // frontier. No plan is rebuilt and an empty frontier stays idle.
            // A callback-less broker rejection leaves no ticket to wake this
            // actor. Timeout is its bounded retry source; it drains the FIFO
            // directly without re-running TreePlan for the same hashes. Do
            // not append network retries while that FIFO remains blocked:
            // they cannot be emitted until the local read gate reopens.
            self.runnable |= retried != 0 || admission_backlog_waiting;
            self.aggressive_by_hash = aggressive_by_hash && retried != 0;
        } else if self.reason != InboundLedgerRequestTrigger::Timeout
            && priority(reason) >= priority(self.reason)
        {
            self.reason = reason;
            self.peer = peer;
        }
    }
}

/// A `Ready` result may be requeued only if the retained continuation actually
/// consumed a branch during this actor turn. This is deliberately checked at
/// the actor boundary: a stale/inconsistent continuation must become idle
/// rather than consume every worker with zero-work successor turns.
fn ready_turn_can_requeue(plan: &TreePlan, branch_steps_before: u64) -> bool {
    plan.has_runnable_frontier() && plan.branch_steps() > branch_steps_before
}

const SCAN_OUTCOME_READY: u8 = 1;
const SCAN_OUTCOME_NEEDS_READS: u8 = 2;
const SCAN_OUTCOME_NEEDS_NETWORK: u8 = 3;
const SCAN_OUTCOME_COMPLETE: u8 = 4;
const SCAN_OUTCOME_INVALID: u8 = 5;

fn scan_outcome_name(outcome: u8) -> &'static str {
    match outcome {
        SCAN_OUTCOME_READY => "ready",
        SCAN_OUTCOME_NEEDS_READS => "needs_reads",
        SCAN_OUTCOME_NEEDS_NETWORK => "needs_network",
        SCAN_OUTCOME_COMPLETE => "complete",
        SCAN_OUTCOME_INVALID => "invalid",
        _ => "not_run",
    }
}

/// Fully-owned peer work emitted by an actor turn. The target is cloned while
/// the detached plan is still available, so no plan/actor borrow survives the
/// outbound boundary.
struct OwnedOutboundRequest {
    message: overlay::ProtocolMessage,
    target: Option<Arc<dyn Peer>>,
}

/// The outbound boundary is deliberately expressed as a sequencing helper:
/// return the detached TreePlan to its mailbox first, then run the send hook.
/// A terminal restoration reports false, so its caller cannot account or send
/// a request after cancellation has won. Both ordinary and aggressive
/// `NeedsNetwork` branches use this helper.
fn restore_tree_plan_before_peer_send(
    actor_plan: ActorTreePlan,
    restore_plan: impl FnOnce(ActorTreePlan) -> bool,
    send_hook: impl FnOnce(),
) -> bool {
    if !restore_plan(actor_plan) {
        return false;
    }
    send_hook();
    true
}

fn send_owned_outbound_request(state: &AcquisitionState, outbound: OwnedOutboundRequest) -> bool {
    // Callers hold `outbound_gate` through restored-plan send linearization.
    state.send_request_while_outbound_gate(&outbound.message, outbound.target.as_ref())
}

/// Mark only the candidates that will be serialized into this request. The
/// retained plan owns excess candidates, so put them back on its immediate
/// frontier rather than making timeout recovery rediscover them.
fn select_tree_network_candidates(
    plan: &mut TreePlan,
    candidates: Vec<(shamap::node_id::SHAMapNodeId, Uint256)>,
    limit: usize,
) -> Vec<(shamap::node_id::SHAMapNodeId, Uint256)> {
    let mut selected = Vec::with_capacity(limit.min(candidates.len()));
    let mut overflow = Vec::new();
    for candidate @ (_, hash) in candidates {
        if selected.len() < limit {
            if plan.mark_request_candidate(hash) {
                selected.push(candidate);
            }
        } else {
            overflow.push(candidate);
        }
    }
    plan.restore_network_candidates(overflow);
    selected
}

/// The bounded actor mailbox. Its reducer consumes, in order, one timeout,
/// one packet step, one persistence event, up to a fixed number of settled
/// broker results, and one tree CPU step before yielding. No tree plan owns
/// NodeStore I/O or a peer send.
struct AcquisitionMailbox {
    packets: VecDeque<PacketWork>,
    packet_bytes: usize,
    /// Transport-held leases reserve this capacity before a decoded matching
    /// reply enters the actor. Terminal cleanup drops the map so every later
    /// lease drop is stale and cannot double-release capacity.
    packet_admissions: BTreeMap<u64, usize>,
    next_packet_admission_id: u64,
    /// Broker completions retain ticket ownership until this actor reduces
    /// them. The broker's global physical-read boundary bounds I/O; mailbox
    /// delivery is never rejected after admission.
    events: VecDeque<ReadReady>,
    persistence_events: VecDeque<PersistenceReady>,
    local_probes: BTreeMap<u64, LocalProbe>,
    completed_local_probes: BTreeSet<LocalProbeKind>,
    token: AcquisitionWorkToken,
    pending_timeouts: u32,
    pending_fetch_pack_generation: u64,
    handled_fetch_pack_generation: u64,
    plan: Option<ActorTreePlan>,
    batch_useful_peer_counts: BTreeMap<u64, i32>,
    buffered_packets_high_water: usize,
    buffered_bytes_high_water: usize,
    stale_events: u64,
    overload_rejections: u64,
}

impl Default for AcquisitionMailbox {
    fn default() -> Self {
        Self {
            packets: VecDeque::new(),
            packet_bytes: 0,
            packet_admissions: BTreeMap::new(),
            next_packet_admission_id: 1,
            events: VecDeque::new(),
            persistence_events: VecDeque::new(),
            local_probes: BTreeMap::new(),
            completed_local_probes: BTreeSet::new(),
            token: AcquisitionWorkToken::Idle,
            pending_timeouts: 0,
            pending_fetch_pack_generation: 0,
            handled_fetch_pack_generation: 0,
            plan: None,
            batch_useful_peer_counts: BTreeMap::new(),
            buffered_packets_high_water: 0,
            buffered_bytes_high_water: 0,
            stale_events: 0,
            overload_rejections: 0,
        }
    }
}

impl AcquisitionMailbox {
    fn buffered_packet_count(&self) -> usize {
        self.packets.len()
    }

    fn has_work(&self, fetch_pack_ready: bool) -> bool {
        !self.packets.is_empty()
            || !self.events.is_empty()
            || !self.persistence_events.is_empty()
            || self.pending_timeouts != 0
            || self.plan.as_ref().is_some_and(|plan| plan.runnable)
            || fetch_pack_ready
    }

    /// `Some(false)` means this kind already has a deferred broker ticket.
    /// Keep that one ticket for deduplication, but let later timeout/reply
    /// triggers take the normal network-recovery path.
    fn local_probe_network_suppression(&self, kind: LocalProbeKind) -> Option<bool> {
        if self.completed_local_probes.contains(&kind) {
            return Some(false);
        }
        self.local_probes
            .values()
            .find(|probe| probe.kind == kind)
            .map(|probe| probe.suppresses_network)
    }

    /// Wake a retained plan without recursively advancing it. An idle mailbox
    /// claims exactly one bounded actor turn; a running turn observes the
    /// runnable plan in `finish_acquisition_turn` and queues the next turn.
    fn wake_tree_plan(&mut self) -> bool {
        let Some(plan) = self.plan.as_mut() else {
            return false;
        };
        plan.runnable = true;
        if self.token == AcquisitionWorkToken::Idle {
            self.token = AcquisitionWorkToken::Queued;
            true
        } else {
            false
        }
    }

    fn record_late_read_event(&mut self) {
        self.stale_events += 1;
    }

    /// Finish one running actor turn. The caller submits exactly one successor
    /// when this reports remaining work, preserving ingress coalescing.
    fn finish_turn(&mut self, fetch_pack_ready: bool) -> bool {
        if self.has_work(fetch_pack_ready) {
            self.token = AcquisitionWorkToken::Queued;
            true
        } else {
            self.token = AcquisitionWorkToken::Idle;
            false
        }
    }

    /// Pop one settled completion. The broker owns admission; this actor only
    /// preserves FIFO reduction and ticket/plan identity checks.
    fn take_read_event(&mut self) -> Option<ReadReady> {
        self.events.pop_front()
    }

    fn clear_terminal_work(&mut self) -> Vec<ReadTicket> {
        let mut tickets: Vec<ReadTicket> = self
            .plan
            .take()
            .map(|plan| plan.tickets.into_values().collect())
            .unwrap_or_default();
        // Local probes use the same broker admission as tree reads. Preserve
        // their tickets until terminal teardown so they cannot consume broker
        // capacity forever when their callback is never reduced.
        tickets.extend(self.local_probes.values().map(|probe| probe.ticket));
        self.packets.clear();
        self.packet_bytes = 0;
        self.packet_admissions.clear();
        self.events.clear();
        self.persistence_events.clear();
        self.local_probes.clear();
        self.completed_local_probes.clear();
        self.pending_timeouts = 0;
        self.batch_useful_peer_counts.clear();
        self.token = AcquisitionWorkToken::Idle;
        tickets
    }
}

/// Per-ledger state owned by the registry.
pub struct AcquisitionState {
    mailbox: Mutex<AcquisitionMailbox>,
    /// Linearizes response-sequence validation plus packet admission with a
    /// zero-to-nonzero header sequence promotion. Registry locks are never
    /// held while taking this gate.
    sequence_gate: Mutex<()>,
    #[cfg(test)]
    state_scan_after_advance_pause: Mutex<Option<Arc<StateScanAfterAdvancePause>>>,
    #[cfg(test)]
    sequence_route_pause: Mutex<Option<Arc<SequenceRoutePause>>>,
    #[cfg(test)]
    sequence_promotion_attempt: Mutex<Option<Arc<SequencePromotionAttempt>>>,
    pub mutable: Mutex<AcqMutableState>,
    pub hash: SHAMapHash,
    pub acquisition_id: u64,
    /// Requested sequence, promoted exactly once from zero by a verified
    /// header. `InboundLedgerLocal` remains the canonical mutable value.
    seq: AtomicU32,
    pub reason: AcquireReason,
    pub peer_set: overlay::SimplePeerSet,
    peer_provider: AcquisitionPeerProvider,
    stats: Arc<AcquisitionStats>,
    /// The NodeFamily-owned cache shared by every inbound traversal. This is
    /// the same cache swept by the application and lets a complete backed
    /// subtree discovered by one acquisition suppress work in another.
    pub shared_full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
    pub node_store: SHAMapStoreNodeStore,
    read_broker: NodeReadBroker,
    persistence: Mutex<PersistenceQueue>,
    /// Serializes every outbound peer send and its accounting with terminal
    /// state publication. A request is either sent before terminal wins or is
    /// suppressed after it; there is no check-then-send gap.
    outbound_gate: Mutex<()>,
    /// Observability only: records peer-availability-to-first-request latency
    /// once per session. It never gates request production.
    first_request_metric_recorded: AtomicBool,
    /// Terminal traversal freezes ingress/request generation while ordered
    /// persistence and its one durability barrier drain.
    draining: AtomicBool,
    next_plan_id: AtomicU64,
    pub shared_tree_cache: Arc<TreeNodeCache<MonotonicClock>>,
    pub store_tx: std::sync::mpsc::SyncSender<CompletedInboundLedger>,
    failure_recorder: AcquisitionFailureRecorder,
    sequence_promoter: AcquisitionSequencePromoter,
    completion_recorder: AcquisitionCompletionRecorder,
    durable_completion_recorder: AcquisitionDurableCompletionRecorder,
    pub stopped: AtomicBool,
    pub completed: AtomicBool,
    completed_ledger: Mutex<Option<Arc<Ledger>>>,
    pub failed: AtomicBool,
    // Mirrors rippled InboundLedger::done's signaled_ guard: terminal failure
    // must be claimed before its registry touch/cooldown callback, but not
    // published to poll/sweep consumers until that callback has completed.
    failure_claimed: AtomicBool,
    // Exactly one caller publishes the complete immutable ledger to the
    // resolver path. This is intentionally distinct from durable completion:
    // rippled exposes the completed ledger before its downstream AcqDone work.
    resolver_publication_claimed: AtomicBool,
    // Set before registry completion registration so cancellation can prevent
    // or revoke every stage of provisional resolver publication.
    provisional_registered: AtomicBool,
    // Set only after the cache-only immutable ledger is visible to the
    // registry, LedgerHistory, and validation resolver.
    resolver_published: AtomicBool,
    // Exactly one caller records terminal durability after the FIFO NodeStore
    // barrier acknowledges every accepted write.
    finalization_claimed: AtomicBool,
    pub fetch_pack_ready: AtomicBool,
    timer_armed: AtomicBool,
    worker_pool: Arc<WorkerPool>,
    scheduler: Arc<AcquisitionReadyScheduler>,
    scheduler_key: AcquisitionKey,
    lifecycle: Arc<AcquisitionLifecycleCounters>,
}

/// A fair turn yields only after an atomic unit when another acquisition is
/// ready. It intentionally replaces packet/node-count continuation churn.
pub(crate) struct TurnBudget {
    started: Instant,
    competing_ready: usize,
}

impl TurnBudget {
    const FAIR_TURN_ELAPSED_TARGET: Duration = Duration::from_millis(2);

    pub(crate) fn new(competing_ready: usize) -> Self {
        Self {
            started: Instant::now(),
            competing_ready,
        }
    }

    pub(crate) fn must_yield_after_atomic_unit(&self) -> bool {
        self.competing_ready != 0 && self.started.elapsed() >= Self::FAIR_TURN_ELAPSED_TARGET
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct AcquisitionTurnOutcome {
    pub terminal: bool,
    pub needs_turn: bool,
}

impl AcquisitionState {
    /// Initialize an inbound ledger at the acquire boundary.
    ///
    /// This matches `InboundLedger::init` in rippled: after the registry has
    /// installed the per-hash entry, initialization immediately checks local
    /// storage, selects peers, and sends the first requests. Only later packet
    /// processing and timeout callbacks occupy the JtLedgerData-equivalent
    /// queue. In particular, initialization must not consume the timeout
    /// admission budget used by `TimeoutCounter` recovery jobs.
    pub fn start(self: &Arc<Self>) {
        self.lifecycle
            .initialization_jobs
            .fetch_add(1, Ordering::Relaxed);
        self.stats.worker_jobs.fetch_add(1, Ordering::Relaxed);
        // Initialization remains synchronous and precedes its first mailbox
        // token. If it creates a scan, `trigger` installs that continuation
        // before requesting the token; ingress that arrives afterward only
        // coalesces behind that established work.
        run_acquisition_job(self, "initialization", || process_init(self));
    }

    /// Request a single runnable acquisition turn. The mailbox lock makes the
    /// idle-to-queued transition atomic with respect to ingress, timer jobs,
    /// and scan continuation persistence; all later events coalesce behind the
    /// same token.
    pub fn submit_data_job(self: &Arc<Self>) {
        if self.request_acquisition_turn() {
            self.enqueue_acquisition_turn();
        }
    }

    /// Reserve the actor's bounded packet and byte capacity before a decoded
    /// matching response is handed to routing. Worker 1 owns the peer-scoped
    /// transport pause/defer policy for `Deferred`; this actor retains no
    /// decoded packet on that outcome.
    pub(crate) fn reserve_packet_admission(
        self: &Arc<Self>,
        bytes: usize,
    ) -> Result<InboundPacketAdmissionLease, PacketAdmissionReservation> {
        if self.is_done() || self.draining.load(Ordering::Acquire) {
            return Err(PacketAdmissionReservation::Terminal);
        }
        let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        if self.is_done() || self.draining.load(Ordering::Acquire) {
            return Err(PacketAdmissionReservation::Terminal);
        }
        let reserved_bytes = mailbox.packet_admissions.values().sum::<usize>();
        if mailbox
            .packets
            .len()
            .saturating_add(mailbox.packet_admissions.len())
            >= ACQ_MAILBOX_PACKET_CAPACITY
            || mailbox
                .packet_bytes
                .saturating_add(reserved_bytes)
                .saturating_add(bytes)
                > ACQ_MAILBOX_BYTE_CAPACITY
        {
            mailbox.overload_rejections += 1;
            return Err(PacketAdmissionReservation::Deferred);
        }
        let reservation_id = mailbox.next_packet_admission_id;
        mailbox.next_packet_admission_id = mailbox
            .next_packet_admission_id
            .checked_add(1)
            .expect("packet admission id overflow");
        mailbox.packet_admissions.insert(reservation_id, bytes);
        Ok(InboundPacketAdmissionLease {
            state: Arc::clone(self),
            acquisition_id: self.acquisition_id,
            reservation_id,
            bytes,
        })
    }

    fn release_packet_admission(&self, reservation_id: u64) {
        self.mailbox
            .lock()
            .expect("acquisition mailbox lock")
            .packet_admissions
            .remove(&reservation_id);
    }

    /// Consume a reservation while holding the sequence gate. The reservation
    /// has already accounted for this exact decoded packet, so neither a
    /// concurrent ingress nor an actor packet can overcommit the mailbox.
    pub(crate) fn enqueue_packet_with_admission(
        self: &Arc<Self>,
        lease: InboundPacketAdmissionLease,
        peer_id: u64,
        response_seq: Option<u32>,
        packet: InboundLedgerPacket,
    ) -> Result<PacketEnqueue, u32> {
        let _sequence_gate = self
            .sequence_gate
            .lock()
            .expect("acquisition sequence gate");
        let expected_seq = self.seq();
        if let Some(response_seq) = response_seq
            && !super::registry::response_sequence_matches_request(expected_seq, response_seq)
        {
            return Err(expected_seq);
        }
        if !lease.belongs_to(self) {
            return Ok(PacketEnqueue::InvalidLease);
        }
        Ok(self.enqueue_admitted_packet(lease, peer_id, packet))
    }

    fn enqueue_admitted_packet(
        self: &Arc<Self>,
        lease: InboundPacketAdmissionLease,
        peer_id: u64,
        packet: InboundLedgerPacket,
    ) -> PacketEnqueue {
        let bytes = packet_bytes(&packet);
        let should_enqueue = {
            let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
            let Some(reserved_bytes) = mailbox.packet_admissions.remove(&lease.reservation_id)
            else {
                return PacketEnqueue::InvalidLease;
            };
            if reserved_bytes != lease.bytes || reserved_bytes != bytes {
                return PacketEnqueue::InvalidLease;
            }
            if self.is_done() || self.draining.load(Ordering::Acquire) {
                return PacketEnqueue::Terminal;
            }
            mailbox.packet_bytes += bytes;
            mailbox.packets.push_back(PacketWork {
                peer_id,
                packet,
                bytes,
                enqueued_at: Instant::now(),
            });
            mailbox.buffered_packets_high_water = mailbox
                .buffered_packets_high_water
                .max(mailbox.buffered_packet_count());
            mailbox.buffered_bytes_high_water =
                mailbox.buffered_bytes_high_water.max(mailbox.packet_bytes);
            quaxar_metrics::acquisition::mailbox_packet_count(mailbox.buffered_packet_count());
            quaxar_metrics::acquisition::mailbox_packet_bytes(mailbox.packet_bytes);
            quaxar_metrics::acquisition::mailbox_packet_high_water(
                mailbox.buffered_packets_high_water,
            );
            quaxar_metrics::acquisition::mailbox_byte_high_water(mailbox.buffered_bytes_high_water);
            if mailbox.token == AcquisitionWorkToken::Idle {
                mailbox.token = AcquisitionWorkToken::Queued;
                true
            } else {
                self.lifecycle
                    .data_jobs_coalesced
                    .fetch_add(1, Ordering::Relaxed);
                false
            }
        };
        if should_enqueue {
            self.enqueue_acquisition_turn();
        }
        PacketEnqueue::Accepted
    }

    /// Validate a wire sequence and enqueue the packet under the same gate
    /// used by zero-to-nonzero sequence promotion. A response that validated
    /// while the sequence was unknown therefore enters before promotion, or
    /// observes the promoted sequence and is rejected; it cannot validate
    /// before promotion and enqueue afterward.
    pub(crate) fn enqueue_packet_with_sequence(
        self: &Arc<Self>,
        peer_id: u64,
        response_seq: Option<u32>,
        packet: InboundLedgerPacket,
    ) -> Result<PacketEnqueue, u32> {
        let _sequence_gate = self
            .sequence_gate
            .lock()
            .expect("acquisition sequence gate");
        let expected_seq = self.seq();
        if let Some(response_seq) = response_seq
            && !super::registry::response_sequence_matches_request(expected_seq, response_seq)
        {
            return Err(expected_seq);
        }
        #[cfg(test)]
        if let Some(pause) = self
            .sequence_route_pause
            .lock()
            .expect("sequence route pause lock")
            .clone()
        {
            pause.pause_after_validation();
        }
        Ok(self.enqueue_packet(peer_id, packet))
    }

    /// Enqueue one immutable packet. Saturation is visible to the caller so
    /// routing can charge/record overload instead of silently losing packet
    /// ownership. Callers that receive a wire sequence must use
    /// `enqueue_packet_with_sequence`.
    fn enqueue_packet(
        self: &Arc<Self>,
        peer_id: u64,
        packet: InboundLedgerPacket,
    ) -> PacketEnqueue {
        if self.is_done() || self.draining.load(Ordering::Acquire) {
            return PacketEnqueue::Terminal;
        }
        let bytes = packet_bytes(&packet);
        let should_enqueue = {
            let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
            let reserved_bytes = mailbox.packet_admissions.values().sum::<usize>();
            if mailbox
                .packets
                .len()
                .saturating_add(mailbox.packet_admissions.len())
                >= ACQ_MAILBOX_PACKET_CAPACITY
                || mailbox
                    .packet_bytes
                    .saturating_add(reserved_bytes)
                    .saturating_add(bytes)
                    > ACQ_MAILBOX_BYTE_CAPACITY
            {
                mailbox.overload_rejections += 1;
                return PacketEnqueue::Full;
            }
            mailbox.packet_bytes += bytes;
            mailbox.packets.push_back(PacketWork {
                peer_id,
                packet,
                bytes,
                enqueued_at: Instant::now(),
            });
            mailbox.buffered_packets_high_water = mailbox
                .buffered_packets_high_water
                .max(mailbox.buffered_packet_count());
            mailbox.buffered_bytes_high_water =
                mailbox.buffered_bytes_high_water.max(mailbox.packet_bytes);
            quaxar_metrics::acquisition::mailbox_packet_count(mailbox.buffered_packet_count());
            quaxar_metrics::acquisition::mailbox_packet_bytes(mailbox.packet_bytes);
            quaxar_metrics::acquisition::mailbox_packet_high_water(
                mailbox.buffered_packets_high_water,
            );
            quaxar_metrics::acquisition::mailbox_byte_high_water(mailbox.buffered_bytes_high_water);
            if mailbox.token == AcquisitionWorkToken::Idle {
                mailbox.token = AcquisitionWorkToken::Queued;
                true
            } else {
                self.lifecycle
                    .data_jobs_coalesced
                    .fetch_add(1, Ordering::Relaxed);
                false
            }
        };
        if should_enqueue {
            self.enqueue_acquisition_turn();
        }
        PacketEnqueue::Accepted
    }

    fn enqueue_read_ready(self: &Arc<Self>, ready: ReadReady) {
        if self.is_done() {
            // Broker cancellation and NodeStore completion may race terminal
            // teardown. The event has no remaining owner, but is visible in
            // diagnostics instead of being silently discarded.
            self.mailbox
                .lock()
                .expect("acquisition mailbox lock")
                .record_late_read_event();
            return;
        }
        let should_enqueue = {
            let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
            mailbox.events.push_back(ready);
            if mailbox.token == AcquisitionWorkToken::Idle {
                mailbox.token = AcquisitionWorkToken::Queued;
                true
            } else {
                false
            }
        };
        if should_enqueue {
            self.enqueue_acquisition_turn_with_cause(ReadyCause::READ_READY);
        }
    }

    fn request_acquisition_turn(&self) -> bool {
        if self.is_done() {
            return false;
        }
        let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        if mailbox.token == AcquisitionWorkToken::Idle {
            mailbox.token = AcquisitionWorkToken::Queued;
            true
        } else {
            self.lifecycle
                .data_jobs_coalesced
                .fetch_add(1, Ordering::Relaxed);
            false
        }
    }

    fn enqueue_acquisition_turn(self: &Arc<Self>) {
        self.enqueue_acquisition_turn_with_cause(ReadyCause::WIRE);
    }

    fn enqueue_acquisition_turn_with_cause(self: &Arc<Self>, cause: ReadyCause) {
        self.lifecycle
            .data_jobs_submitted
            .fetch_add(1, Ordering::Relaxed);
        self.scheduler.wake(self.scheduler_key, self, cause);
    }

    /// Scheduler-owned execution boundary. Mailbox state still protects actor
    /// payload, while admission/cancellation is exclusively keyed by the
    /// registry-owned ready set.
    pub(crate) fn run_ready_turn(self: &Arc<Self>, budget: &TurnBudget) -> AcquisitionTurnOutcome {
        let queued_at = Instant::now();
        self.lifecycle
            .data_jobs_started
            .fetch_add(1, Ordering::Relaxed);
        self.stats.worker_jobs.fetch_add(1, Ordering::Relaxed);
        self.stats
            .worker_queue_wait_us
            .fetch_add(queued_at.elapsed().as_micros() as u64, Ordering::Relaxed);
        run_acquisition_job(self, "mailbox", || process_acquisition_turn(self, budget));
        let mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        let needs_turn = !self.is_done()
            && (mailbox.token == AcquisitionWorkToken::Queued
                || (!mailbox.packets.is_empty() && !budget.must_yield_after_atomic_unit()));
        AcquisitionTurnOutcome {
            terminal: self.is_done(),
            needs_turn,
        }
    }

    fn begin_acquisition_turn(&self) -> bool {
        let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        if mailbox.token != AcquisitionWorkToken::Queued {
            return false;
        }
        mailbox.token = AcquisitionWorkToken::Running;
        true
    }

    /// Return a running token to queued only when work was observed under the
    /// same mailbox lock. Ingress that arrives before the observation is seen;
    /// ingress that arrives after it sees queued or idle and schedules itself.
    fn finish_acquisition_turn(self: &Arc<Self>) {
        let (should_enqueue, cancelled) = {
            let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
            if self.is_done() {
                (false, mailbox.clear_terminal_work())
            } else {
                (
                    mailbox.finish_turn(self.fetch_pack_ready.load(Ordering::Acquire)),
                    Vec::new(),
                )
            }
        };
        for ticket in cancelled {
            self.read_broker.cancel(ticket);
        }
        if should_enqueue {
            self.enqueue_acquisition_turn();
        }
    }

    fn take_packet_for_turn(&self) -> Option<PacketWork> {
        let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        let packet = mailbox.packets.pop_front()?;
        mailbox.packet_bytes = mailbox.packet_bytes.saturating_sub(packet.bytes);
        quaxar_metrics::acquisition::record_mailbox_packet_age(
            packet.enqueued_at.elapsed().as_secs_f64(),
        );
        quaxar_metrics::acquisition::mailbox_packet_count(mailbox.buffered_packet_count());
        quaxar_metrics::acquisition::mailbox_packet_bytes(mailbox.packet_bytes);
        Some(packet)
    }

    fn record_stale_event(&self) {
        self.mailbox
            .lock()
            .expect("acquisition mailbox lock")
            .record_late_read_event();
    }

    fn take_read_event(&self) -> Option<ReadReady> {
        self.mailbox
            .lock()
            .expect("acquisition mailbox lock")
            .take_read_event()
    }

    fn enqueue_persistence_ready(self: &Arc<Self>, ready: PersistenceReady) {
        if self.is_done() {
            return;
        }
        let should_enqueue = {
            let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
            mailbox.persistence_events.push_back(ready);
            if mailbox.token == AcquisitionWorkToken::Idle {
                mailbox.token = AcquisitionWorkToken::Queued;
                true
            } else {
                false
            }
        };
        if should_enqueue {
            self.enqueue_acquisition_turn();
        }
    }

    fn take_persistence_event(&self) -> Option<PersistenceReady> {
        self.mailbox
            .lock()
            .expect("acquisition mailbox lock")
            .persistence_events
            .pop_front()
    }

    fn local_probe_candidate(&self) -> Option<(LocalProbeKind, ReadKey)> {
        let mut mutable = self.lock_mutable("local probe candidate")?;
        let planner = mutable.inbound.planner_state();
        let candidate = if !planner.have_header {
            Some((LocalProbeKind::Header, *self.hash.as_uint256(), self.seq()))
        } else {
            let ledger = mutable.inbound.ledger_mut()?;
            if !planner.have_state && ledger.state_map_mut().hash().is_zero() {
                Some((
                    LocalProbeKind::StateRoot,
                    *ledger.header().account_hash.as_uint256(),
                    ledger.header().seq,
                ))
            } else if planner.have_state
                && !planner.have_transactions
                && ledger.tx_map_mut().hash().is_zero()
                && !ledger.header().tx_hash.is_zero()
            {
                Some((
                    LocalProbeKind::TransactionRoot,
                    *ledger.header().tx_hash.as_uint256(),
                    ledger.header().seq,
                ))
            } else {
                None
            }
        };
        candidate.map(|(kind, hash, seq)| {
            let store_generation = self.node_store.store_generation();
            (kind, ReadKey::new(hash, seq, store_generation))
        })
    }

    /// Returns true when a local probe is in flight, so callers must not issue
    /// a network request until that explicit broker outcome is reduced.
    fn request_next_local_probe(
        self: &Arc<Self>,
        reason: InboundLedgerRequestTrigger,
        peer: Option<Arc<dyn Peer>>,
    ) -> bool {
        let Some((kind, key)) = self.local_probe_candidate() else {
            return false;
        };
        {
            let mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
            if let Some(suppresses_network) = mailbox.local_probe_network_suppression(kind) {
                return suppresses_network;
            }
        }
        let weak = Arc::downgrade(self);
        let sink: ReadReadySink = Arc::new(move |ready| {
            if let Some(state) = weak.upgrade() {
                state.enqueue_read_ready(ready);
            }
        });
        match self
            .read_broker
            .request(key, self.acquisition_id, LOCAL_PROBE_PLAN_ID, sink)
        {
            ReadAdmission::Accepted(ticket) | ReadAdmission::Attached(ticket) => {
                self.mailbox
                    .lock()
                    .expect("acquisition mailbox lock")
                    .local_probes
                    .insert(
                        ticket.id().get(),
                        LocalProbe {
                            ticket,
                            kind,
                            suppresses_network: true,
                            reason,
                            peer,
                        },
                    );
                self.read_broker
                    .submit_ready_to_node_store(&self.node_store);
                self.lifecycle
                    .requests_suppressed_local_probe
                    .fetch_add(1, Ordering::Relaxed);
                true
            }
            ReadAdmission::Deferred(ticket) => {
                // Preserve the broker-owned FIFO subscription, but do not let
                // a physical-dispatch wait suppress the normal request path.
                self.mailbox
                    .lock()
                    .expect("acquisition mailbox lock")
                    .local_probes
                    .insert(
                        ticket.id().get(),
                        LocalProbe {
                            ticket,
                            kind,
                            suppresses_network: false,
                            reason,
                            peer,
                        },
                    );
                self.read_broker
                    .submit_ready_to_node_store(&self.node_store);
                self.lifecycle
                    .local_probe_deferred_network_fallbacks
                    .fetch_add(1, Ordering::Relaxed);
                false
            }
            ReadAdmission::CapacityDeferred => {
                self.lifecycle
                    .local_probe_deferred_network_fallbacks
                    .fetch_add(1, Ordering::Relaxed);
                false
            }
            ReadAdmission::Rejected(ReadRejectReason::Stopped) => false,
        }
    }

    fn take_local_probe(&self, ready: &ReadReady) -> Option<LocalProbe> {
        let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        let ticket_id = ready.ticket.id().get();
        let probe = mailbox.local_probes.get(&ticket_id)?;
        if probe.ticket != ready.ticket {
            mailbox.record_late_read_event();
            return None;
        }
        let probe = mailbox
            .local_probes
            .remove(&ticket_id)
            .expect("checked local probe must remain present");
        mailbox.completed_local_probes.insert(probe.kind);
        Some(probe)
    }

    /// Submit packet/scan batches after actor ownership is released. The
    /// NodeStore owns execution through `schedule_write`; the acquisition only
    /// receives one ticket completion per bounded batch and the final fence.
    fn submit_persistence_writes(self: &Arc<Self>, writes: Vec<PersistenceWrite>) {
        if writes.is_empty() || self.is_done() {
            return;
        }
        let store_generation = self.node_store.store_generation();
        self.persistence
            .lock()
            .expect("persistence queue lock")
            .enqueue_writes(self.acquisition_id, store_generation, writes);
        self.dispatch_next_persistence_command();
    }

    /// Reserve the final FIFO fence before resolver visibility so the
    /// provisional identity names the exact durable operation that releases it.
    fn enqueue_durability_barrier(
        self: &Arc<Self>,
        ledger_hash: Uint256,
        ledger_seq: u32,
    ) -> Option<PersistenceIdentity> {
        if self.is_done() {
            return None;
        }
        let store_generation = self.node_store.store_generation();
        let identity = self
            .persistence
            .lock()
            .expect("persistence queue lock")
            .enqueue_barrier(self.acquisition_id, store_generation);
        tracing::debug!(
            target: "inbound_ledger",
            event = "durability_barrier_enqueued",
            target_hash = %self.hash,
            ledger_hash = %ledger_hash,
            ledger_seq,
            acquisition_id = identity.acquisition_id,
            store_generation = identity.store_generation,
            persistence_generation = identity.persistence_generation,
            "inbound durability barrier enqueued behind accepted writes"
        );
        Some(identity)
    }

    fn dispatch_next_persistence_command(self: &Arc<Self>) {
        let command = self
            .persistence
            .lock()
            .expect("persistence queue lock")
            .take_next();
        let Some(command) = command else {
            return;
        };
        let state = Arc::clone(self);
        let node_store = state.node_store.clone();
        let identity = command.identity();
        let (ledger_hash, ledger_seq) = state
            .completed_ledger
            .lock()
            .expect("acquisition completed ledger lock")
            .as_ref()
            .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq))
            .unwrap_or((*state.hash.as_uint256(), state.seq()));
        if command.is_durability_barrier() {
            let timing = command.timing();
            tracing::debug!(
                target: "inbound_ledger",
                event = "durability_scheduler_dispatch",
                target_hash = %state.hash,
                ledger_hash = %ledger_hash,
                ledger_seq,
                acquisition_id = identity.acquisition_id,
                store_generation = identity.store_generation,
                persistence_generation = identity.persistence_generation,
                queue_elapsed_us = timing.enqueued_at.elapsed().as_micros() as u64,
                "inbound durability barrier dispatched to NodeStore scheduler"
            );
        }
        let completion = PersistenceCompletionGuard::new(
            Arc::clone(&state),
            identity,
            command.is_durability_barrier(),
        );
        node_store.schedule_write(Box::new(AcquisitionPersistenceWork {
            node_store: node_store.clone(),
            command,
            completion,
        }));
    }

    /// Record one completed packet's useful nodes and, only after observing
    /// its coalesced FIFO queue empty under this same mailbox lock,
    /// prune/sample the entire batch for reply triggers.
    fn finish_packet_batch(&self, peer_id: u64, useful_nodes: u64) -> Vec<u64> {
        let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        if self.is_done() {
            let cancelled = mailbox.clear_terminal_work();
            drop(mailbox);
            for ticket in cancelled {
                self.read_broker.cancel(ticket);
            }
            return Vec::new();
        }
        if useful_nodes != 0 {
            let useful_nodes = useful_nodes.min(i32::MAX as u64) as i32;
            mailbox
                .batch_useful_peer_counts
                .entry(peer_id)
                .and_modify(|count| *count = (*count).max(useful_nodes))
                .or_insert(useful_nodes);
        }

        if !mailbox.packets.is_empty() {
            return Vec::new();
        }

        let scores: Vec<_> = mailbox
            .batch_useful_peer_counts
            .iter()
            .map(|(&peer_id, &useful_count)| InboundLedgerPeerScore {
                peer_id,
                useful_count,
            })
            .collect();
        mailbox.batch_useful_peer_counts.clear();
        select_inbound_ledger_reply_peers(&scores)
    }

    fn take_admitted_timeout(&self) -> bool {
        let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        if mailbox.pending_timeouts == 0 {
            return false;
        }
        mailbox.pending_timeouts -= 1;
        true
    }

    pub(crate) fn has_pending_timeout(&self) -> bool {
        self.mailbox
            .lock()
            .expect("acquisition mailbox lock")
            .pending_timeouts
            != 0
    }

    fn record_admitted_timeout(self: &Arc<Self>) {
        if self.is_done() {
            return;
        }
        let (should_enqueue, pending_timeouts, scan_pending, buffered_packets) = {
            let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
            mailbox.pending_timeouts = mailbox.pending_timeouts.saturating_add(1);
            let should_enqueue = if mailbox.token == AcquisitionWorkToken::Idle {
                mailbox.token = AcquisitionWorkToken::Queued;
                true
            } else {
                false
            };
            (
                should_enqueue,
                mailbox.pending_timeouts,
                mailbox.plan.as_ref().is_some_and(|plan| plan.runnable),
                mailbox.buffered_packet_count(),
            )
        };
        if self.stats.should_emit_sampled_diagnostic() {
            tracing::debug!(
                target: "inbound_ledger",
                seq = self.seq(),
                hash = %self.hash,
                pending_timeouts,
                scan_pending,
                buffered_packets,
                "sampled admitted timeout parked in acquisition mailbox"
            );
        }
        if should_enqueue {
            self.lifecycle
                .data_jobs_submitted
                .fetch_add(1, Ordering::Relaxed);
        }
        // Timeouts are the recovery class of the same acquisition identity;
        // never submit a separate WorkerPool closure outside the ready set.
        self.scheduler
            .wake(self.scheduler_key, self, ReadyCause::TIMEOUT);
    }

    fn install_tree_plan(&self, plan: ActorTreePlan) -> bool {
        let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        if self.is_done() || mailbox.plan.is_some() {
            return false;
        }
        mailbox.plan = Some(plan);
        self.stats
            .state_scan_continuations
            .fetch_add(1, Ordering::Relaxed);
        true
    }

    fn take_tree_plan(&self) -> Option<ActorTreePlan> {
        self.mailbox
            .lock()
            .expect("acquisition mailbox lock")
            .plan
            .take()
    }

    fn try_restore_tree_plan(&self, plan: ActorTreePlan) -> bool {
        let mut pending = Some(plan);
        let (restored, rejected_tickets) = {
            let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
            if !self.is_done() && mailbox.plan.is_none() {
                mailbox.plan = pending.take();
                self.stats.state_scan_yields.fetch_add(1, Ordering::Relaxed);
                (true, Vec::new())
            } else {
                // A terminal transition can race while the actor temporarily
                // owns its plan. Never drop newly admitted/deferred broker
                // tickets in that gap; settle them after releasing the
                // mailbox lock just like ordinary terminal teardown.
                (
                    false,
                    pending
                        .take()
                        .expect("detached tree plan must remain owned until restoration")
                        .tickets
                        .into_values()
                        .collect::<Vec<_>>(),
                )
            }
        };
        for ticket in rejected_tickets {
            self.read_broker.cancel(ticket);
        }
        restored
    }

    fn restore_tree_plan(&self, plan: ActorTreePlan) {
        let _ = self.try_restore_tree_plan(plan);
    }

    fn restore_tree_plan_before_peer_send(
        &self,
        actor_plan: ActorTreePlan,
        send_hook: impl FnOnce(),
    ) -> bool {
        let _outbound = self
            .outbound_gate
            .lock()
            .expect("acquisition outbound gate lock");
        restore_tree_plan_before_peer_send(
            actor_plan,
            |actor_plan| self.try_restore_tree_plan(actor_plan),
            send_hook,
        )
    }

    fn send_request_while_outbound_gate(
        &self,
        message: &overlay::ProtocolMessage,
        target: Option<&Arc<dyn Peer>>,
    ) -> bool {
        if self.is_done() || self.draining.load(Ordering::Acquire) {
            return false;
        }
        self.lifecycle
            .request_messages
            .fetch_add(1, Ordering::Relaxed);
        if !self
            .first_request_metric_recorded
            .swap(true, Ordering::Relaxed)
            && let Some(elapsed) = quaxar_metrics::acquisition::peers_available_elapsed()
        {
            quaxar_metrics::acquisition::record_peer_availability_to_first_request(
                elapsed.as_secs_f64(),
            );
        }
        self.peer_set.send_request(message, target);
        true
    }

    fn send_request_if_live(
        &self,
        message: &overlay::ProtocolMessage,
        target: Option<&Arc<dyn Peer>>,
    ) -> bool {
        let _outbound = self
            .outbound_gate
            .lock()
            .expect("acquisition outbound gate lock");
        self.send_request_while_outbound_gate(message, target)
    }

    fn wake_tree_plan(self: &Arc<Self>) {
        let should_enqueue = self
            .mailbox
            .lock()
            .expect("acquisition mailbox lock")
            .wake_tree_plan();
        if should_enqueue {
            self.enqueue_acquisition_turn();
        }
    }

    fn retarget_tree_plan(
        &self,
        reason: InboundLedgerRequestTrigger,
        peer: Option<Arc<dyn Peer>>,
    ) -> Option<bool> {
        // Query the planner before taking the mailbox lock. This retains the
        // exact `> 4`, no-progress, by-hash gate used by `prepare_trigger`
        // without re-entering its whole-map request scan or replacing a plan.
        let aggressive_by_hash = reason == InboundLedgerRequestTrigger::Timeout
            && self
                .lock_mutable("timeout tree-plan policy")
                .is_some_and(|mutable| mutable.inbound.should_use_aggressive_by_hash());
        let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        let plan = mailbox.plan.as_mut()?;
        plan.retarget(reason, peer, aggressive_by_hash);
        Some(plan.runnable)
    }

    fn has_tree_plan(&self) -> bool {
        self.mailbox
            .lock()
            .expect("acquisition mailbox lock")
            .plan
            .as_ref()
            .is_some_and(|plan| plan.runnable)
    }

    fn queue_timeout_job(self: &Arc<Self>) {
        if self.is_done() {
            return;
        }
        // `AcquisitionReadyScheduler` owns the shared five-slot admission
        // boundary and recovery/normal fairness. Record the timeout in this
        // actor's mailbox, then wake that one identity through the scheduler;
        // do not bypass it with a WorkerPool-only timeout closure.
        self.record_admitted_timeout();
    }

    pub(crate) fn on_acquisition_timer_fired(self: &Arc<Self>) {
        self.timer_armed.store(false, Ordering::Release);
        self.queue_timeout_job();
    }

    fn arm_timer(self: &Arc<Self>) {
        if self.is_done()
            || self
                .timer_armed
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_err()
        {
            return;
        }
        self.worker_pool
            .schedule_acquisition_timeout(ACQUIRE_TIMEOUT, self);
    }

    fn refresh_peers(&self) {
        self.peer_set.refresh_peers((self.peer_provider)());
    }

    /// Record a fetch-pack generation for this acquisition. rippled's
    /// `gotFetchPack()` calls `checkLocal()` for every active acquisition
    /// because any retained descendant may now be resident.
    pub(crate) fn note_fetch_pack_generation(&self, generation: u64) -> bool {
        if self.is_done() {
            return false;
        }
        let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        if generation <= mailbox.pending_fetch_pack_generation {
            return false;
        }
        mailbox.pending_fetch_pack_generation = generation;
        self.fetch_pack_ready.store(true, Ordering::Release);
        if mailbox.token == AcquisitionWorkToken::Idle {
            mailbox.token = AcquisitionWorkToken::Queued;
        }
        true
    }

    pub(crate) fn diagnostics(&self) -> AcquisitionSnapshot {
        let (seq, planner, timeouts) = self
            .lock_mutable("diagnostics")
            .map(|mutable| {
                (
                    mutable.inbound.seq(),
                    mutable.inbound.planner_state(),
                    mutable.inbound.timeout_count(),
                )
            })
            .unwrap_or((self.seq(), Default::default(), 0));
        let (
            buffered_packets,
            buffered_packets_high_water,
            mailbox_token,
            scan_continuation_pending,
            pending_admitted_timeouts,
        ) = {
            let mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
            (
                mailbox.buffered_packet_count(),
                mailbox.buffered_packets_high_water,
                mailbox.token.name(),
                mailbox.plan.is_some(),
                mailbox.pending_timeouts,
            )
        };
        let header_after_ms = self
            .stats
            .first_header_at
            .lock()
            .expect("acquisition first_header_at lock")
            .map(|at| at.duration_since(self.stats.started_at).as_millis() as u64);
        AcquisitionSnapshot {
            age_ms: self.stats.started_at.elapsed().as_millis() as u64,
            header_after_ms,
            seq,
            have_header: planner.have_header,
            have_state: planner.have_state,
            have_transactions: planner.have_transactions,
            timeouts,
            packets: self.stats.packets.load(Ordering::Relaxed),
            useful_packets: self.stats.useful_packets.load(Ordering::Relaxed),
            useful_nodes: self.stats.useful_nodes.load(Ordering::Relaxed),
            state_packets: self.stats.state_packets.load(Ordering::Relaxed),
            state_useful_nodes: self.stats.state_useful_nodes.load(Ordering::Relaxed),
            state_duplicate_nodes: self.stats.state_duplicate_nodes.load(Ordering::Relaxed),
            malformed_packets: self.stats.malformed_packets.load(Ordering::Relaxed),
            state_scan_runs: self.stats.state_scan_runs.load(Ordering::Relaxed),
            state_missing_nodes: self.stats.state_missing_nodes.load(Ordering::Relaxed),
            tx_missing_nodes: self.stats.tx_missing_nodes.load(Ordering::Relaxed),
            state_scan_us: self.stats.state_scan_us.load(Ordering::Relaxed),
            state_scan_branch_steps: self.stats.state_scan_branch_steps.load(Ordering::Relaxed),
            state_scan_missing_nodes_recorded: self
                .stats
                .state_scan_missing_nodes_recorded
                .load(Ordering::Relaxed),
            state_scan_positive_progress_slices: self
                .stats
                .state_scan_positive_progress_slices
                .load(Ordering::Relaxed),
            state_scan_branch_budget_yields: self
                .stats
                .state_scan_branch_budget_yields
                .load(Ordering::Relaxed),
            state_scan_deferred_read_budget_yields: self
                .stats
                .state_scan_deferred_read_budget_yields
                .load(Ordering::Relaxed),
            state_scan_deferred_read_resume_yields: self
                .stats
                .state_scan_deferred_read_resume_yields
                .load(Ordering::Relaxed),
            state_scan_missing_node_limit_yields: self
                .stats
                .state_scan_missing_node_limit_yields
                .load(Ordering::Relaxed),
            state_scan_completed_slices: self
                .stats
                .state_scan_completed_slices
                .load(Ordering::Relaxed),
            state_scan_last_yield: scan_outcome_name(
                self.stats.state_scan_last_outcome.load(Ordering::Relaxed),
            ),
            state_scan_last_branch_steps: self
                .stats
                .state_scan_last_branch_steps
                .load(Ordering::Relaxed),
            state_scan_last_deferred_reads: self
                .stats
                .state_scan_last_deferred_reads
                .load(Ordering::Relaxed),
            state_scan_last_deferred_resumes: self
                .stats
                .state_scan_last_deferred_resumes
                .load(Ordering::Relaxed),
            state_scan_last_missing_nodes: self
                .stats
                .state_scan_last_missing_nodes
                .load(Ordering::Relaxed),
            state_scan_branches_seen: self.stats.state_scan_branches_seen.load(Ordering::Relaxed),
            state_scan_duplicate_missing_hashes: self
                .stats
                .state_scan_duplicate_missing_hashes
                .load(Ordering::Relaxed),
            state_scan_full_below_hits: self
                .stats
                .state_scan_full_below_hits
                .load(Ordering::Relaxed),
            state_scan_loaded_or_cached_children: self
                .stats
                .state_scan_loaded_or_cached_children
                .load(Ordering::Relaxed),
            state_scan_pending_reads: self.stats.state_scan_pending_reads.load(Ordering::Relaxed),
            state_scan_read_slot_full: self.stats.state_scan_read_slot_full.load(Ordering::Relaxed),
            state_scan_read_admission_accepted: self
                .stats
                .state_scan_read_admission_accepted
                .load(Ordering::Relaxed),
            state_scan_read_admission_deferred: self
                .stats
                .state_scan_read_admission_deferred
                .load(Ordering::Relaxed),
            state_scan_read_admission_attached: self
                .stats
                .state_scan_read_admission_attached
                .load(Ordering::Relaxed),
            state_scan_read_broker_rejected: self
                .stats
                .state_scan_read_broker_rejected
                .load(Ordering::Relaxed),
            state_scan_max_pending_reads: self
                .stats
                .state_scan_max_pending_reads
                .load(Ordering::Relaxed),
            state_scan_pending_hits: self.stats.state_scan_pending_hits.load(Ordering::Relaxed),
            state_scan_pending_misses: self.stats.state_scan_pending_misses.load(Ordering::Relaxed),
            state_scan_deferred_resumes: self
                .stats
                .state_scan_deferred_resumes
                .load(Ordering::Relaxed),
            state_scan_yields: self.stats.state_scan_yields.load(Ordering::Relaxed),
            state_scan_continuations: self.stats.state_scan_continuations.load(Ordering::Relaxed),
            timeout_dispatches: self.stats.timeout_dispatches.load(Ordering::Relaxed),
            state_scan_max_buffered_packets: self
                .stats
                .state_scan_max_buffered_packets
                .load(Ordering::Relaxed),
            data_drain_runs: self.stats.data_drain_runs.load(Ordering::Relaxed),
            data_drain_us: self.stats.data_drain_us.load(Ordering::Relaxed),
            data_drain_max_us: self.stats.data_drain_max_us.load(Ordering::Relaxed),
            data_drain_max_packets: self.stats.data_drain_max_packets.load(Ordering::Relaxed),
            tx_scan_us: self.stats.tx_scan_us.load(Ordering::Relaxed),
            worker_jobs: self.stats.worker_jobs.load(Ordering::Relaxed),
            worker_queue_wait_us: self.stats.worker_queue_wait_us.load(Ordering::Relaxed),
            node_store_fetch_hits: self.stats.node_store_fetch_hits.load(Ordering::Relaxed),
            node_store_fetch_misses: self.stats.node_store_fetch_misses.load(Ordering::Relaxed),
            tracked_peers: self.peer_set.peer_count(),
            buffered_packets,
            buffered_packets_high_water,
            mailbox_token,
            scan_continuation_pending,
            pending_admitted_timeouts,
        }
    }

    /// Explicit terminal cancellation revokes a resolver-visible provisional
    /// identity through the failure recorder while its registry entry is still
    /// available. Other cancellations only settle local work and reservations.
    pub(crate) fn cancel(&self) {
        if self.provisional_registered.load(Ordering::Acquire)
            && !self.completed.load(Ordering::Acquire)
        {
            self.mark_failed();
            return;
        }
        let tickets = {
            let _outbound = self
                .outbound_gate
                .lock()
                .expect("acquisition outbound gate lock");
            if self.stopped.swap(true, Ordering::AcqRel) {
                return;
            }
            self.scheduler.cancel(self.scheduler_key);
            self.persistence
                .lock()
                .expect("persistence queue lock")
                .cancel();
            self.clear_terminal_work()
        };
        for ticket in tickets {
            self.read_broker.cancel(ticket);
        }
    }

    fn is_done(&self) -> bool {
        self.stopped.load(Ordering::Acquire)
            || self.completed.load(Ordering::Acquire)
            || self.failed.load(Ordering::Acquire)
    }

    /// Settle mailbox-owned packet work and transport leases at the actor
    /// boundary. The caller cancels returned broker tickets after releasing
    /// any lifecycle gate; a cleared reservation cannot be released again by
    /// a later lease drop.
    pub(crate) fn clear_terminal_work(&self) -> Vec<ReadTicket> {
        self.mailbox
            .lock()
            .expect("acquisition mailbox lock")
            .clear_terminal_work()
    }

    /// A resolver-visible ledger may remain in ordered persistence after the
    /// app has acknowledged its cache handoff. Registry sweep must retain this
    /// state until the FIFO durability barrier has settled.
    pub(crate) fn has_pending_durability(&self) -> bool {
        self.draining.load(Ordering::Acquire)
            && !self.completed.load(Ordering::Acquire)
            && !self.failed.load(Ordering::Acquire)
            && !self.stopped.load(Ordering::Acquire)
    }

    /// Refuse to continue an acquisition after an unwind poisoned its mutable
    /// planner state. Dropping the recovered guard first prevents the failure
    /// recorder from re-entering while this mutex remains locked.
    fn lock_mutable(&self, operation: &'static str) -> Option<MutexGuard<'_, AcqMutableState>> {
        match self.mutable.lock() {
            Ok(mutable) => Some(mutable),
            Err(poison) => {
                drop(poison.into_inner());
                tracing::error!(
                    target: "inbound_ledger",
                    operation,
                    seq = self.seq(),
                    hash = %self.hash,
                    "acquisition mutable state was poisoned; failing acquisition"
                );
                self.mark_failed();
                None
            }
        }
    }

    fn mark_failed(&self) {
        let tickets = {
            let _outbound = self
                .outbound_gate
                .lock()
                .expect("acquisition outbound gate lock");
            if self
                .failure_claimed
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_err()
            {
                return;
            }
            // InboundLedger::done touches before dispatching AcqDone. Keep the
            // matching registry entry alive and record its cooldown before any
            // strand poll or sweep can observe the terminal failure flags.
            (self.failure_recorder)(*self.hash.as_uint256());
            self.scheduler.cancel(self.scheduler_key);
            self.persistence
                .lock()
                .expect("persistence queue lock")
                .cancel();
            self.failed.store(true, Ordering::Release);
            self.stopped.store(true, Ordering::Release);
            // Failure can be raised outside a normal actor turn (for example from
            // a persistence acknowledgement or a poisoned mutable guard). Settle
            // all retained tree and local-probe subscriptions here rather than
            // relying on a later sweep or callback to reclaim broker capacity.
            self.clear_terminal_work()
        };
        for ticket in tickets {
            self.read_broker.cancel(ticket);
        }
        self.lifecycle
            .terminal_failed
            .fetch_add(1, Ordering::Relaxed);
    }

    pub(crate) fn take_buffered_packets(&self) -> Vec<ledger::InboundLedgerReceivedPacket> {
        let mut mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        let packets = std::mem::take(&mut mailbox.packets);
        mailbox.packet_bytes = 0;
        packets
            .into_iter()
            .map(|work| ledger::InboundLedgerReceivedPacket::new(Some(work.peer_id), work.packet))
            .collect()
    }

    fn has_pending_packets(&self) -> bool {
        let mailbox = self.mailbox.lock().expect("acquisition mailbox lock");
        !mailbox.packets.is_empty()
    }

    pub(crate) fn seq(&self) -> u32 {
        self.seq.load(Ordering::Acquire)
    }

    /// Propagate the verified canonical sequence only while this acquisition
    /// remains hash-only. Header mismatch rejection belongs to
    /// `InboundLedgerLocal`; this mirror only publishes its settled result.
    /// The gate also covers registry promotion so routing cannot validate a
    /// zero sequence and enqueue after this promotion has completed.
    fn promote_seq(&self, sequence: u32) -> bool {
        if sequence == 0 {
            return false;
        }
        #[cfg(test)]
        if let Some(attempt) = self
            .sequence_promotion_attempt
            .lock()
            .expect("sequence promotion attempt lock")
            .clone()
        {
            attempt.mark_attempted();
        }
        let _sequence_gate = self
            .sequence_gate
            .lock()
            .expect("acquisition sequence gate");
        if self
            .seq
            .compare_exchange(0, sequence, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            (self.sequence_promoter)(sequence);
            return true;
        }
        false
    }

    fn sync_header_sequence(&self, sequence: u32) {
        if self.promote_seq(sequence) {
            self.lifecycle
                .header_sequences_promoted
                .fetch_add(1, Ordering::Relaxed);
            tracing::debug!(
                target: "inbound_ledger",
                hash = %self.hash,
                acquisition_id = self.acquisition_id,
                seq = sequence,
                "promoted verified inbound ledger sequence"
            );
        }
    }

    pub(crate) fn update_seq(&self, seq: u32) {
        let canonical_seq = {
            let Some(mut mutable) = self.lock_mutable("update sequence") else {
                return;
            };
            // Match rippled `InboundLedger::update`: do not replace a known
            // value, including one learned by a racing header parse.
            mutable.inbound.update(seq, time::Duration::ZERO);
            mutable.inbound.seq()
        };
        self.promote_seq(canonical_seq);
    }

    #[cfg(test)]
    pub(crate) fn set_sequence_route_pause_for_test(&self, pause: Arc<SequenceRoutePause>) {
        *self
            .sequence_route_pause
            .lock()
            .expect("sequence route pause lock") = Some(pause);
    }

    #[cfg(test)]
    pub(crate) fn set_sequence_promotion_attempt_for_test(
        &self,
        attempt: Arc<SequencePromotionAttempt>,
    ) {
        *self
            .sequence_promotion_attempt
            .lock()
            .expect("sequence promotion attempt lock") = Some(attempt);
    }

    pub(crate) fn completed_ledger(&self) -> Option<Arc<Ledger>> {
        if let Some(ledger) = self
            .completed_ledger
            .lock()
            .expect("acquisition completed ledger lock")
            .clone()
        {
            return Some(ledger);
        }
        self.lock_mutable("completed ledger")?
            .inbound
            .ledger()
            .cloned()
            .map(Arc::new)
    }
}

pub struct AcquisitionBuilder {
    pub hash: SHAMapHash,
    pub acquisition_id: u64,
    pub seq: u32,
    pub reason: AcquireReason,
    pub node_store: SHAMapStoreNodeStore,
    pub read_broker: NodeReadBroker,
    pub tree_cache: Arc<TreeNodeCache<MonotonicClock>>,
    pub fetch_pack: Arc<FetchPackCache>,
    pub store_tx: std::sync::mpsc::SyncSender<CompletedInboundLedger>,
    pub failure_recorder: AcquisitionFailureRecorder,
    pub sequence_promoter: AcquisitionSequencePromoter,
    pub completion_recorder: AcquisitionCompletionRecorder,
    pub durable_completion_recorder: AcquisitionDurableCompletionRecorder,
    pub shared_full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
    pub worker_pool: Arc<WorkerPool>,
    pub scheduler: Arc<AcquisitionReadyScheduler>,
    pub initial_peers: Vec<Arc<dyn Peer>>,
    pub peer_provider: AcquisitionPeerProvider,
    pub lifecycle: Arc<AcquisitionLifecycleCounters>,
}

impl AcquisitionBuilder {
    pub fn build(self) -> Arc<AcquisitionState> {
        let reason = match self.reason {
            AcquireReason::History => InboundLedgerReason::History,
            AcquireReason::Generic => InboundLedgerReason::Generic,
            AcquireReason::Consensus => InboundLedgerReason::Consensus,
        };
        let stats = Arc::new(AcquisitionStats::new());
        Arc::new(AcquisitionState {
            mailbox: Mutex::new(AcquisitionMailbox::default()),
            sequence_gate: Mutex::new(()),
            #[cfg(test)]
            state_scan_after_advance_pause: Mutex::new(None),
            #[cfg(test)]
            sequence_route_pause: Mutex::new(None),
            #[cfg(test)]
            sequence_promotion_attempt: Mutex::new(None),
            mutable: Mutex::new(AcqMutableState {
                inbound: InboundLedgerLocal::new_with_reason(self.hash, self.seq, reason),
                store: WorkerStore {
                    pending_writes: Vec::new(),
                    pending_keys: BTreeSet::new(),
                },
                fetch_pack: WorkerFetchPack {
                    cache: self.fetch_pack,
                },
            }),
            hash: self.hash,
            acquisition_id: self.acquisition_id,
            seq: AtomicU32::new(self.seq),
            reason: self.reason,
            peer_set: overlay::SimplePeerSet::new(self.initial_peers),
            peer_provider: self.peer_provider,
            stats,
            shared_full_below: self.shared_full_below,
            node_store: self.node_store,
            read_broker: self.read_broker,
            persistence: Mutex::new(PersistenceQueue::default()),
            outbound_gate: Mutex::new(()),
            draining: AtomicBool::new(false),
            next_plan_id: AtomicU64::new(1),
            shared_tree_cache: self.tree_cache,
            store_tx: self.store_tx,
            failure_recorder: self.failure_recorder,
            sequence_promoter: self.sequence_promoter,
            completion_recorder: self.completion_recorder,
            durable_completion_recorder: self.durable_completion_recorder,
            stopped: AtomicBool::new(false),
            completed: AtomicBool::new(false),
            completed_ledger: Mutex::new(None),
            failed: AtomicBool::new(false),
            failure_claimed: AtomicBool::new(false),
            resolver_publication_claimed: AtomicBool::new(false),
            provisional_registered: AtomicBool::new(false),
            resolver_published: AtomicBool::new(false),
            finalization_claimed: AtomicBool::new(false),
            fetch_pack_ready: AtomicBool::new(false),
            timer_armed: AtomicBool::new(false),
            // Observability only: records peer-availability-to-first-request
            // latency once per session; does not gate any request production.
            first_request_metric_recorded: AtomicBool::new(false),
            worker_pool: self.worker_pool,
            scheduler_key: AcquisitionKey {
                hash: *self.hash.as_uint256(),
                id: self.acquisition_id,
            },
            scheduler: self.scheduler,
            lifecycle: self.lifecycle,
        })
    }
}

fn run_acquisition_job(state: &Arc<AcquisitionState>, operation: &'static str, job: impl FnOnce()) {
    if let Err(payload) = catch_unwind(AssertUnwindSafe(job)) {
        let message = payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| {
                payload
                    .downcast_ref::<&str>()
                    .map(|message| (*message).to_owned())
            })
            .unwrap_or_else(|| "non-string panic payload".to_owned());
        tracing::error!(
            target: "inbound_ledger",
            operation,
            seq = state.seq(),
            hash = %state.hash,
            %message,
            "acquisition job panicked; failing acquisition"
        );
        state.mark_failed();
        state.finish_acquisition_turn();
    }
}

pub(crate) struct ActorNodeFetcher;

impl shamap::family::SHAMapNodeFetcher for ActorNodeFetcher {
    fn fetch_node_object(
        &self,
        _hash: SHAMapHash,
        _ledger_seq: u32,
    ) -> Option<shamap::node_object::NodeObject> {
        // Acquisition reads are exclusively brokered asynchronously. Packet
        // verification may consult resident/fetch-pack data but never falls
        // through to a synchronous NodeStore read while actor state is held.
        None
    }
}

fn family(
    state: &AcquisitionState,
) -> SHAMapFamily<
    MonotonicClock,
    HardenedHashBuilder,
    Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
    ActorNodeFetcher,
    NullMissingNodeReporter,
    (),
> {
    SHAMapFamily::new(
        Arc::clone(&state.shared_tree_cache),
        Arc::clone(&state.shared_full_below),
        ActorNodeFetcher,
        NullMissingNodeReporter,
    )
}

fn trigger(
    state: &Arc<AcquisitionState>,
    reason: InboundLedgerRequestTrigger,
    peer: Option<Arc<dyn Peer>>,
) {
    if state.is_done() || state.draining.load(Ordering::Acquire) {
        return;
    }
    if state.request_next_local_probe(reason, peer.clone()) {
        return;
    }
    state
        .lifecycle
        .request_triggers
        .fetch_add(1, Ordering::Relaxed);
    if let Some(should_wake) = state.retarget_tree_plan(reason, peer.clone()) {
        if should_wake {
            // If the trigger arrived while idle, claim one bounded actor turn.
            // A running turn coalesces this wake and observes `runnable` in
            // `finish_acquisition_turn`.
            state.wake_tree_plan();
        }
        return;
    }

    // Planner mutation is isolated from command emission. In particular, peer
    // sends happen only after this guard is dropped.
    let (messages, plan, terminal, canonical_seq) = {
        let Some(mut mutable) = state.lock_mutable("trigger") else {
            return;
        };
        let AcqMutableState {
            inbound,
            store,
            fetch_pack,
        } = &mut *mutable;
        let journal = WorkerJournal;
        let config = ledger::LedgerConfig::default();
        let family = family(state);
        let setup = inbound.prepare_trigger(reason, &journal, &config, store, fetch_pack, &family);
        let kind = if setup.state_plan {
            Some(TreeKind::State)
        } else if setup.tx_plan {
            Some(TreeKind::Transaction)
        } else {
            None
        };
        let plan = kind
            .and_then(|kind| {
                inbound.start_tree_plan(
                    kind,
                    TreePlanId::new(state.next_plan_id.fetch_add(1, Ordering::Relaxed)),
                    state.shared_full_below.generation(),
                )
            })
            .map(|plan| ActorTreePlan {
                plan,
                reason,
                peer: peer.clone(),
                tickets: BTreeMap::new(),
                read_admission_backlog: VecDeque::new(),
                runnable: true,
                aggressive_by_hash: false,
            });
        (
            setup.messages_to_send,
            plan,
            inbound.is_failed() || inbound.is_complete(),
            inbound.seq(),
        )
    };
    state.sync_header_sequence(canonical_seq);

    for message in messages {
        if !state.send_request_if_live(&message, peer.as_ref()) {
            return;
        }
    }
    if let Some(plan) = plan
        && state.install_tree_plan(plan)
    {
        state.submit_data_job();
    }
    if terminal {
        finalize_terminal(state);
    }
}

fn peer_has_acquisition_target(peer: &Arc<dyn Peer>, hash: Uint256, seq: u32) -> bool {
    // Match PeerImp::hasLedger exactly: a zero sequence has no range claim,
    // so it is eligible only when the peer advertised this exact recent hash.
    peer.has_ledger(hash, seq)
}

fn add_peers(state: &AcquisitionState) -> Vec<Arc<dyn Peer>> {
    // Rippled's PeerSet walks the live overlay on every addPeers call. Refresh
    // immediately before scoring so an acquisition started before a usable
    // peer connected can recruit that peer on the next no-progress turn.
    state.refresh_peers();
    let limit = if state.peer_set.peer_count() == 0 {
        PEER_COUNT_START
    } else {
        PEER_COUNT_ADD
    };
    let hash = *state.hash.as_uint256();
    let mut eligible = 0u64;
    let mut added = Vec::new();
    state.peer_set.add_peers(
        limit,
        &mut |peer| {
            let has_target = peer_has_acquisition_target(peer, hash, state.seq());
            if has_target {
                eligible += 1;
            }
            has_target
        },
        &mut |peer| added.push(Arc::clone(peer)),
    );
    state
        .lifecycle
        .peer_candidates_eligible
        .fetch_add(eligible, Ordering::Relaxed);
    state
        .lifecycle
        .peers_added
        .fetch_add(added.len() as u64, Ordering::Relaxed);
    added
}

fn check_local(state: &AcquisitionState, mutable: &mut AcqMutableState) {
    let AcqMutableState {
        inbound,
        store,
        fetch_pack,
    } = mutable;
    let journal = WorkerJournal;
    let config = ledger::LedgerConfig::default();
    let family = family(state);
    inbound.check_local_with_family_and_config(&journal, &config, store, fetch_pack, &family);
}

fn process_init(state: &Arc<AcquisitionState>) {
    if state.is_done() {
        return;
    }
    let (persistence_writes, terminal, canonical_seq) = {
        let Some(mut mutable) = state.lock_mutable("initialization") else {
            return;
        };
        check_local(state, &mut mutable);
        let persistence_writes = mutable.store.take_pending_writes();
        let terminal = mutable.inbound.is_failed() || mutable.inbound.is_complete();
        (persistence_writes, terminal, mutable.inbound.seq())
    };
    state.sync_header_sequence(canonical_seq);
    let added = if terminal {
        Vec::new()
    } else {
        add_peers(state)
    };
    state.submit_persistence_writes(persistence_writes);
    if terminal {
        finalize_terminal(state);
        return;
    }
    if state.reason != AcquireReason::History {
        for peer in added {
            trigger(state, InboundLedgerRequestTrigger::Added, Some(peer));
        }
    }
    state.queue_timeout_job();
}

fn process_acquisition_turn(state: &Arc<AcquisitionState>, budget: &TurnBudget) {
    if !state.begin_acquisition_turn() {
        return;
    }
    if state.is_done() {
        state.finish_acquisition_turn();
        return;
    }

    // Event-first fairness: recovery is never disabled by pending reads; a
    // fair packet batch and one plan advance then yield to the shared worker
    // queue.
    if state.take_admitted_timeout() {
        process_timeout_job(state);
    }
    if !state.is_done()
        && (state.has_pending_packets() || state.fetch_pack_ready.load(Ordering::Acquire))
    {
        process_data_job(state, budget);
    }
    if !state.is_done() {
        process_persistence_event(state);
    }
    if !state.is_done() {
        process_read_events(state, budget);
    }
    if !state.is_done() && state.has_tree_plan() {
        process_tree_plan_turn(state, budget);
    }
    state.finish_acquisition_turn();
}

/// Apply peer nodes that packet validation has already accepted to a retained
/// plan. A matching network attachment may unblock deferred parent resumes;
/// that is runnable actor work, not a passive cache update.
fn apply_verified_peer_nodes_to_plan(
    actor_plan: &mut ActorTreePlan,
    nodes: impl IntoIterator<
        Item = basics::intrusive_pointer::SharedIntrusive<shamap::tree_node::SHAMapTreeNode>,
    >,
) -> bool {
    let plan_id = actor_plan.plan.id();
    let mut unblocked_deferred_parent = false;
    for node in nodes {
        let hash = node.get_hash();
        if matches!(
            actor_plan.plan.apply_network_node(plan_id, hash, node),
            MissingNodeReadApply::Applied { attached_edges, .. } if attached_edges != 0
        ) {
            unblocked_deferred_parent = true;
        }
    }
    if unblocked_deferred_parent && actor_plan.plan.has_runnable_frontier() {
        actor_plan.runnable = true;
        return true;
    }
    false
}

fn apply_packet_nodes_to_plan(
    state: &Arc<AcquisitionState>,
    packet_type: InboundLedgerDataType,
    nodes: Vec<basics::intrusive_pointer::SharedIntrusive<shamap::tree_node::SHAMapTreeNode>>,
) {
    let expected_kind = match packet_type {
        InboundLedgerDataType::StateNode => TreeKind::State,
        InboundLedgerDataType::TransactionNode => TreeKind::Transaction,
        InboundLedgerDataType::Base => return,
    };
    let Some(mut actor_plan) = state.take_tree_plan() else {
        return;
    };
    if actor_plan.plan.kind() != expected_kind {
        state.restore_tree_plan(actor_plan);
        return;
    }
    let wake_bounded_turn = apply_verified_peer_nodes_to_plan(&mut actor_plan, nodes);
    state.restore_tree_plan(actor_plan);
    if wake_bounded_turn {
        // Idle callers claim one queued turn immediately. During a running
        // packet turn, `finish_acquisition_turn` observes `runnable` and
        // queues the same bounded continuation without recursion.
        state.wake_tree_plan();
    }
}

/// Drain the packet batch ready for this acquisition, yielding only after an
/// atomic packet reduction when another ready identity has consumed its fair
/// elapsed-work share. This mirrors `InboundLedger::runData()`'s swap-and-drain
/// loop while retaining the Rust scheduler's cross-acquisition fairness bound.
fn process_data_job(state: &Arc<AcquisitionState>, budget: &TurnBudget) {
    loop {
        let processed_packet = state.has_pending_packets();
        process_one_data_job(state);
        if state.is_done()
            || !state.has_pending_packets()
            || (processed_packet && budget.must_yield_after_atomic_unit())
        {
            return;
        }
    }
}

/// Record a first accepted wire header even when that packet also reaches a
/// terminal inbound state. The pre-packet header observation keeps both the
/// timestamp and lifecycle counter exactly once per acquisition.
fn record_first_packet_header_received(
    stats: &AcquisitionStats,
    lifecycle: &AcquisitionLifecycleCounters,
    had_header: bool,
    have_header_after_processing: bool,
    terminal_after_processing: bool,
) {
    if matches!(
        (
            had_header,
            have_header_after_processing,
            terminal_after_processing,
        ),
        (false, true, _)
    ) {
        stats.mark_header_received();
        lifecycle
            .reply_headers_received
            .fetch_add(1, Ordering::Relaxed);
    }
}

fn process_one_data_job(state: &Arc<AcquisitionState>) {
    if state.is_done() {
        return;
    }

    let Some(work) = state.take_packet_for_turn() else {
        let (terminal, persistence_writes, canonical_seq) = {
            let Some(mut mutable) = state.lock_mutable("data processing") else {
                return;
            };
            let data_drain_started = Instant::now();
            if state.fetch_pack_ready.swap(false, Ordering::AcqRel) {
                check_local(state, &mut mutable);
                let mut mailbox = state.mailbox.lock().expect("acquisition mailbox lock");
                mailbox.handled_fetch_pack_generation = mailbox.pending_fetch_pack_generation;
            }
            let terminal = mutable.inbound.is_failed() || mutable.inbound.is_complete();
            let persistence_writes = mutable.store.take_pending_writes();
            state
                .stats
                .record_data_drain(data_drain_started.elapsed().as_micros() as u64, 0);
            (terminal, persistence_writes, mutable.inbound.seq())
        };
        state.sync_header_sequence(canonical_seq);
        state.submit_persistence_writes(persistence_writes);
        if terminal {
            finalize_terminal(state);
        }
        return;
    };

    let step_start = 0;
    let mut accepted_nodes = Vec::new();
    let data_drain_started = Instant::now();
    let packet_type = work.packet.packet_type;
    let peer_id = work.peer_id;
    let mut packet_stats = SHAMapAddNode::default();
    let mut packet_complete = false;
    let mut malformed = None;
    let mut invalid = false;
    let mut had_header = false;
    let terminal;
    let persistence_writes;
    let canonical_seq;
    {
        let Some(mut mutable) = state.lock_mutable("data processing") else {
            return;
        };
        if state.fetch_pack_ready.swap(false, Ordering::AcqRel) {
            check_local(state, &mut mutable);
        }
        let AcqMutableState {
            inbound,
            store,
            fetch_pack,
        } = &mut *mutable;
        if !(inbound.is_failed() || inbound.is_complete()) {
            had_header = inbound.planner_state().have_header;
            let journal = WorkerJournal;
            let config = ledger::LedgerConfig::default();
            let family = family(state);
            match inbound.process_packet_with_family_and_config(
                &work.packet,
                &journal,
                &config,
                store,
                fetch_pack,
                &family,
            ) {
                Ok(stats) => {
                    packet_stats = stats;
                    packet_complete = true;
                    if !matches!(packet_type, InboundLedgerDataType::Base) && !stats.is_invalid() {
                        accepted_nodes.extend(work.packet.nodes[step_start..].iter().filter_map(
                            |node| {
                                shamap::tree_node::SHAMapTreeNode::make_from_wire(&node.node_data)
                                    .ok()
                                    .flatten()
                            },
                        ));
                    }
                    inbound.record_packet_stats_with_family_and_config(
                        packet_stats,
                        &journal,
                        &config,
                        &family,
                    );
                    invalid = packet_stats.is_invalid();
                }
                Err(error) => {
                    malformed = Some(error);
                    packet_complete = true;
                }
            }
        }
        terminal = inbound.is_failed() || inbound.is_complete();
        canonical_seq = inbound.seq();
        persistence_writes = store.take_pending_writes();
    }

    // The packet reducer has released `mutable`; physical NodeStore I/O now
    // enters the actor-external FIFO command queue.
    state.sync_header_sequence(canonical_seq);
    state.submit_persistence_writes(persistence_writes);

    let data_drain_us = data_drain_started.elapsed().as_micros() as u64;
    state.stats.record_data_drain(data_drain_us, 1);
    if state.stats.should_emit_sampled_diagnostic() {
        tracing::debug!(
            target: "inbound_ledger",
            seq = state.seq(),
            hash = %state.hash,
            drain_us = data_drain_us,
            nodes = work.packet.nodes.len(),
            "sampled full inbound data packet"
        );
    }

    if !accepted_nodes.is_empty() && !invalid && malformed.is_none() {
        apply_packet_nodes_to_plan(state, packet_type, accepted_nodes);
    }
    let have_header_after_processing = state
        .lock_mutable("data header diagnostics")
        .map(|mutable| mutable.inbound.planner_state().have_header)
        .unwrap_or(false);
    record_first_packet_header_received(
        &state.stats,
        &state.lifecycle,
        had_header,
        have_header_after_processing,
        terminal,
    );
    state.lifecycle.packet_steps.fetch_add(1, Ordering::Relaxed);
    if packet_complete {
        state
            .lifecycle
            .packet_steps_completed
            .fetch_add(1, Ordering::Relaxed);
    }
    state.stats.packets.fetch_add(1, Ordering::Relaxed);
    let useful_nodes = packet_stats.get_good().max(0) as u64;
    state
        .stats
        .useful_packets
        .fetch_add(u64::from(useful_nodes != 0), Ordering::Relaxed);
    state
        .stats
        .useful_nodes
        .fetch_add(useful_nodes, Ordering::Relaxed);
    if packet_type == ledger::InboundLedgerDataType::StateNode {
        state.stats.state_packets.fetch_add(1, Ordering::Relaxed);
        state
            .stats
            .state_useful_nodes
            .fetch_add(useful_nodes, Ordering::Relaxed);
        state.stats.state_duplicate_nodes.fetch_add(
            packet_stats.get_duplicate().max(0) as u64,
            Ordering::Relaxed,
        );
    }
    let packet_error_count = usize::from(malformed.is_some()) + usize::from(invalid);
    state
        .lifecycle
        .packet_step_errors
        .fetch_add(packet_error_count as u64, Ordering::Relaxed);
    if let Some(error) = malformed {
        state
            .stats
            .malformed_packets
            .fetch_add(1, Ordering::Relaxed);
        charge_malformed_packet(state, peer_id, packet_type, error);
    }
    if invalid {
        charge_invalid_data_packet(
            state,
            peer_id,
            packet_type,
            InboundLedgerPacketError::InvalidData,
        );
    }

    if terminal {
        finalize_terminal(state);
        return;
    }
    // A registry terminal transition can race after the packet mutation lock
    // is released. It must suppress this packet's deferred reply triggers;
    // `finish_acquisition_turn` performs the ordinary mailbox cleanup.
    if state.is_done() {
        return;
    }
    // Do not trigger once per completed packet. The mailbox records useful
    // results in FIFO order and returns peers only after it observed the
    // coalesced queue empty under the same lock; a concurrent later arrival
    // becomes the next batch.
    for reply_peer_id in state.finish_packet_batch(peer_id, useful_nodes) {
        if let Some(peer) = state.peer_set.find_peer(reply_peer_id as u32) {
            let reason = if peer.is_high_latency() {
                InboundLedgerRequestTrigger::ReplyHighLatency
            } else {
                InboundLedgerRequestTrigger::Reply
            };
            trigger(state, reason, Some(peer));
        }
    }
}
struct ActorResident<'a> {
    cache: &'a TreeNodeCache<MonotonicClock>,
    full_below: &'a FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>,
}

impl MissingNodeResidentLookup for ActorResident<'_> {
    fn load_resident(
        &mut self,
        hash: SHAMapHash,
        _ledger_seq: u32,
    ) -> Option<basics::intrusive_pointer::SharedIntrusive<shamap::tree_node::SHAMapTreeNode>> {
        self.cache.fetch(hash.as_uint256())
    }

    fn is_full_below(&mut self, hash: SHAMapHash) -> bool {
        self.full_below.touch_if_exists(*hash.as_uint256())
    }

    fn mark_full_below(
        &mut self,
        node: basics::intrusive_pointer::SharedIntrusive<shamap::tree_node::SHAMapTreeNode>,
        generation: u32,
    ) {
        node.set_full_below_gen(generation);
        self.full_below.insert(*node.get_hash().as_uint256());
    }
}

fn fail_actor_plan(state: &AcquisitionState, actor_plan: ActorTreePlan) {
    for ticket in actor_plan.tickets.into_values() {
        state.read_broker.cancel(ticket);
    }
    state.mark_failed();
}

fn process_persistence_event(state: &Arc<AcquisitionState>) {
    let Some(mut ready) = state.take_persistence_event() else {
        return;
    };
    // PersistenceIdentity is immutable across the schedule/callback boundary.
    // A callback from a retired store is terminally cancelled before it can
    // acknowledge a replacement-generation command.
    if ready.identity.acquisition_id != state.acquisition_id
        || ready.identity.store_generation != state.node_store.store_generation()
    {
        ready.outcome = PersistenceOutcome::Cancelled;
    }
    let (timing, failed) = {
        let mut queue = state.persistence.lock().expect("persistence queue lock");
        let timing = queue.acknowledge(&ready);
        (timing, queue.failed.clone())
    };
    let Some(timing) = timing else {
        state.record_stale_event();
        return;
    };
    if ready.durability_barrier {
        let outcome = match &ready.outcome {
            PersistenceOutcome::Durable => "durable",
            PersistenceOutcome::Fault(_) => "fault",
            PersistenceOutcome::Cancelled => "cancelled",
        };
        let (ledger_hash, ledger_seq) = state
            .completed_ledger
            .lock()
            .expect("acquisition completed ledger lock")
            .as_ref()
            .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq))
            .unwrap_or((*state.hash.as_uint256(), state.seq()));
        tracing::debug!(
            target: "inbound_ledger",
            event = "durability_barrier_settled",
            target_hash = %state.hash,
            ledger_hash = %ledger_hash,
            ledger_seq,
            acquisition_id = ready.identity.acquisition_id,
            store_generation = ready.identity.store_generation,
            persistence_generation = ready.identity.persistence_generation,
            outcome,
            queue_elapsed_us = timing
                .dispatched_at
                .duration_since(timing.enqueued_at)
                .as_micros() as u64,
            total_elapsed_us = timing.enqueued_at.elapsed().as_micros() as u64,
            "inbound durability barrier settled"
        );
    }
    if let Some(error) = failed {
        tracing::error!(target: "inbound_ledger", seq = state.seq(), hash = %state.hash, %error,
            "acquisition persistence command failed");
        state.mark_failed();
        return;
    }
    state.dispatch_next_persistence_command();
    if ready.durability_barrier {
        finalize_durable_acquisition(state);
    }
}

fn process_local_probe(state: &Arc<AcquisitionState>, probe: LocalProbe, ready: ReadReady) {
    let ReadOutcome::Found(object) = ready.outcome else {
        // A miss/cancel/fault is an explicit completed local probe. It permits
        // the retained normal request policy to proceed; it is never progress.
        trigger(state, probe.reason, probe.peer);
        return;
    };
    let mut verified = false;
    let mut invalid_local_root = false;
    let writes = match probe.kind {
        LocalProbeKind::Header => {
            let Some(mut mutable) = state.lock_mutable("brokered local header") else {
                return;
            };
            let config = ledger::LedgerConfig::default();
            let AcqMutableState { inbound, store, .. } = &mut *mutable;
            verified = inbound.apply_brokered_header(
                object.data().to_vec(),
                &config,
                store,
                &WorkerJournal,
            );
            store.take_pending_writes()
        }
        LocalProbeKind::StateRoot | LocalProbeKind::TransactionRoot => {
            let hash = SHAMapHash::new(ready.ticket.key().hash);
            let Ok(node) = shamap::tree_node::SHAMapTreeNode::make_from_prefix(object.data(), hash)
            else {
                state.mark_failed();
                return;
            };
            let Ok(wire) = node.serialize_for_wire() else {
                state.mark_failed();
                return;
            };
            let packet_type = match probe.kind {
                LocalProbeKind::StateRoot => InboundLedgerDataType::StateNode,
                LocalProbeKind::TransactionRoot => InboundLedgerDataType::TransactionNode,
                LocalProbeKind::Header => unreachable!(),
            };
            let packet = InboundLedgerPacket::new(
                packet_type,
                vec![ledger::InboundLedgerNodeData::new(
                    Some(shamap::node_id::SHAMapNodeId::default().get_raw_string()),
                    wire,
                )],
            );
            let Some(mut mutable) = state.lock_mutable("brokered local root") else {
                return;
            };
            let journal = WorkerJournal;
            let config = ledger::LedgerConfig::default();
            let family = family(state);
            let AcqMutableState {
                inbound,
                store,
                fetch_pack,
            } = &mut *mutable;
            match inbound.process_packet_step_with_family_and_config(
                &packet,
                0,
                ledger::INBOUND_LEDGER_MAX_PACKET_NODES_PER_STEP,
                &journal,
                &config,
                store,
                fetch_pack,
                &family,
            ) {
                Ok(step) if !step.stats.is_invalid() => {
                    inbound.record_packet_stats_with_family_and_config(
                        step.stats, &journal, &config, &family,
                    );
                    verified = step.stats.is_useful();
                }
                Ok(_) | Err(_) => invalid_local_root = true,
            }
            store.take_pending_writes()
        }
    };
    state.submit_persistence_writes(writes);
    if probe.kind == LocalProbeKind::Header && verified {
        let canonical_seq = state
            .lock_mutable("brokered header sequence")
            .map(|mutable| mutable.inbound.seq())
            .unwrap_or_default();
        state.sync_header_sequence(canonical_seq);
        state.stats.mark_header_received();
    }
    if invalid_local_root {
        state.mark_failed();
        return;
    }
    if verified {
        if let Some(mut mutable) = state.lock_mutable("verified local probe progress") {
            mutable.inbound.record_verified_progress();
        }
    }
    if state.is_done() {
        finalize_terminal(state);
    } else {
        trigger(state, probe.reason, probe.peer);
    }
}

/// Reduce settled broker completions into the same retained traversal pass.
/// A contested scheduler yields only between completed atomic reductions; an
/// idle scheduler drains all currently-ready work without an eight-event cap.
fn process_read_events(state: &Arc<AcquisitionState>, budget: &TurnBudget) {
    while !budget.must_yield_after_atomic_unit() && process_one_read_event(state) {}
}

/// Reduce one settled completion. Returning false leaves the mailbox untouched;
/// returning true means precisely one reservation was released and its event
/// was handled, including stale and terminal paths.
fn process_one_read_event(state: &Arc<AcquisitionState>) -> bool {
    if state.is_done() {
        return false;
    }
    let Some(ready) = state.take_read_event() else {
        return false;
    };
    if ready.ticket.acquisition_id() != state.acquisition_id {
        state.record_stale_event();
        return true;
    }
    // Agent 1's typed work is admitted with this exact store generation.
    // Never let a late callback from a retired NodeStore generation mutate an
    // acquisition that may now be represented by replacement work.
    if ready.ticket.key().database_generation != state.node_store.store_generation() {
        state.record_stale_event();
        // The old broker work has already released Agent 1's typed permit;
        // terminally clear this actor's ticket/plan ownership rather than
        // retaining a stale edge that could route after replacement.
        state.mark_failed();
        return true;
    }
    if let Some(probe) = state.take_local_probe(&ready) {
        process_local_probe(state, probe, ready);
        return true;
    }
    let Some(mut actor_plan) = state.take_tree_plan() else {
        state.record_stale_event();
        return true;
    };
    if ready.ticket.acquisition_id() != state.acquisition_id
        || actor_plan.plan.id().get() != ready.ticket.plan_id()
    {
        state.record_stale_event();
        state.restore_tree_plan(actor_plan);
        return true;
    }
    let hash = SHAMapHash::new(ready.ticket.key().hash);
    actor_plan.tickets.remove(&hash);
    let apply = match ready.outcome {
        ReadOutcome::Found(object) => {
            let node =
                match shamap::tree_node::SHAMapTreeNode::make_from_prefix(object.data(), hash) {
                    Ok(node) => node,
                    Err(_) => {
                        fail_actor_plan(state, actor_plan);
                        return true;
                    }
                };
            actor_plan.plan.apply_read_result(
                TreePlanId::new(ready.ticket.plan_id()),
                hash,
                MissingNodeReadOutcome::Found(node),
            )
        }
        ReadOutcome::Miss => actor_plan.plan.apply_read_result(
            TreePlanId::new(ready.ticket.plan_id()),
            hash,
            MissingNodeReadOutcome::Miss,
        ),
        ReadOutcome::Cancelled => actor_plan.plan.apply_read_result(
            TreePlanId::new(ready.ticket.plan_id()),
            hash,
            MissingNodeReadOutcome::Cancelled,
        ),
        ReadOutcome::Fault(_) => {
            fail_actor_plan(state, actor_plan);
            return true;
        }
    };
    match apply {
        MissingNodeReadApply::HashMismatch => fail_actor_plan(state, actor_plan),
        MissingNodeReadApply::Applied { attached_edges, .. } => {
            if attached_edges != 0 {
                if let Some(mut mutable) = state.lock_mutable("verified broker read progress") {
                    mutable.inbound.record_verified_progress();
                }
            }
            actor_plan.runnable = !actor_plan.read_admission_backlog.is_empty()
                || actor_plan.plan.has_runnable_frontier();
            state.restore_tree_plan(actor_plan);
        }
        MissingNodeReadApply::Requeued => {
            actor_plan.runnable = !actor_plan.read_admission_backlog.is_empty();
            state.restore_tree_plan(actor_plan);
        }
        MissingNodeReadApply::Cancelled => fail_actor_plan(state, actor_plan),
        MissingNodeReadApply::StalePlan | MissingNodeReadApply::UnknownRead => {
            // A deferred local hit may arrive after the peer already supplied
            // the same candidate. The retained plan is authoritative; this is
            // harmless late local data rather than an acquisition failure.
            state.record_stale_event();
            state.restore_tree_plan(actor_plan);
        }
    }
    true
}

/// Build one bounded normal or aggressive request from a retained verified
/// network frontier. The caller restores the detached plan before sending.
fn take_tree_network_request(
    state: &AcquisitionState,
    actor_plan: &mut ActorTreePlan,
    candidates: Vec<(shamap::node_id::SHAMapNodeId, Uint256)>,
) -> (Option<OwnedOutboundRequest>, bool) {
    let limit = match actor_plan.reason {
        InboundLedgerRequestTrigger::Reply | InboundLedgerRequestTrigger::ReplyHighLatency => 128,
        _ => 12,
    };
    let candidates = select_tree_network_candidates(&mut actor_plan.plan, candidates, limit);
    if candidates.is_empty() {
        return (None, false);
    }
    if actor_plan.reason == InboundLedgerRequestTrigger::Timeout && actor_plan.aggressive_by_hash {
        let object_type = match actor_plan.plan.kind() {
            TreeKind::State => InboundLedgerObjectType::StateNode,
            TreeKind::Transaction => InboundLedgerObjectType::TransactionNode,
        };
        let needed = candidates
            .iter()
            .map(|(_, hash)| (object_type, *hash))
            .collect::<Vec<_>>();
        let outbound =
            make_inbound_needed_by_hash_request(state.hash, state.seq(), &needed).map(|message| {
                actor_plan.aggressive_by_hash = false;
                OwnedOutboundRequest {
                    message,
                    target: None,
                }
            });
        let consumed = outbound.is_some();
        return (outbound, consumed);
    }

    let ids = candidates.iter().map(|(id, _)| *id).collect::<Vec<_>>();
    let depth = match actor_plan.reason {
        InboundLedgerRequestTrigger::Reply => 1,
        InboundLedgerRequestTrigger::ReplyHighLatency => 2,
        _ => 0,
    };
    let itype = match actor_plan.plan.kind() {
        TreeKind::State => 2,
        TreeKind::Transaction => 1,
    };
    let message = make_get_ledger_with_node_ids(
        state.hash,
        state.seq(),
        itype,
        &ids,
        depth,
        (actor_plan.reason == InboundLedgerRequestTrigger::Timeout).then_some(0),
    );
    let target = (actor_plan.reason != InboundLedgerRequestTrigger::Timeout)
        .then(|| actor_plan.peer.clone())
        .flatten();
    (Some(OwnedOutboundRequest { message, target }), false)
}

/// Admit retained TreePlan reads while there is mailbox completion capacity.
///
/// `TreePlan::advance` removes emitted needs from its unannounced set. When
/// admission is full, ownership moves to `read_admission_backlog`; those needs
/// are not converted back to `Rejected`, so the next completion retries this
/// FIFO directly and cannot create a zero-branch TreePlan turn.
fn submit_read_admission_backlog(state: &Arc<AcquisitionState>, mut actor_plan: ActorTreePlan) {
    let plan_id = actor_plan.plan.id();
    while let Some(need) = actor_plan.read_admission_backlog.pop_front() {
        let store_generation = state.node_store.store_generation();
        let key = ReadKey::new(
            *need.hash().as_uint256(),
            need.ledger_seq(),
            store_generation,
        );
        let weak = Arc::downgrade(state);
        let sink: ReadReadySink = Arc::new(move |ready| {
            if let Some(state) = weak.upgrade() {
                state.enqueue_read_ready(ready);
            }
        });
        match state
            .read_broker
            .request(key, state.acquisition_id, plan_id.get(), sink)
        {
            ReadAdmission::Accepted(ticket) => {
                state
                    .stats
                    .state_scan_read_admission_accepted
                    .fetch_add(1, Ordering::Relaxed);
                actor_plan.tickets.insert(need.hash(), ticket);
            }
            ReadAdmission::Deferred(ticket) => {
                state
                    .stats
                    .state_scan_read_admission_deferred
                    .fetch_add(1, Ordering::Relaxed);
                actor_plan.tickets.insert(need.hash(), ticket);
            }
            ReadAdmission::CapacityDeferred => {
                // Broker pressure is not a NodeStore miss. Rippled waits for
                // all locally deferred reads before exposing missing nodes, so
                // retain this edge for timeout-driven retry without creating a
                // synthetic peer request.
                actor_plan.read_admission_backlog.push_front(need);
                state
                    .stats
                    .state_scan_read_admission_deferred
                    .fetch_add(1, Ordering::Relaxed);
                break;
            }
            ReadAdmission::Attached(ticket) => {
                state
                    .stats
                    .state_scan_read_admission_attached
                    .fetch_add(1, Ordering::Relaxed);
                actor_plan.tickets.insert(need.hash(), ticket);
            }
            ReadAdmission::Rejected(ReadRejectReason::Stopped) => {
                fail_actor_plan(state, actor_plan);
                return;
            }
        }
    }
    actor_plan.runnable =
        !actor_plan.awaiting_local_read_batch() && actor_plan.plan.has_runnable_frontier();
    state.restore_tree_plan(actor_plan);
    state
        .read_broker
        .submit_ready_to_node_store(&state.node_store);
}

fn process_tree_plan_turn(state: &Arc<AcquisitionState>, budget: &TurnBudget) {
    let Some(mut actor_plan) = state.take_tree_plan() else {
        return;
    };
    if !actor_plan.read_admission_backlog.is_empty() {
        submit_read_admission_backlog(state, actor_plan);
        return;
    }
    if actor_plan.awaiting_local_read_batch() {
        actor_plan.runnable = false;
        state.restore_tree_plan(actor_plan);
        return;
    }
    let retained_reads = actor_plan
        .plan
        .take_read_admission_batch(ACQ_DEFERRED_READS_PER_PASS);
    if !retained_reads.is_empty() {
        actor_plan.read_admission_backlog.extend(retained_reads);
        submit_read_admission_backlog(state, actor_plan);
        return;
    }
    let started = Instant::now();
    let scan_before = actor_plan.plan.scan_stats();
    let branch_steps_before = scan_before.branch_steps;
    let mut resident = ActorResident {
        cache: &state.shared_tree_cache,
        full_below: state.shared_full_below.as_ref(),
    };
    let advance = actor_plan.plan.advance_with_yield(
        ACQ_DEFERRED_READS_PER_PASS,
        &mut resident,
        &mut || basics::random::rand_int_to(255u8),
        &mut || budget.must_yield_after_atomic_unit(),
    );
    let scan_after = actor_plan.plan.scan_stats();
    let branch_steps_after = scan_after.branch_steps;
    let branch_steps_delta = branch_steps_after.saturating_sub(branch_steps_before);
    let deferred_reads_delta = scan_after
        .pending_reads
        .saturating_sub(scan_before.pending_reads);
    let deferred_resumes_delta = scan_after
        .deferred_resumes
        .saturating_sub(scan_before.deferred_resumes);
    let missing_nodes_delta = scan_after
        .missing_recorded
        .saturating_sub(scan_before.missing_recorded);
    let outcome = match &advance {
        TreeAdvance::Ready => SCAN_OUTCOME_READY,
        TreeAdvance::NeedsReads(_) => SCAN_OUTCOME_NEEDS_READS,
        TreeAdvance::NeedsNetwork(_) => SCAN_OUTCOME_NEEDS_NETWORK,
        TreeAdvance::Complete => SCAN_OUTCOME_COMPLETE,
        TreeAdvance::Invalid => SCAN_OUTCOME_INVALID,
    };
    state.stats.state_scan_runs.fetch_add(1, Ordering::Relaxed);
    state
        .stats
        .state_scan_last_outcome
        .store(outcome, Ordering::Relaxed);
    state
        .stats
        .state_scan_branch_steps
        .fetch_add(branch_steps_delta, Ordering::Relaxed);
    state
        .stats
        .state_scan_missing_nodes_recorded
        .fetch_add(missing_nodes_delta, Ordering::Relaxed);
    state
        .stats
        .state_missing_nodes
        .fetch_add(missing_nodes_delta, Ordering::Relaxed);
    state.stats.state_scan_branches_seen.fetch_add(
        scan_after
            .branches_seen
            .saturating_sub(scan_before.branches_seen),
        Ordering::Relaxed,
    );
    state.stats.state_scan_duplicate_missing_hashes.fetch_add(
        scan_after
            .duplicate_missing_hashes
            .saturating_sub(scan_before.duplicate_missing_hashes),
        Ordering::Relaxed,
    );
    state.stats.state_scan_full_below_hits.fetch_add(
        scan_after
            .full_below_hits
            .saturating_sub(scan_before.full_below_hits),
        Ordering::Relaxed,
    );
    state.stats.state_scan_loaded_or_cached_children.fetch_add(
        scan_after
            .loaded_or_cached_children
            .saturating_sub(scan_before.loaded_or_cached_children),
        Ordering::Relaxed,
    );
    state.stats.state_scan_pending_hits.fetch_add(
        scan_after
            .completed_pending_reads
            .saturating_sub(scan_before.completed_pending_reads),
        Ordering::Relaxed,
    );
    state.stats.state_scan_pending_misses.fetch_add(
        scan_after
            .completed_pending_misses
            .saturating_sub(scan_before.completed_pending_misses),
        Ordering::Relaxed,
    );
    state
        .stats
        .state_scan_deferred_resumes
        .fetch_add(deferred_resumes_delta, Ordering::Relaxed);
    state
        .stats
        .state_scan_max_pending_reads
        .fetch_max(scan_after.max_pending_reads, Ordering::Relaxed);
    state
        .stats
        .state_scan_pending_reads
        .store(actor_plan.plan.pending_hashes() as u64, Ordering::Relaxed);
    state
        .stats
        .state_scan_last_branch_steps
        .store(branch_steps_delta, Ordering::Relaxed);
    state
        .stats
        .state_scan_last_deferred_reads
        .store(deferred_reads_delta, Ordering::Relaxed);
    state
        .stats
        .state_scan_last_deferred_resumes
        .store(deferred_resumes_delta, Ordering::Relaxed);
    state
        .stats
        .state_scan_last_missing_nodes
        .store(missing_nodes_delta, Ordering::Relaxed);
    if branch_steps_delta != 0 {
        state
            .stats
            .state_scan_positive_progress_slices
            .fetch_add(1, Ordering::Relaxed);
    }
    match &advance {
        TreeAdvance::Ready | TreeAdvance::NeedsReads(_) | TreeAdvance::NeedsNetwork(_) => {
            state
                .stats
                .state_scan_yields
                .fetch_add(1, Ordering::Relaxed);
        }
        TreeAdvance::Complete => {
            state
                .stats
                .state_scan_completed_slices
                .fetch_add(1, Ordering::Relaxed);
        }
        TreeAdvance::Invalid => {}
    }
    if outcome == SCAN_OUTCOME_READY && budget.must_yield_after_atomic_unit() {
        state
            .stats
            .state_scan_branch_budget_yields
            .fetch_add(1, Ordering::Relaxed);
    }
    if outcome == SCAN_OUTCOME_NEEDS_READS
        && deferred_reads_delta == ACQ_DEFERRED_READS_PER_PASS as u64
    {
        state
            .stats
            .state_scan_deferred_read_budget_yields
            .fetch_add(1, Ordering::Relaxed);
    }
    if deferred_resumes_delta != 0 && outcome == SCAN_OUTCOME_READY {
        state
            .stats
            .state_scan_deferred_read_resume_yields
            .fetch_add(1, Ordering::Relaxed);
    }
    state
        .stats
        .state_scan_us
        .fetch_add(started.elapsed().as_micros() as u64, Ordering::Relaxed);
    match advance {
        TreeAdvance::Invalid => fail_actor_plan(state, actor_plan),
        TreeAdvance::Complete => {
            state
                .lifecycle
                .tree_plans_completed
                .fetch_add(1, Ordering::Relaxed);
            let kind = actor_plan.plan.kind();
            let terminal = state
                .lock_mutable("complete tree plan")
                .is_some_and(|mut mutable| {
                    mutable.inbound.complete_tree_plan(kind);
                    mutable.inbound.is_failed() || mutable.inbound.is_complete()
                });
            if terminal {
                finalize_terminal(state);
            } else {
                trigger(state, actor_plan.reason, actor_plan.peer);
            }
        }
        TreeAdvance::NeedsReads(reads) => {
            actor_plan.read_admission_backlog.extend(reads);
            submit_read_admission_backlog(state, actor_plan);
        }
        TreeAdvance::NeedsNetwork(candidates) => {
            let (outbound, consume_aggressive_by_hash) =
                take_tree_network_request(state, &mut actor_plan, candidates);
            if consume_aggressive_by_hash {
                if let Some(mut mutable) = state.lock_mutable("consume aggressive by-hash request")
                {
                    mutable.inbound.set_by_hash(false);
                }
            }
            actor_plan.runnable = actor_plan.plan.has_runnable_frontier();
            state.restore_tree_plan_before_peer_send(actor_plan, || {
                if let Some(outbound) = outbound {
                    let _ = send_owned_outbound_request(state, outbound);
                }
            });
        }
        TreeAdvance::Ready => {
            actor_plan.runnable = ready_turn_can_requeue(&actor_plan.plan, branch_steps_before);
            state.restore_tree_plan(actor_plan);
        }
    }
}

fn charge_malformed_packet(
    state: &AcquisitionState,
    peer_id: u64,
    packet_type: ledger::InboundLedgerDataType,
    error: InboundLedgerPacketError,
) {
    let Some(peer) = state.peer_set.find_peer(peer_id as u32) else {
        return;
    };
    let context = match (packet_type, error) {
        (ledger::InboundLedgerDataType::Base, InboundLedgerPacketError::EmptyNodes) => {
            "ledger_data empty header"
        }
        (_, InboundLedgerPacketError::EmptyNodes) => "ledger_data no nodes",
        (_, InboundLedgerPacketError::EmptyNodeData) => "ledger_data empty node",
        (_, InboundLedgerPacketError::InvalidHeader) => "ledger_data invalid header",
        (_, InboundLedgerPacketError::MissingNodeId) => "ledger_data missing node id",
        (_, InboundLedgerPacketError::InvalidNodeId) => "ledger_data invalid node id",
        (_, InboundLedgerPacketError::InvalidNodeData) => "ledger_data malformed node data",
        (_, InboundLedgerPacketError::InvalidData) => "ledger_data invalid data",
    };
    peer.charge(
        (*resource::FEE_MALFORMED_REQUEST).clone(),
        context.to_owned(),
    );
}

fn charge_invalid_data_packet(
    state: &AcquisitionState,
    peer_id: u64,
    packet_type: ledger::InboundLedgerDataType,
    error: InboundLedgerPacketError,
) {
    let Some(peer) = state.peer_set.find_peer(peer_id as u32) else {
        return;
    };
    let context = match (packet_type, error) {
        (ledger::InboundLedgerDataType::Base, _) => "ledger_data invalid root",
        (_, InboundLedgerPacketError::InvalidData) => "ledger_data invalid node",
        (_, _) => "ledger_data invalid data",
    };
    peer.charge((*resource::FEE_INVALID_DATA).clone(), context.to_owned());
}

fn process_timeout_job(state: &Arc<AcquisitionState>) {
    if state.is_done() {
        return;
    }
    // This function runs only after `take_admitted_timeout` consumes one
    // mailbox event. The one acquisition token makes the mutable planner safe
    // without a scan-active discard/re-arm branch.
    state
        .stats
        .timeout_dispatches
        .fetch_add(1, Ordering::Relaxed);
    if state.stats.should_emit_sampled_diagnostic() {
        tracing::debug!(
            target: "inbound_ledger",
            seq = state.seq(),
            hash = %state.hash,
            timeout_dispatches = state.stats.timeout_dispatches.load(Ordering::Relaxed),
            "sampled admitted timeout dispatched from acquisition mailbox"
        );
    }
    state.lifecycle.timeout_jobs.fetch_add(1, Ordering::Relaxed);

    let mut retry = false;
    let mut finalize = false;
    let mut failed = false;
    let persistence_writes;
    let canonical_seq;
    {
        let Some(mut mutable) = state.lock_mutable("timeout") else {
            return;
        };
        match mutable.inbound.timeout_expired() {
            InboundLedgerTimerResult::Progress => {}
            InboundLedgerTimerResult::Done => finalize = true,
            InboundLedgerTimerResult::Failed => failed = true,
            InboundLedgerTimerResult::NoProgress => {
                state
                    .lifecycle
                    .timeout_no_progress
                    .fetch_add(1, Ordering::Relaxed);
                check_local(state, &mut mutable);
                if mutable.inbound.is_failed() {
                    failed = true;
                } else if mutable.inbound.is_complete() {
                    finalize = true;
                } else {
                    mutable.inbound.set_by_hash(true);
                    retry = true;
                    state
                        .lifecycle
                        .timeout_retries
                        .fetch_add(1, Ordering::Relaxed);
                }
            }
        }
        persistence_writes = mutable.store.take_pending_writes();
        canonical_seq = mutable.inbound.seq();
    }

    state.sync_header_sequence(canonical_seq);
    state.submit_persistence_writes(persistence_writes);
    if failed || finalize {
        finalize_terminal(state);
        return;
    }
    // Timeout recovery mutates planner state before it fans out requests. A
    // concurrent registry terminal transition must stop that follow-up; the
    // running turn will perform mailbox cleanup.
    if state.is_done() {
        return;
    }
    if retry {
        state
            .mailbox
            .lock()
            .expect("acquisition mailbox lock")
            .completed_local_probes
            .clear();
        // Match InboundLedger::onTimer exactly: for non-history work the
        // tracked peers receive Timeout before new peers receive Added; for
        // history work addPeers does not trigger Added, then Timeout fans out.
        if state.reason != AcquireReason::History {
            trigger(state, InboundLedgerRequestTrigger::Timeout, None);
            for peer in add_peers(state) {
                trigger(state, InboundLedgerRequestTrigger::Added, Some(peer));
            }
        } else {
            let _ = add_peers(state);
            trigger(state, InboundLedgerRequestTrigger::Timeout, None);
        }
    }
    state.arm_timer();
}

/// Finalize the terminal planner state after its mutable acquisition lock has
/// been released. Failure deliberately wins if both flags are visible, as in
/// rippled's `done()` completion predicate (`complete_ && !failed_`). Both
/// finalizers are idempotent: `mark_failed` records once and
/// `record_completed_ledger` publishes once.
fn finalize_terminal(state: &Arc<AcquisitionState>) {
    let Some(mutable) = state.lock_mutable("terminal finalization") else {
        return;
    };

    let (failed, complete) = (mutable.inbound.is_failed(), mutable.inbound.is_complete());
    drop(mutable);

    if failed {
        state.mark_failed();
    } else if complete {
        finalize_acquisition(state);
    }
}

fn record_resolver_visible_ledger(
    acquisition_id: u64,
    resolver_published: &AtomicBool,
    completed_ledger: &Mutex<Option<Arc<Ledger>>>,
    store_tx: &std::sync::mpsc::SyncSender<CompletedInboundLedger>,
    reason: AcquireReason,
    ledger: Arc<Ledger>,
) -> bool {
    // Record first: the registry polling path is the authoritative recovery
    // path when its notification receiver is disconnected or late. Holding
    // this lock closes the publication=true/cache-empty window for concurrent
    // acquire/poll callers.
    let mut cached = completed_ledger
        .lock()
        .expect("acquisition completed ledger lock");
    if resolver_published.swap(true, Ordering::AcqRel) {
        return false;
    }
    *cached = Some(Arc::clone(&ledger));
    drop(cached);

    // This channel only wakes a consumer; registry publication retains the
    // completed result independently of durable NodeStore acknowledgement.
    let _ = store_tx.try_send(CompletedInboundLedger {
        ledger,
        reason,
        acquisition_id,
        from_coordinator: false,
        durable_handoff: None,
        coordinator_session: None,
    });
    true
}

fn publish_resolver_visible_ledger(
    identity: ProvisionalLedgerIdentity,
    completion_recorder: &AcquisitionCompletionRecorder,
    resolver_published: &AtomicBool,
    completed_ledger: &Mutex<Option<Arc<Ledger>>>,
    store_tx: &std::sync::mpsc::SyncSender<CompletedInboundLedger>,
    reason: AcquireReason,
    ledger: Arc<Ledger>,
) -> bool {
    // Establish the registry identity only after the acquisition durability
    // fence. The queued strand work then performs validation registration and
    // acceptance, just as rippled's separately dispatched AcqDone job does.
    if !completion_recorder(identity, Arc::clone(&ledger)) {
        return false;
    }
    record_resolver_visible_ledger(
        identity.acquisition_id,
        resolver_published,
        completed_ledger,
        store_tx,
        reason,
        ledger,
    )
}

/// Snapshot the completed ledger while the acquisition is frozen, then release
/// actor ownership before immutable-ledger setup can invoke its node fetcher.
fn snapshot_completed_ledger(state: &AcquisitionState) -> Option<Ledger> {
    let mutable = state.lock_mutable("snapshot completed ledger")?;
    if mutable.inbound.is_failed() || !mutable.inbound.is_complete() {
        return None;
    }
    mutable.inbound.ledger().cloned()
}

/// Build the immutable acquired ledger with the same cache-then-NodeStore
/// read-through ownership that rippled's SHAMap family provides. A completed
/// ledger can outlive individual TreeNodeCache entries, so a cache-only
/// fetcher would turn an evicted branch into an apparent absent ledger object.
fn build_resolver_visible_ledger(state: &AcquisitionState) -> Option<Arc<Ledger>> {
    let mut ledger = snapshot_completed_ledger(state)?;
    if !ledger.is_immutable() {
        ledger.set_immutable(true);
    }
    ledger.set_full();
    let tree_cache = Arc::clone(&state.shared_tree_cache);
    let node_store = state.node_store.clone();
    let ledger_seq = ledger.header().seq;
    ledger.set_node_fetcher(Arc::new(move |hash| {
        if let Some(node) = tree_cache.fetch(hash.as_uint256()) {
            return Some(node);
        }
        let object = match &node_store {
            SHAMapStoreNodeStore::Single(database) => database.fetch_node_object(
                hash.as_uint256(),
                ledger_seq,
                nodestore::FetchType::Synchronous,
                false,
            ),
            SHAMapStoreNodeStore::Rotating(database) => database.fetch_node_object(
                hash.as_uint256(),
                ledger_seq,
                nodestore::FetchType::Synchronous,
                false,
            ),
        }?;
        let mut node =
            shamap::tree_node::SHAMapTreeNode::make_from_prefix(object.data(), hash).ok()?;
        tree_cache.canonicalize_replace_client(hash.as_uint256(), &mut node);
        Some(node)
    }));
    Some(Arc::new(ledger))
}

fn finalize_acquisition(state: &Arc<AcquisitionState>) {
    let began_terminal_drain = {
        let _outbound = state
            .outbound_gate
            .lock()
            .expect("acquisition outbound gate lock");
        !state.is_done()
            && state
                .draining
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
    };
    if !began_terminal_drain {
        return;
    }
    let terminal = state
        .lock_mutable("begin terminal drain")
        .is_some_and(|mutable| mutable.inbound.is_complete() && !mutable.inbound.is_failed());
    if !terminal {
        state.draining.store(false, Ordering::Release);
        state.mark_failed();
        return;
    }

    if state
        .resolver_publication_claimed
        .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
        .is_err()
    {
        state.mark_failed();
        return;
    }
    let Some(ledger) = build_resolver_visible_ledger(state) else {
        state.mark_failed();
        return;
    };
    let ledger_seq = ledger.header().seq;
    let ledger_hash = *ledger.header().hash.as_uint256();
    if state
        .enqueue_durability_barrier(ledger_hash, ledger_seq)
        .is_none()
    {
        state.mark_failed();
        return;
    };
    *state
        .completed_ledger
        .lock()
        .expect("acquisition completed ledger lock") = Some(ledger);
    tracing::info!(
        target: "lcl_trace",
        event = "inbound_waiting_for_durability",
        target_hash = %state.hash,
        ledger_hash = %ledger_hash,
        target_matches_header = *state.hash.as_uint256() == ledger_hash,
        ledger_seq,
        acquisition_id = state.acquisition_id,
        reason = ?state.reason,
        "LCL trace: completed inbound ledger held until NodeStore durability fence"
    );

    // rippled does not expose an acquired ledger until its accepted nodes are
    // owned by NodeStore. The Rust write port is asynchronous, so the FIFO
    // fence is the equivalent ownership boundary.
    state.dispatch_next_persistence_command();
}

fn finalize_durable_acquisition(state: &Arc<AcquisitionState>) {
    if state.is_done()
        || state
            .finalization_claimed
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
    {
        return;
    }
    let Some(ledger) = state
        .completed_ledger
        .lock()
        .expect("acquisition completed ledger lock")
        .clone()
    else {
        state.mark_failed();
        return;
    };

    let Some(provisional_identity) = state
        .persistence
        .lock()
        .expect("persistence queue lock")
        .provisional_identity(
            *state.hash.as_uint256(),
            *ledger.header().hash.as_uint256(),
            ledger.header().seq,
        )
    else {
        state.mark_failed();
        return;
    };

    state.provisional_registered.store(true, Ordering::Release);
    if !publish_resolver_visible_ledger(
        provisional_identity,
        &state.completion_recorder,
        &state.resolver_published,
        &state.completed_ledger,
        &state.store_tx,
        state.reason,
        Arc::clone(&ledger),
    ) {
        state.mark_failed();
        return;
    }

    {
        let _outbound = state
            .outbound_gate
            .lock()
            .expect("acquisition outbound gate lock");
        if state.is_done() {
            return;
        }
        state.completed.store(true, Ordering::Release);
    }
    (state.durable_completion_recorder)(provisional_identity);
    state
        .lifecycle
        .terminal_completed
        .fetch_add(1, Ordering::Relaxed);
    tracing::info!(
        target: "lcl_trace",
        event = "inbound_durable_complete",
        target_hash = %state.hash,
        ledger_hash = %ledger.header().hash,
        target_matches_header = state.hash == ledger.header().hash,
        ledger_seq = ledger.header().seq,
        acquisition_id = state.acquisition_id,
        store_generation = provisional_identity.store_generation,
        persistence_generation = provisional_identity.persistence_generation,
        reason = ?state.reason,
        "LCL trace: inbound acquisition durability barrier acknowledged"
    );
    tracing::info!(
        target: "inbound_ledger",
        seq = ledger.header().seq,
        hash = %ledger.header().hash,
        acquisition_id = state.acquisition_id,
        reason = ?state.reason,
        "LEDGER ACQUIRED"
    );
}
/// Stash state nodes from an unroutable response in the fetch pack, matching
/// `InboundLedgersImp::gotStaleData`.
pub fn stash_stale_packet<FP>(packet: &InboundLedgerPacket, stale_data_store: &mut FP) -> bool
where
    FP: FetchPackStore,
{
    for node in &packet.nodes {
        if node.node_id.is_none() {
            return false;
        }
        let Ok(Some(decoded)) =
            shamap::nodes::tree_node::SHAMapTreeNode::make_from_wire(&node.node_data)
        else {
            return false;
        };
        let Ok(prefixed) = decoded.serialize_with_prefix() else {
            return false;
        };
        stale_data_store.add_fetch_pack(*decoded.get_hash().as_uint256(), prefixed);
    }
    true
}

#[cfg(test)]
mod actor_mailbox_tests {
    use super::*;

    fn packet_work(peer_id: u64, bytes: usize) -> PacketWork {
        PacketWork {
            peer_id,
            packet: InboundLedgerPacket::new(
                InboundLedgerDataType::StateNode,
                vec![ledger::InboundLedgerNodeData::new(
                    Some(vec![0; 33]),
                    vec![0; bytes],
                )],
            ),
            bytes,
            enqueued_at: Instant::now(),
        }
    }

    #[test]
    fn retained_tree_read_batches_drain_without_another_branch_scan() {
        use shamap::sync::{SHAMapType, SyncState, SyncTree};
        use shamap::tree_node::SHAMapTreeNode;

        struct NoResident;
        impl MissingNodeResidentLookup for NoResident {
            fn load_resident(
                &mut self,
                _hash: SHAMapHash,
                _ledger_seq: u32,
            ) -> Option<basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>> {
                None
            }
        }

        // A two-level inner tree has far more distinct missing leaves than the
        // 16-read actor admission batch. One bounded advance retains later
        // batches internally after returning the first batch.
        let root = SHAMapTreeNode::new_inner(1);
        for parent_branch in 0..16 {
            let child = SHAMapTreeNode::new_inner(1);
            for child_branch in 0..16 {
                let byte = (parent_branch * 16 + child_branch + 1) as u8;
                child.set_child_hash(
                    child_branch,
                    SHAMapHash::new(Uint256::from_array([byte; 32])),
                );
            }
            child.update_hash();
            root.set_child_hash(parent_branch, child.get_hash());
            root.canonicalize_child(parent_branch, child);
        }
        root.update_hash();
        let tree = SyncTree::from_root_with_type(
            root.clone(),
            SHAMapType::State,
            true,
            77,
            SyncState::Synching,
        );
        let mut first_child = || 0;
        let mut plan = TreePlan::new(
            TreePlanId::new(95),
            TreeKind::State,
            &tree,
            root.get_hash(),
            256,
            9,
            &mut first_child,
        );
        let mut resident = NoResident;
        let TreeAdvance::NeedsReads(initial_reads) =
            plan.advance(256, 16, &mut resident, &mut first_child)
        else {
            panic!("expected the first bounded local-read batch");
        };
        assert_eq!(initial_reads.len(), 16);
        let branch_steps_before = plan.branch_steps();
        let retained_reads = plan.take_read_admission_batch(16);
        assert_eq!(retained_reads.len(), 16);
        assert_eq!(
            plan.branch_steps(),
            branch_steps_before,
            "extracting a retained batch must not run another TreePlan scan"
        );
    }

    #[test]
    fn deferred_ticket_with_runnable_frontier_parks_until_read_ready() {
        use super::super::read_broker::ReadBrokerConfig;
        use shamap::sync::{SHAMapType, SyncState, SyncTree};
        use shamap::tree_node::SHAMapTreeNode;

        struct NoResident;
        impl MissingNodeResidentLookup for NoResident {
            fn load_resident(
                &mut self,
                _hash: SHAMapHash,
                _ledger_seq: u32,
            ) -> Option<basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>> {
                None
            }
        }

        // A two-level, 256-leaf tree has more missing children than one
        // bounded read batch, leaving retained CPU frontier after the first
        // `NeedsReads` result.
        let root = SHAMapTreeNode::new_inner(1);
        for parent_branch in 0..16 {
            let child = SHAMapTreeNode::new_inner(1);
            for child_branch in 0..16 {
                let byte = (parent_branch * 16 + child_branch + 1) as u8;
                child.set_child_hash(
                    child_branch,
                    SHAMapHash::new(Uint256::from_array([byte; 32])),
                );
            }
            child.update_hash();
            root.set_child_hash(parent_branch, child.get_hash());
            root.canonicalize_child(parent_branch, child);
        }
        root.update_hash();
        let tree = SyncTree::from_root_with_type(
            root.clone(),
            SHAMapType::State,
            true,
            77,
            SyncState::Synching,
        );
        let mut first_child = || 0;
        let mut plan = TreePlan::new(
            TreePlanId::new(96),
            TreeKind::State,
            &tree,
            root.get_hash(),
            256,
            9,
            &mut first_child,
        );
        let mut resident = NoResident;
        let TreeAdvance::NeedsReads(reads) = plan.advance(256, 16, &mut resident, &mut first_child)
        else {
            panic!("expected bounded local-read needs");
        };
        assert_eq!(reads.len(), 16);
        assert!(
            plan.has_runnable_frontier(),
            "remaining branches keep the TreePlan frontier runnable"
        );

        let broker = NodeReadBroker::new(ReadBrokerConfig {
            global_in_flight: 1,
            ..ReadBrokerConfig::default()
        })
        .expect("valid broker config");
        let delivered = Arc::new(Mutex::new(Vec::<ReadReady>::new()));
        let sink: ReadReadySink = {
            let delivered = Arc::clone(&delivered);
            Arc::new(move |ready| delivered.lock().expect("read events lock").push(ready))
        };
        let first = &reads[0];
        let second = &reads[1];
        assert!(matches!(
            broker.request(
                ReadKey::new(*first.hash().as_uint256(), first.ledger_seq(), 0),
                41,
                plan.id().get(),
                Arc::clone(&sink),
            ),
            ReadAdmission::Accepted(_)
        ));
        assert!(matches!(
            broker.request(
                ReadKey::new(*second.hash().as_uint256(), second.ledger_seq(), 0),
                41,
                plan.id().get(),
                sink,
            ),
            ReadAdmission::Deferred(_)
        ));
        assert!(
            delivered.lock().expect("read events lock").is_empty(),
            "a Deferred ticket has not delivered ReadReady"
        );
        assert_eq!(broker.take_ready_dispatches().len(), 1);
    }

    #[test]
    fn read_admission_backpressure_waits_instead_of_spinning_zero_branch_needs_reads() {
        use shamap::sync::{SHAMapType, SyncState, SyncTree};
        use shamap::tree_node::SHAMapTreeNode;

        struct NoResident;
        impl MissingNodeResidentLookup for NoResident {
            fn load_resident(
                &mut self,
                _hash: SHAMapHash,
                _ledger_seq: u32,
            ) -> Option<basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>> {
                None
            }
        }

        // One inner root produces exactly 16 local-read needs. Simulating
        // admission rejection reannounces those same needs. Its stack is then
        // exhausted, so a retry returns `NeedsReads` with zero branch work:
        // this matches the live high-rate telemetry shape.
        let root = SHAMapTreeNode::new_inner(1);
        for branch in 0..16 {
            root.set_child_hash(
                branch,
                SHAMapHash::new(Uint256::from_array([(branch + 1) as u8; 32])),
            );
        }
        root.update_hash();
        let tree = SyncTree::from_root_with_type(
            root.clone(),
            SHAMapType::State,
            true,
            77,
            SyncState::Synching,
        );
        let mut first_child = || 0;
        let mut plan = TreePlan::new(
            TreePlanId::new(94),
            TreeKind::State,
            &tree,
            root.get_hash(),
            16,
            9,
            &mut first_child,
        );
        let mut resident = NoResident;
        let TreeAdvance::NeedsReads(initial_reads) =
            plan.advance(256, 16, &mut resident, &mut first_child)
        else {
            panic!("expected the initial 16 local-read needs");
        };
        // TreePlan has removed these needs from its unannounced set. A full
        // completion mailbox transfers them to the actor FIFO rather than
        // applying `Rejected`, which would recreate the zero-branch batch.
        let read_admission_backlog = VecDeque::from(initial_reads);
        assert_eq!(read_admission_backlog.len(), 16);
        assert!(
            !plan.has_runnable_frontier(),
            "broker-pending hashes alone cannot manufacture another scan"
        );

        let branch_steps_before = plan.branch_steps();
        assert!(matches!(
            plan.advance(256, 16, &mut resident, &mut first_child,),
            TreeAdvance::Ready
        ));
        assert_eq!(plan.branch_steps(), branch_steps_before);

        let mut actor_plan = ActorTreePlan {
            plan,
            reason: InboundLedgerRequestTrigger::Blind,
            peer: None,
            tickets: BTreeMap::new(),
            read_admission_backlog,
            runnable: false,
            aggressive_by_hash: false,
        };
        actor_plan.retarget(InboundLedgerRequestTrigger::Timeout, None, false);
        assert!(
            actor_plan.runnable,
            "a timeout must retry a callback-less broker-rejected FIFO"
        );
        assert!(
            !actor_plan.aggressive_by_hash,
            "a blocked local-read FIFO must not append a peer retry"
        );
        let ActorTreePlan {
            mut plan,
            read_admission_backlog,
            ..
        } = actor_plan;
        let mut read_admission_backlog = read_admission_backlog;

        // One real completion releases a reservation. The actor takes exactly
        // one FIFO entry for admission; the remaining needs stay retained and
        // do not reappear as another TreePlan NeedsReads result.
        let admitted_after_completion = read_admission_backlog
            .pop_front()
            .expect("retained FIFO must supply the freed completion slot");
        assert_eq!(read_admission_backlog.len(), 15);
        assert!(matches!(
            plan.apply_read_result(
                plan.id(),
                admitted_after_completion.hash(),
                MissingNodeReadOutcome::Miss,
            ),
            MissingNodeReadApply::Applied {
                attached_edges: 0,
                missing_edges: 1,
            }
        ));
        assert!(matches!(
            plan.advance(256, 16, &mut resident, &mut first_child,),
            TreeAdvance::Ready
        ));
    }

    #[test]
    fn ready_without_branch_progress_is_not_requeued() {
        use shamap::sync::{SHAMapType, SyncState, SyncTree};
        use shamap::tree_node::SHAMapTreeNode;

        struct NoResident;
        impl MissingNodeResidentLookup for NoResident {
            fn load_resident(
                &mut self,
                _hash: SHAMapHash,
                _ledger_seq: u32,
            ) -> Option<basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>> {
                None
            }
        }

        // The stack is intentionally retained and CPU-runnable, but a zero
        // branch budget produces `Ready` before the continuation can select a
        // branch. This is the actor-side shape that previously self-requeued
        // solely from `has_runnable_frontier()`.
        let child = SHAMapTreeNode::new_inner(1);
        child.set_child_hash(0, SHAMapHash::new(Uint256::from_array([0x51; 32])));
        child.update_hash();
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(0, child.get_hash());
        root.canonicalize_child(0, child);
        root.update_hash();
        let tree = SyncTree::from_root_with_type(
            root.clone(),
            SHAMapType::State,
            true,
            77,
            SyncState::Synching,
        );
        let mut first_child = || 0;
        let mut plan = TreePlan::new(
            TreePlanId::new(93),
            TreeKind::State,
            &tree,
            root.get_hash(),
            16,
            9,
            &mut first_child,
        );
        let mut resident = NoResident;
        let branch_steps_before = plan.branch_steps();

        assert!(matches!(
            plan.advance(0, 16, &mut resident, &mut first_child),
            TreeAdvance::Ready
        ));
        assert!(
            plan.has_runnable_frontier(),
            "the retained stack still has CPU work"
        );
        assert_eq!(plan.branch_steps(), branch_steps_before);
        assert!(
            !ready_turn_can_requeue(&plan, branch_steps_before),
            "a no-progress Ready turn must leave the mailbox idle"
        );
    }

    #[test]
    fn verified_peer_node_resumes_deferred_parent_and_queues_a_bounded_turn() {
        use shamap::sync::{SHAMapType, SyncState, SyncTree};
        use shamap::tree_node::SHAMapTreeNode;

        struct NoResident;
        impl MissingNodeResidentLookup for NoResident {
            fn load_resident(
                &mut self,
                _hash: SHAMapHash,
                _ledger_seq: u32,
            ) -> Option<basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>> {
                None
            }
        }

        let child = SHAMapTreeNode::new_inner(1);
        child.set_child_hash(0, SHAMapHash::new(Uint256::from_array([0x42; 32])));
        child.update_hash();
        let missing = child.get_hash();
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(7, missing);
        root.update_hash();
        let tree = SyncTree::from_root_with_type(
            root.clone(),
            SHAMapType::State,
            true,
            77,
            SyncState::Synching,
        );
        let mut first_child = || 0;
        let mut plan = TreePlan::new(
            TreePlanId::new(92),
            TreeKind::State,
            &tree,
            root.get_hash(),
            16,
            7,
            &mut first_child,
        );
        let mut resident = NoResident;
        let TreeAdvance::NeedsReads(reads) = plan.advance(256, 16, &mut resident, &mut first_child)
        else {
            panic!("expected one brokered read");
        };
        assert_eq!(reads.len(), 1);
        assert!(matches!(
            plan.apply_read_result(plan.id(), missing, MissingNodeReadOutcome::Miss),
            MissingNodeReadApply::Applied {
                missing_edges: 1,
                ..
            }
        ));
        assert!(matches!(
            plan.advance(256, 16, &mut resident, &mut first_child),
            TreeAdvance::NeedsNetwork(_)
        ));
        assert!(
            !plan.has_runnable_frontier(),
            "the retained plan is waiting on its peer edge"
        );

        let mut actor_plan = ActorTreePlan {
            plan,
            reason: InboundLedgerRequestTrigger::Blind,
            peer: None,
            tickets: BTreeMap::new(),
            read_admission_backlog: VecDeque::new(),
            runnable: false,
            aggressive_by_hash: false,
        };
        assert!(
            apply_verified_peer_nodes_to_plan(&mut actor_plan, [child]),
            "a verified peer node must wake its deferred parent"
        );
        assert!(actor_plan.runnable);
        assert!(actor_plan.plan.has_runnable_frontier());

        let mut mailbox = AcquisitionMailbox::default();
        mailbox.plan = Some(actor_plan);
        assert!(
            mailbox.wake_tree_plan(),
            "an idle mailbox must claim one bounded turn"
        );
        assert_eq!(mailbox.token, AcquisitionWorkToken::Queued);
        assert!(mailbox.has_work(false));
    }

    #[test]
    fn terminal_local_probe_cancellation_is_exact_once_and_accounts_late_events() {
        use super::super::read_broker::ReadBrokerConfig;

        let broker = NodeReadBroker::new(ReadBrokerConfig::default()).expect("valid broker config");
        let delivered = Arc::new(Mutex::new(Vec::<ReadReady>::new()));
        let sink: ReadReadySink = {
            let delivered = Arc::clone(&delivered);
            Arc::new(move |ready| {
                delivered
                    .lock()
                    .expect("local probe events lock")
                    .push(ready)
            })
        };
        let key = ReadKey::new(Uint256::from_array([15; 32]), 77, 0);
        let ticket = match broker.request(key, 41, LOCAL_PROBE_PLAN_ID, sink) {
            ReadAdmission::Accepted(ticket) => ticket,
            other => panic!("expected accepted local probe ticket, got {other:?}"),
        };

        let mut mailbox = AcquisitionMailbox::default();
        mailbox.local_probes.insert(
            ticket.id().get(),
            LocalProbe {
                ticket,
                kind: LocalProbeKind::Header,
                suppresses_network: true,
                reason: InboundLedgerRequestTrigger::Blind,
                peer: None,
            },
        );
        let terminal_tickets = mailbox.clear_terminal_work();
        assert_eq!(terminal_tickets, vec![ticket]);
        assert!(mailbox.local_probes.is_empty());
        assert!(
            mailbox.clear_terminal_work().is_empty(),
            "terminal cleanup cannot return a ticket twice"
        );

        assert!(broker.cancel(ticket));
        assert!(
            !broker.cancel(ticket),
            "the broker must not settle an already-cancelled ticket twice"
        );
        let delivered = delivered.lock().expect("local probe events lock");
        assert_eq!(delivered.len(), 1);
        assert_eq!(delivered[0].ticket, ticket);
        assert_eq!(delivered[0].outcome, ReadOutcome::Cancelled);
        drop(delivered);

        // `enqueue_read_ready` follows this terminal path for the cancelled
        // callback: no work is revived, and diagnostics retain the late event.
        mailbox.record_late_read_event();
        assert_eq!(mailbox.stale_events, 1);
        assert_eq!(broker.snapshot().metrics.cancelled, 1);
    }

    #[test]
    fn deferred_local_probe_keeps_one_ticket_without_suppressing_later_recovery() {
        use super::super::read_broker::ReadBrokerConfig;

        let broker = NodeReadBroker::new(ReadBrokerConfig {
            global_in_flight: 1,
            ..ReadBrokerConfig::default()
        })
        .expect("valid broker config");
        let sink: ReadReadySink = Arc::new(|_| {});
        let admitted = match broker.request(
            ReadKey::new(Uint256::from_array([0xD1; 32]), 77, 0),
            41,
            LOCAL_PROBE_PLAN_ID,
            Arc::clone(&sink),
        ) {
            ReadAdmission::Accepted(ticket) => ticket,
            other => panic!("expected admitted probe ticket, got {other:?}"),
        };
        let deferred = match broker.request(
            ReadKey::new(Uint256::from_array([0xD2; 32]), 77, 0),
            41,
            LOCAL_PROBE_PLAN_ID,
            sink,
        ) {
            ReadAdmission::Deferred(ticket) => ticket,
            other => panic!("expected deferred probe ticket, got {other:?}"),
        };

        let mut mailbox = AcquisitionMailbox::default();
        mailbox.local_probes.insert(
            deferred.id().get(),
            LocalProbe {
                ticket: deferred,
                kind: LocalProbeKind::Header,
                suppresses_network: false,
                reason: InboundLedgerRequestTrigger::Timeout,
                peer: None,
            },
        );
        for _ in 0..2 {
            assert_eq!(
                mailbox.local_probe_network_suppression(LocalProbeKind::Header),
                Some(false),
                "a repeated trigger must recover through the network while retaining the deferred ticket"
            );
        }
        assert_eq!(
            mailbox.local_probes.len(),
            1,
            "later triggers reuse the existing deferred subscription instead of issuing another local read"
        );
        assert!(broker.cancel(deferred));
        assert!(broker.cancel(admitted));
    }

    #[test]
    fn complete_wire_packets_remain_fifo_units() {
        let mut mailbox = AcquisitionMailbox::default();
        mailbox.packets.push_back(packet_work(11, 128));
        mailbox.packets.push_back(packet_work(22, 1));
        mailbox.packet_bytes = 129;

        let active = mailbox.packets.pop_front().expect("first FIFO packet");
        mailbox.packet_bytes = mailbox.packet_bytes.saturating_sub(active.bytes);
        assert_eq!(active.peer_id, 11);
        assert_eq!(mailbox.packets.front().expect("later packet").peer_id, 22);
        assert_eq!(mailbox.packet_bytes, 1);
    }

    #[test]
    fn terminal_packet_first_header_receipt_is_recorded_exactly_once() {
        let stats = AcquisitionStats::new();
        let lifecycle = AcquisitionLifecycleCounters::default();

        record_first_packet_header_received(&stats, &lifecycle, false, true, true);
        record_first_packet_header_received(&stats, &lifecycle, true, true, true);

        assert!(
            stats
                .first_header_at
                .lock()
                .expect("acquisition first_header_at lock")
                .is_some(),
            "the terminal packet's first header must set its receipt timestamp"
        );
        assert_eq!(
            lifecycle.reply_headers_received.load(Ordering::Relaxed),
            1,
            "a later packet observing the same header must not increment again"
        );
    }

    fn network_waiting_actor_plan(
        plan_id: u64,
        reason: InboundLedgerRequestTrigger,
        aggressive_by_hash: bool,
    ) -> ActorTreePlan {
        use shamap::sync::{SHAMapType, SyncState, SyncTree};
        use shamap::tree_node::SHAMapTreeNode;

        struct NoResident;
        impl MissingNodeResidentLookup for NoResident {
            fn load_resident(
                &mut self,
                _hash: SHAMapHash,
                _ledger_seq: u32,
            ) -> Option<basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>> {
                None
            }
        }

        let missing = SHAMapHash::new(Uint256::from_array([plan_id as u8; 32]));
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(7, missing);
        root.update_hash();
        let tree = SyncTree::from_root_with_type(
            root.clone(),
            SHAMapType::State,
            true,
            77,
            SyncState::Synching,
        );
        let mut first_child = || 0;
        let mut plan = TreePlan::new(
            TreePlanId::new(plan_id),
            TreeKind::State,
            &tree,
            root.get_hash(),
            16,
            7,
            &mut first_child,
        );
        let mut resident = NoResident;
        let TreeAdvance::NeedsReads(reads) = plan.advance(256, 16, &mut resident, &mut first_child)
        else {
            panic!("expected one brokered read");
        };
        assert_eq!(reads.len(), 1);
        assert!(matches!(
            plan.apply_read_result(plan.id(), missing, MissingNodeReadOutcome::Miss),
            MissingNodeReadApply::Applied {
                missing_edges: 1,
                ..
            }
        ));
        assert!(matches!(
            plan.advance(256, 16, &mut resident, &mut first_child),
            TreeAdvance::NeedsNetwork(_)
        ));
        ActorTreePlan {
            plan,
            reason,
            peer: None,
            tickets: BTreeMap::new(),
            read_admission_backlog: VecDeque::new(),
            runnable: false,
            aggressive_by_hash,
        }
    }

    #[test]
    fn needs_network_send_hook_observes_restored_plan_for_ordinary_and_aggressive_requests() {
        for (plan_id, reason, initial_aggressive_by_hash, restored_aggressive_by_hash) in [
            (93, InboundLedgerRequestTrigger::Reply, false, false),
            (94, InboundLedgerRequestTrigger::Timeout, true, false),
        ] {
            let mut actor_plan =
                network_waiting_actor_plan(plan_id, reason, initial_aggressive_by_hash);
            // Mirror the aggressive branch's pre-restoration commit: the
            // synchronous send hook must see the consumed state, not the
            // detached plan's earlier by-hash value.
            actor_plan.aggressive_by_hash = restored_aggressive_by_hash;
            let mailbox = Arc::new(Mutex::new(AcquisitionMailbox::default()));
            let restored_mailbox = Arc::clone(&mailbox);
            let send_hook_mailbox = Arc::clone(&mailbox);
            let send_hook_observed_restored_plan = Arc::new(AtomicBool::new(false));
            let send_hook_observation = Arc::clone(&send_hook_observed_restored_plan);

            restore_tree_plan_before_peer_send(
                actor_plan,
                move |actor_plan| {
                    restored_mailbox.lock().expect("restore mailbox lock").plan = Some(actor_plan);
                    true
                },
                move || {
                    // This deterministic send hook models a synchronous peer
                    // callback and must observe the committed retained plan.
                    let restored = send_hook_mailbox.lock().expect("send-hook mailbox lock");
                    let plan = restored
                        .plan
                        .as_ref()
                        .expect("plan restored before send hook");
                    assert_eq!(plan.plan.id(), TreePlanId::new(plan_id));
                    assert_eq!(plan.reason, reason);
                    assert_eq!(plan.aggressive_by_hash, restored_aggressive_by_hash);
                    assert!(!plan.runnable, "NeedsNetwork is waiting after emission");
                    send_hook_observation.store(true, Ordering::Release);
                },
            );
            assert!(
                send_hook_observed_restored_plan.load(Ordering::Acquire),
                "{reason:?} send hook must run after plan restoration"
            );
        }
    }

    #[test]
    fn local_read_batch_fence_requires_all_admitted_reads_to_settle() {
        use super::super::read_broker::ReadBrokerConfig;

        let broker = NodeReadBroker::new(ReadBrokerConfig::default()).expect("valid broker config");
        let events = Arc::new(Mutex::new(Vec::<ReadReady>::new()));
        let sink: ReadReadySink = {
            let events = Arc::clone(&events);
            Arc::new(move |ready| events.lock().expect("read events lock").push(ready))
        };
        let first = match broker.request(
            ReadKey::new(Uint256::from_array([0xA1; 32]), 77, 0),
            41,
            93,
            Arc::clone(&sink),
        ) {
            ReadAdmission::Accepted(ticket) => ticket,
            other => panic!("expected first accepted ticket, got {other:?}"),
        };
        let second = match broker.request(
            ReadKey::new(Uint256::from_array([0xA2; 32]), 77, 0),
            41,
            93,
            sink,
        ) {
            ReadAdmission::Accepted(ticket) => ticket,
            other => panic!("expected second accepted ticket, got {other:?}"),
        };

        let mut actor_plan =
            network_waiting_actor_plan(93, InboundLedgerRequestTrigger::Reply, false);
        actor_plan
            .tickets
            .insert(SHAMapHash::new(first.key().hash), first);
        actor_plan
            .tickets
            .insert(SHAMapHash::new(second.key().hash), second);
        assert!(actor_plan.awaiting_local_read_batch());

        actor_plan
            .tickets
            .remove(&SHAMapHash::new(first.key().hash));
        assert!(
            actor_plan.awaiting_local_read_batch(),
            "one local miss cannot expose peer candidates before its batch completes"
        );
        actor_plan
            .tickets
            .remove(&SHAMapHash::new(second.key().hash));
        assert!(!actor_plan.awaiting_local_read_batch());
    }

    #[test]
    fn cancelled_restore_suppresses_peer_send_and_settles_ticket() {
        use super::super::read_broker::ReadBrokerConfig;

        let broker = NodeReadBroker::new(ReadBrokerConfig::default()).expect("valid broker config");
        let events = Arc::new(Mutex::new(Vec::<ReadReady>::new()));
        let sink: ReadReadySink = {
            let events = Arc::clone(&events);
            Arc::new(move |ready| events.lock().expect("read events lock").push(ready))
        };
        let ticket = match broker.request(
            ReadKey::new(Uint256::from_array([0xD1; 32]), 77, 0),
            41,
            93,
            sink,
        ) {
            ReadAdmission::Accepted(ticket) => ticket,
            other => panic!("expected accepted ticket, got {other:?}"),
        };
        let dispatch = broker
            .take_ready_dispatches()
            .into_iter()
            .next()
            .expect("admitted read dispatch");
        let mut actor_plan =
            network_waiting_actor_plan(93, InboundLedgerRequestTrigger::Reply, false);
        actor_plan
            .tickets
            .insert(SHAMapHash::new(ticket.key().hash), ticket);
        let sent = Arc::new(AtomicBool::new(false));
        let sent_hook = Arc::clone(&sent);
        let cancel_broker = broker.clone();

        assert!(
            !restore_tree_plan_before_peer_send(
                actor_plan,
                move |actor_plan| {
                    for ticket in actor_plan.tickets.into_values() {
                        assert!(cancel_broker.cancel(ticket));
                    }
                    false
                },
                move || sent_hook.store(true, Ordering::Release),
            ),
            "terminal restore must report non-live"
        );
        assert!(
            !sent.load(Ordering::Acquire),
            "a peer request cannot send after cancellation wins"
        );
        assert_eq!(events.lock().expect("read events lock").len(), 1);
        assert_eq!(
            events.lock().expect("read events lock")[0].outcome,
            ReadOutcome::Cancelled
        );
        assert!(
            !broker.cancel(ticket),
            "terminal restoration leaves no retained broker subscription"
        );
        dispatch.complete(ReadOutcome::Miss);
    }

    #[test]
    fn network_request_overflow_is_requeued_without_marking_or_timeout() {
        use shamap::sync::{SHAMapType, SyncState, SyncTree};
        use shamap::tree_node::SHAMapTreeNode;

        struct NoResident;
        impl MissingNodeResidentLookup for NoResident {
            fn load_resident(
                &mut self,
                _hash: SHAMapHash,
                _ledger_seq: u32,
            ) -> Option<basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>> {
                None
            }
        }

        let root = SHAMapTreeNode::new_inner(1);
        for branch in 0..16 {
            root.set_child_hash(
                branch,
                SHAMapHash::new(Uint256::from_array([(branch + 1) as u8; 32])),
            );
        }
        root.update_hash();
        let tree = SyncTree::from_root_with_type(
            root.clone(),
            SHAMapType::State,
            true,
            77,
            SyncState::Synching,
        );
        let mut first_child = || 0;
        let mut plan = TreePlan::new(
            TreePlanId::new(95),
            TreeKind::State,
            &tree,
            root.get_hash(),
            16,
            7,
            &mut first_child,
        );
        let mut resident = NoResident;
        let TreeAdvance::NeedsReads(reads) = plan.advance(256, 16, &mut resident, &mut first_child)
        else {
            panic!("expected sixteen brokered reads");
        };
        for read in reads {
            assert!(matches!(
                plan.apply_read_result(plan.id(), read.hash(), MissingNodeReadOutcome::Miss),
                MissingNodeReadApply::Applied { .. }
            ));
        }
        let TreeAdvance::NeedsNetwork(candidates) =
            plan.advance(256, 16, &mut resident, &mut first_child)
        else {
            panic!("expected sixteen network candidates");
        };
        assert_eq!(candidates.len(), 16);

        let selected = select_tree_network_candidates(&mut plan, candidates, 12);
        assert_eq!(selected.len(), 12, "outbound serialization remains bounded");
        let overflow = plan.take_network_candidates();
        assert_eq!(
            overflow.len(),
            4,
            "overflow stays on the immediate frontier"
        );
        for (_, hash) in overflow {
            assert!(
                plan.mark_request_candidate(hash),
                "an overflow candidate was not marked before its later request"
            );
        }
    }

    #[test]
    fn timeout_retargets_the_retained_network_frontier_without_rebuilding() {
        use shamap::sync::{SHAMapType, SyncState, SyncTree};
        use shamap::tree_node::SHAMapTreeNode;

        struct NoResident;
        impl MissingNodeResidentLookup for NoResident {
            fn load_resident(
                &mut self,
                _hash: SHAMapHash,
                _ledger_seq: u32,
            ) -> Option<basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>> {
                None
            }
        }

        let missing = SHAMapHash::new(Uint256::from_array([42; 32]));
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(7, missing);
        root.update_hash();
        let tree = SyncTree::from_root_with_type(
            root.clone(),
            SHAMapType::State,
            true,
            77,
            SyncState::Synching,
        );
        let mut first_child = || 0;
        let mut plan = TreePlan::new(
            TreePlanId::new(91),
            TreeKind::State,
            &tree,
            root.get_hash(),
            16,
            7,
            &mut first_child,
        );
        let mut resident = NoResident;
        let TreeAdvance::NeedsReads(reads) = plan.advance(256, 16, &mut resident, &mut first_child)
        else {
            panic!("expected one brokered read");
        };
        assert_eq!(reads.len(), 1);
        assert!(matches!(
            plan.apply_read_result(plan.id(), missing, MissingNodeReadOutcome::Miss),
            MissingNodeReadApply::Applied {
                missing_edges: 1,
                ..
            }
        ));
        assert!(matches!(
            plan.advance(256, 16, &mut resident, &mut first_child),
            TreeAdvance::NeedsNetwork(_)
        ));

        let mut retained = ActorTreePlan {
            plan,
            reason: InboundLedgerRequestTrigger::Blind,
            peer: None,
            tickets: BTreeMap::new(),
            read_admission_backlog: VecDeque::new(),
            runnable: false,
            aggressive_by_hash: false,
        };
        assert!(!uses_aggressive_by_hash_timeout(4));
        assert!(uses_aggressive_by_hash_timeout(5));
        retained.retarget(InboundLedgerRequestTrigger::Timeout, None, true);
        assert!(
            retained.runnable,
            "a lost peer reply wakes the same retained plan"
        );
        assert!(
            retained.aggressive_by_hash,
            "the existing >4 threshold selects by-hash"
        );
        assert_eq!(
            retained.plan.id(),
            TreePlanId::new(91),
            "retarget never rebuilds a plan"
        );
        assert!(matches!(
            retained
                .plan
                .advance(256, 16, &mut resident, &mut first_child),
            TreeAdvance::NeedsNetwork(_)
        ));
    }

    #[test]
    fn persistence_queue_dispatches_once_and_deduplicates() {
        let mut queue = PersistenceQueue::default();
        let write = PersistenceWrite {
            key: PersistenceKey {
                hash: Uint256::from_array([8; 32]),
                ledger_seq: 12,
                object_type: 3,
            },
            object_type: nodestore::NodeObjectType::Ledger,
            data: vec![7],
        };
        queue.enqueue_writes(42, 7, vec![write.clone()]);
        let first = queue.take_next().expect("first write dispatch");
        queue.enqueue_writes(42, 7, vec![write]);
        queue.enqueue_barrier(42, 7);
        assert!(
            queue.take_next().is_none(),
            "an in-flight command cannot dispatch twice"
        );
        assert_eq!(
            queue.in_flight.as_ref().map(PersistenceCommand::identity),
            Some(first.identity())
        );
        assert!(
            queue
                .acknowledge(&PersistenceReady {
                    identity: first.identity(),
                    outcome: PersistenceOutcome::Durable,
                    durability_barrier: false,
                })
                .is_some()
        );
        assert!(matches!(
            queue.take_next(),
            Some(PersistenceCommand::DurabilityBarrier { .. })
        ));
    }

    #[test]
    fn terminal_cancellation_discards_in_flight_and_queued_persistence() {
        let mut queue = PersistenceQueue::default();
        queue.enqueue_writes(
            43,
            8,
            vec![PersistenceWrite {
                key: PersistenceKey {
                    hash: Uint256::from_array([6; 32]),
                    ledger_seq: 13,
                    object_type: 3,
                },
                object_type: nodestore::NodeObjectType::Ledger,
                data: vec![9],
            }],
        );
        queue.enqueue_barrier(43, 8);
        let in_flight = queue.take_next().expect("write dispatch");
        queue.cancel();
        assert!(queue.in_flight.is_none());
        assert!(queue.queued.is_empty());
        assert!(
            queue
                .acknowledge(&PersistenceReady {
                    identity: in_flight.identity(),
                    outcome: PersistenceOutcome::Durable,
                    durability_barrier: false,
                })
                .is_none(),
            "late worker completion cannot overwrite terminal cancellation"
        );
    }

    #[test]
    fn completed_ledger_fetcher_reads_through_cache_and_nodestore() {
        let source = include_str!("acquisition.rs");
        let start = source
            .find("fn build_resolver_visible_ledger")
            .expect("resolver-visible ledger builder source");
        let builder = &source[start
            ..source[start..]
                .find("\nfn finalize_acquisition")
                .map(|offset| start + offset)
                .expect("resolver-visible ledger builder boundary")];
        assert!(builder.contains("snapshot_completed_ledger(state)"));
        assert!(builder.contains("tree_cache.fetch(hash.as_uint256())"));
        assert!(builder.contains("fetch_node_object("));
        assert!(builder.contains("FetchType::Synchronous"));
    }

    #[test]
    fn resolver_publication_waits_for_durability_fence() {
        let source = include_str!("acquisition.rs");
        let start = source
            .find("fn finalize_acquisition")
            .expect("initial finalizer source");
        let durable = source[start..]
            .find("fn finalize_durable_acquisition")
            .map(|offset| start + offset)
            .expect("durable finalizer source");
        let initial = &source[start..durable];
        let durable_finalizer = &source[durable..];
        assert!(initial.contains("enqueue_durability_barrier"));
        assert!(!initial.contains("publish_resolver_visible_ledger("));
        assert!(durable_finalizer.contains("publish_resolver_visible_ledger("));
    }

    #[test]
    fn persistence_queue_keeps_write_then_barrier_in_fifo_ack_order() {
        let mut queue = PersistenceQueue::default();
        let write = PersistenceWrite {
            key: PersistenceKey {
                hash: Uint256::from_array([9; 32]),
                ledger_seq: 10,
                object_type: 3,
            },
            object_type: nodestore::NodeObjectType::Ledger,
            data: vec![1, 2, 3],
        };
        queue.enqueue_writes(44, 9, vec![write]);
        queue.enqueue_barrier(44, 9);
        let first = queue.take_next().expect("write command");
        assert!(matches!(first, PersistenceCommand::WriteBatch { .. }));
        assert!(
            queue
                .acknowledge(&PersistenceReady {
                    identity: first.identity(),
                    outcome: PersistenceOutcome::Durable,
                    durability_barrier: false,
                })
                .is_some()
        );
        let second = queue.take_next().expect("barrier command");
        assert!(matches!(
            second,
            PersistenceCommand::DurabilityBarrier { .. }
        ));
        assert!(
            queue
                .acknowledge(&PersistenceReady {
                    identity: second.identity(),
                    outcome: PersistenceOutcome::Durable,
                    durability_barrier: true,
                })
                .is_some()
        );
        assert!(queue.barrier_acknowledged);
    }

    #[test]
    fn persistence_fault_cancels_queued_barrier_before_publication_can_proceed() {
        let mut queue = PersistenceQueue::default();
        queue.enqueue_writes(
            45,
            10,
            vec![PersistenceWrite {
                key: PersistenceKey {
                    hash: Uint256::from_array([7; 32]),
                    ledger_seq: 11,
                    object_type: 3,
                },
                object_type: nodestore::NodeObjectType::Ledger,
                data: vec![4, 5, 6],
            }],
        );
        queue.enqueue_barrier(45, 10);
        let write = queue.take_next().expect("write command");
        assert!(matches!(write, PersistenceCommand::WriteBatch { .. }));
        assert!(
            queue
                .acknowledge(&PersistenceReady {
                    identity: write.identity(),
                    outcome: PersistenceOutcome::Fault(Arc::from("store fault")),
                    durability_barrier: false,
                })
                .is_some()
        );
        assert!(
            queue.failed.is_some(),
            "a write fault is terminal before publication"
        );
        queue.cancel();
        assert!(
            queue.queued.is_empty(),
            "failure cancels the unacknowledged barrier"
        );
        assert!(
            queue.take_next().is_none(),
            "no barrier can acknowledge after a write fault"
        );
    }

    #[test]
    fn packet_admission_reservations_are_bounded_and_terminal_clear_settles_them() {
        let mut mailbox = AcquisitionMailbox::default();
        mailbox.packet_admissions.insert(1, 64);
        mailbox
            .packet_admissions
            .insert(2, ACQ_MAILBOX_BYTE_CAPACITY - 64);
        assert_eq!(mailbox.packet_admissions.len(), 2);
        assert_eq!(
            mailbox.packet_admissions.values().sum::<usize>(),
            ACQ_MAILBOX_BYTE_CAPACITY,
            "leases account for byte capacity before decoded packets enter FIFO ownership"
        );

        mailbox.clear_terminal_work();
        assert!(
            mailbox.packet_admissions.is_empty(),
            "terminal cleanup settles every actor-owned transport reservation exactly once"
        );
    }

    #[test]
    fn persistence_identity_mismatch_remains_in_flight_until_its_exact_acknowledgement() {
        let mut queue = PersistenceQueue::default();
        queue.enqueue_writes(
            71,
            19,
            vec![PersistenceWrite {
                key: PersistenceKey {
                    hash: Uint256::from_array([0x71; 32]),
                    ledger_seq: 19,
                    object_type: 3,
                },
                object_type: nodestore::NodeObjectType::Ledger,
                data: vec![1],
            }],
        );
        let command = queue.take_next().expect("admitted persistence command");
        let identity = command.identity();
        let stale = PersistenceIdentity {
            store_generation: identity.store_generation.saturating_add(1),
            ..identity
        };
        assert!(
            queue
                .acknowledge(&PersistenceReady {
                    identity: stale,
                    outcome: PersistenceOutcome::Durable,
                    durability_barrier: false,
                })
                .is_none(),
            "a rotation-mismatched acknowledgement cannot settle the active command"
        );
        assert_eq!(
            queue.in_flight.as_ref().map(PersistenceCommand::identity),
            Some(identity)
        );
        assert!(
            queue
                .acknowledge(&PersistenceReady {
                    identity,
                    outcome: PersistenceOutcome::Durable,
                    durability_barrier: false,
                })
                .is_some()
        );
    }

    #[test]
    fn terminal_clear_releases_mailbox_packet_and_event_ownership() {
        let mut mailbox = AcquisitionMailbox::default();
        mailbox.packets.push_back(packet_work(7, 64));
        mailbox.packet_bytes = 64;
        mailbox.pending_timeouts = 1;
        mailbox.token = AcquisitionWorkToken::Running;

        let tickets = mailbox.clear_terminal_work();

        assert!(tickets.is_empty());
        assert!(mailbox.packets.is_empty());
        assert!(mailbox.events.is_empty());
        assert_eq!(mailbox.packet_bytes, 0);
        assert_eq!(mailbox.pending_timeouts, 0);
        assert_eq!(mailbox.token, AcquisitionWorkToken::Idle);
    }
}
