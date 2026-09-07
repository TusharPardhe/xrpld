use crate::database::{
    Database as DatabaseTrait, DatabaseDelegate, DatabaseImporter, DatabaseRuntime, DatabaseSource,
};
use crate::{
    AsyncReadWork, Backend, FetchReport, FetchType, JournalLevel, NodeObject, NodeObjectType,
    NodeStoreJournal, ScheduledWrite, Scheduler, Status,
};
use basics::base_uint::Uint256;
use basics::basic_config::Section;
use basics::blob::Blob;
use basics::str_hex::str_hex;
use protocol::JsonValue;
use std::any::Any;
use std::collections::{BTreeMap, BTreeSet};
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::Arc;

struct DatabaseNodeImpCore {
    backend: Arc<dyn Backend>,
}

impl DatabaseDelegate for DatabaseNodeImpCore {
    fn is_same_db(&self, _first: u32, _second: u32) -> bool {
        true
    }

    fn fetch_node_object(
        &self,
        hash: &Uint256,
        _ledger_seq: u32,
        fetch_report: &mut FetchReport,
        _duplicate: bool,
        journal: &dyn NodeStoreJournal,
    ) -> Option<Arc<NodeObject>> {
        let hash_hex = str_hex(hash.data());
        let (node_object, status) =
            match catch_unwind(AssertUnwindSafe(|| self.backend.fetch(hash))) {
                Ok(result) => result,
                Err(payload) => {
                    journal.log(
                        JournalLevel::Fatal,
                        &format!(
                            "fetchNodeObject {hash_hex}: Exception fetching from backend: {}",
                            panic_message(payload.as_ref())
                        ),
                    );
                    resume_unwind(payload);
                }
            };

        match status {
            Status::Ok | Status::NotFound => {}
            Status::DataCorrupt => {
                let message = format!("fetchNodeObject {hash_hex}: nodestore data is corrupted");
                tracing::error!(target: "nodestore", %message);
                journal.log(JournalLevel::Error, &message);
                // rippled logs its fatal backend-read failure and rethrows.
                // This Rust surface has status values instead of exceptions,
                // so propagate every non-miss status as a panic rather than
                // converting corruption into an ordinary cache miss.
                panic!("{message}");
            }
            other => {
                let message =
                    format!("fetchNodeObject {hash_hex}: backend returned error status {other:?}");
                tracing::error!(target: "nodestore", %message);
                journal.log(JournalLevel::Error, &message);
                panic!("{message}");
            }
        }

        if node_object.is_some() {
            fetch_report.was_found = true;
        }
        node_object
    }

    fn evict_membership_filter(&self) {
        // Single-store delegate: forward to the backend so its transient
        // (e.g. backfill-acceleration) Bloom filter memory is reclaimed.
        self.backend.evict_membership_filter();
    }
}

pub struct DatabaseNodeImp {
    database: DatabaseRuntime,
    backend: Arc<dyn Backend>,
}

impl Drop for DatabaseNodeImp {
    fn drop(&mut self) {
        self.stop();
    }
}

impl DatabaseNodeImp {
    pub fn new(
        scheduler: Arc<dyn Scheduler>,
        read_threads: usize,
        backend: Arc<dyn Backend>,
        config: &Section,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Arc<Self>, String> {
        let database = DatabaseRuntime::new(
            Arc::new(DatabaseNodeImpCore {
                backend: backend.clone(),
            }),
            scheduler,
            read_threads,
            config,
            journal,
        )?;

        Ok(Arc::new(Self { database, backend }))
    }

    pub fn get_name(&self) -> String {
        self.backend.get_name()
    }

    pub fn get_write_load(&self) -> i32 {
        self.backend.get_write_load()
    }

    pub fn import_database(&self, source: &dyn DatabaseSource) {
        self.database.import_internal(self.backend.as_ref(), source);
    }

    pub fn store(
        &self,
        object_type: NodeObjectType,
        data: Blob,
        hash: Uint256,
        _ledger_seq: u32,
    ) -> Result<(), String> {
        let object = NodeObject::create_object(object_type, data, hash);
        self.backend.store(Arc::clone(&object)).map_err(|error| {
            tracing::error!(target: "nodestore", %error, hash = %object.hash(), "NodeStore backend write failed");
            error
        })?;
        // Match rippled's post-store canonicalization ordering: neither
        // counters nor cache state can imply a write that the backend rejected.
        self.database.store_stats(1, object.data().len() as u64);
        self.database.promote_node_object(object);
        Ok(())
    }

    /// Persist a complete NodeStore batch and publish cache/stat bookkeeping
    /// only after the backend reports success for the whole batch.
    pub fn store_batch(
        &self,
        objects: Vec<(NodeObjectType, Blob, Uint256, u32)>,
    ) -> Result<(), String> {
        let mut seen_hashes = BTreeSet::new();
        let batch = objects
            .into_iter()
            .filter_map(|(object_type, data, hash, _ledger_seq)| {
                seen_hashes
                    .insert(hash)
                    .then(|| NodeObject::create_object(object_type, data, hash))
            })
            .collect::<crate::Batch>();
        self.backend.store_batch_result(&batch).map_err(|error| {
            tracing::error!(
                target: "nodestore",
                %error,
                object_count = batch.len(),
                "NodeStore backend batch write failed"
            );
            error
        })?;
        for object in batch {
            self.database.store_stats(1, object.data().len() as u64);
            self.database.promote_node_object(object);
        }
        Ok(())
    }

    pub fn is_same_db(&self, _first: u32, _second: u32) -> bool {
        true
    }

    pub fn sync(&self) {
        self.backend.sync();
    }

    pub fn sync_result(&self) -> Result<(), String> {
        self.backend.sync_result()
    }

    pub fn fetch_node_object(
        &self,
        hash: &Uint256,
        ledger_seq: u32,
        fetch_type: FetchType,
        duplicate: bool,
    ) -> Option<Arc<NodeObject>> {
        self.database
            .fetch_node_object(hash, ledger_seq, fetch_type, duplicate)
    }

    pub fn async_fetch(&self, hash: Uint256, ledger_seq: u32, work: Box<dyn AsyncReadWork>) {
        self.database.async_fetch(hash, ledger_seq, work);
    }

    /// Compatibility batch helper. The public Database trait has no batch
    /// surface, so route each element through DatabaseRuntime to retain the
    /// mandatory cache, validation, and single-flight policy.
    pub fn fetch_batch(&self, hashes: &[Uint256]) -> Vec<Option<Arc<NodeObject>>> {
        hashes
            .iter()
            .map(|hash| {
                let result =
                    self.database
                        .fetch_node_object(hash, 0, FetchType::Synchronous, false);
                if result.is_none() {
                    self.database.journal().log(
                        JournalLevel::Error,
                        &format!(
                            "fetchBatch - record not found in db. hash = {}",
                            str_hex(hash.data())
                        ),
                    );
                }
                result
            })
            .collect()
    }

    pub fn stop(&self) {
        self.database.stop();
        if let Err(error) = self.backend.close() {
            tracing::error!(target: "nodestore", %error, "NodeStore backend close failed");
        }
    }

    pub fn is_stopping(&self) -> bool {
        self.database.is_stopping()
    }

    pub fn earliest_ledger_seq(&self) -> u32 {
        self.database.earliest_ledger_seq()
    }

    pub fn get_store_count(&self) -> u64 {
        self.database.get_store_count()
    }

    pub fn get_fetch_total_count(&self) -> u64 {
        self.database.get_fetch_total_count()
    }

    pub fn get_fetch_hit_count(&self) -> u64 {
        self.database.get_fetch_hit_count()
    }

    pub fn get_store_size(&self) -> u64 {
        self.database.get_store_size()
    }

    pub fn get_fetch_size(&self) -> u64 {
        self.database.get_fetch_size()
    }

    pub fn add_counts_json(&self, obj: &mut BTreeMap<String, JsonValue>) {
        self.database.add_counts_json(obj);
    }

    pub fn get_counts_json(&self) -> JsonValue {
        self.database.get_counts_json()
    }

    pub fn fd_required(&self) -> i32 {
        self.backend.fd_required()
    }

    pub fn store_generation(&self) -> u64 {
        self.database.store_generation()
    }
}

impl DatabaseSource for DatabaseNodeImp {
    fn for_each(&self, callback: &mut dyn FnMut(Arc<NodeObject>)) {
        self.backend.for_each(callback);
    }
}

impl DatabaseImporter for DatabaseNodeImp {
    fn import_database(&self, source: &dyn DatabaseSource) {
        DatabaseNodeImp::import_database(self, source);
    }
}

impl DatabaseTrait for DatabaseNodeImp {
    fn get_name(&self) -> String {
        DatabaseNodeImp::get_name(self)
    }

    fn get_write_load(&self) -> i32 {
        DatabaseNodeImp::get_write_load(self)
    }

    fn store(
        &self,
        object_type: NodeObjectType,
        data: Blob,
        hash: Uint256,
        ledger_seq: u32,
    ) -> Result<(), String> {
        DatabaseNodeImp::store(self, object_type, data, hash, ledger_seq)
    }

    fn store_batch(
        &self,
        objects: Vec<(NodeObjectType, Blob, Uint256, u32)>,
    ) -> Result<(), String> {
        DatabaseNodeImp::store_batch(self, objects)
    }

    fn is_same_db(&self, first: u32, second: u32) -> bool {
        let _ = (first, second);
        true
    }

    fn sync(&self) {
        DatabaseNodeImp::sync(self);
    }

    fn sync_result(&self) -> Result<(), String> {
        DatabaseNodeImp::sync_result(self)
    }

    fn schedule_write(&self, write: ScheduledWrite) {
        self.database.schedule_write(write);
    }

    fn store_generation(&self) -> u64 {
        DatabaseNodeImp::store_generation(self)
    }

    fn fetch_node_object(
        &self,
        hash: &Uint256,
        ledger_seq: u32,
        fetch_type: FetchType,
        duplicate: bool,
    ) -> Option<Arc<NodeObject>> {
        DatabaseNodeImp::fetch_node_object(self, hash, ledger_seq, fetch_type, duplicate)
    }

    fn async_fetch(&self, hash: Uint256, ledger_seq: u32, work: Box<dyn AsyncReadWork>) {
        DatabaseNodeImp::async_fetch(self, hash, ledger_seq, work);
    }

    fn stop(&self) {
        DatabaseNodeImp::stop(self);
    }

    fn is_stopping(&self) -> bool {
        DatabaseNodeImp::is_stopping(self)
    }

    fn earliest_ledger_seq(&self) -> u32 {
        DatabaseNodeImp::earliest_ledger_seq(self)
    }

    fn get_store_count(&self) -> u64 {
        DatabaseNodeImp::get_store_count(self)
    }

    fn get_fetch_total_count(&self) -> u64 {
        DatabaseNodeImp::get_fetch_total_count(self)
    }

    fn get_fetch_hit_count(&self) -> u64 {
        DatabaseNodeImp::get_fetch_hit_count(self)
    }

    fn get_store_size(&self) -> u64 {
        DatabaseNodeImp::get_store_size(self)
    }

    fn get_fetch_size(&self) -> u64 {
        DatabaseNodeImp::get_fetch_size(self)
    }

    fn add_counts_json(&self, obj: &mut BTreeMap<String, JsonValue>) {
        DatabaseNodeImp::add_counts_json(self, obj);
    }

    fn get_counts_json(&self) -> JsonValue {
        DatabaseNodeImp::get_counts_json(self)
    }

    fn fd_required(&self) -> i32 {
        DatabaseNodeImp::fd_required(self)
    }

    fn export_backend(&self) -> Option<Arc<dyn Backend>> {
        Some(Arc::clone(&self.backend))
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
    use super::DatabaseNodeImp;
    use crate::{
        Backend, BatchWriteReport, Database as DatabaseTrait, FetchReport, NodeObject,
        NodeObjectType, NullJournal, PersistenceWork, Scheduler, Status, Task,
    };
    use basics::base_uint::Uint256;
    use basics::basic_config::Section;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Mutex};

    struct RejectingScheduler {
        attempts: Arc<AtomicUsize>,
    }

    impl Scheduler for RejectingScheduler {
        fn schedule_task(&self, _task: Arc<dyn Task>) {}

        fn try_schedule_task(&self, _task: Arc<dyn Task>) -> bool {
            self.attempts.fetch_add(1, Ordering::AcqRel);
            false
        }

        fn on_fetch(&self, _report: FetchReport) {}

        fn on_batch_write(&self, _report: BatchWriteReport) {}
    }

    struct EmptyBackend;

    impl Backend for EmptyBackend {
        fn get_name(&self) -> String {
            "empty".to_owned()
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

        fn fetch_batch(&self, hashes: &[Uint256]) -> (Vec<Option<Arc<NodeObject>>>, Status) {
            (vec![None; hashes.len()], Status::NotFound)
        }

        fn store(&self, _object: Arc<NodeObject>) -> Result<(), String> {
            Ok(())
        }

        fn store_batch(&self, _batch: &crate::Batch) {}

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

    struct FailingBatchBackend;

    impl Backend for FailingBatchBackend {
        fn get_name(&self) -> String {
            "failing-batch".to_owned()
        }
        fn open(&self, _: bool) -> Result<(), String> {
            Ok(())
        }
        fn is_open(&self) -> bool {
            true
        }
        fn close(&self) -> Result<(), String> {
            Ok(())
        }
        fn fetch(&self, _: &Uint256) -> (Option<Arc<NodeObject>>, Status) {
            (None, Status::NotFound)
        }
        fn fetch_batch(&self, hashes: &[Uint256]) -> (Vec<Option<Arc<NodeObject>>>, Status) {
            (vec![None; hashes.len()], Status::NotFound)
        }
        fn store(&self, _: Arc<NodeObject>) -> Result<(), String> {
            Ok(())
        }
        fn store_batch(&self, _: &crate::Batch) {}
        fn store_batch_result(&self, _: &crate::Batch) -> Result<(), String> {
            Err("injected batch failure".to_owned())
        }
        fn sync(&self) {}
        fn for_each(&self, _: &mut dyn FnMut(Arc<NodeObject>)) {}
        fn get_write_load(&self) -> i32 {
            0
        }
        fn set_delete_path(&self) {}
        fn fd_required(&self) -> i32 {
            0
        }
    }

    struct CapturingBatchBackend {
        batch: Arc<Mutex<crate::Batch>>,
    }

    impl Backend for CapturingBatchBackend {
        fn get_name(&self) -> String {
            "capturing-batch".to_owned()
        }
        fn open(&self, _: bool) -> Result<(), String> {
            Ok(())
        }
        fn is_open(&self) -> bool {
            true
        }
        fn close(&self) -> Result<(), String> {
            Ok(())
        }
        fn fetch(&self, _: &Uint256) -> (Option<Arc<NodeObject>>, Status) {
            (None, Status::NotFound)
        }
        fn fetch_batch(&self, hashes: &[Uint256]) -> (Vec<Option<Arc<NodeObject>>>, Status) {
            (vec![None; hashes.len()], Status::NotFound)
        }
        fn store(&self, _: Arc<NodeObject>) -> Result<(), String> {
            Ok(())
        }
        fn store_batch(&self, _: &crate::Batch) {}
        fn store_batch_result(&self, batch: &crate::Batch) -> Result<(), String> {
            *self.batch.lock().expect("captured batch mutex") = batch.clone();
            Ok(())
        }
        fn sync(&self) {}
        fn for_each(&self, _: &mut dyn FnMut(Arc<NodeObject>)) {}
        fn get_write_load(&self) -> i32 {
            0
        }
        fn set_delete_path(&self) {}
        fn fd_required(&self) -> i32 {
            0
        }
    }

    struct TerminalTicket(Arc<AtomicUsize>);

    impl Drop for TerminalTicket {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::AcqRel);
        }
    }

    struct TerminalWriteWork {
        ticket: TerminalTicket,
        payload: Vec<u8>,
    }

    impl PersistenceWork for TerminalWriteWork {
        fn retained_payload_bytes(&self) -> usize {
            self.payload.capacity()
        }

        fn run(self: Box<Self>) {
            drop(self);
        }
    }

    #[test]
    fn database_trait_forwards_store_generation_and_rejected_write_once() {
        let attempts = Arc::new(AtomicUsize::new(0));
        let database: Arc<dyn DatabaseTrait> = DatabaseNodeImp::new(
            Arc::new(RejectingScheduler {
                attempts: Arc::clone(&attempts),
            }),
            1,
            Arc::new(EmptyBackend),
            &Section::new("node_db"),
            Arc::new(NullJournal),
        )
        .expect("database node adapter");
        let terminal = Arc::new(AtomicUsize::new(0));
        let ticket = TerminalTicket(Arc::clone(&terminal));

        assert_eq!(
            database.store_generation(),
            1,
            "the Database trait must forward the runtime's initial nonzero store generation"
        );
        database.schedule_write(Box::new(TerminalWriteWork {
            ticket,
            payload: Vec::with_capacity(1),
        }));

        assert_eq!(
            attempts.load(Ordering::Acquire),
            1,
            "the adapter must forward the write to the real runtime scheduler"
        );
        assert_eq!(
            terminal.load(Ordering::Acquire),
            1,
            "a rejected scheduler task must terminally release its write owner exactly once"
        );
        database.stop();
        assert_eq!(
            terminal.load(Ordering::Acquire),
            1,
            "stop must not redeliver an already rejected write owner"
        );
    }

    #[test]
    fn failed_checked_batch_does_not_publish_store_bookkeeping() {
        let database = DatabaseNodeImp::new(
            Arc::new(RejectingScheduler {
                attempts: Arc::new(AtomicUsize::new(0)),
            }),
            1,
            Arc::new(FailingBatchBackend),
            &Section::new("node_db"),
            Arc::new(NullJournal),
        )
        .expect("database node adapter");
        let objects = vec![
            (
                NodeObjectType::AccountNode,
                vec![1, 2],
                Uint256::from_array([1; 32]),
                1,
            ),
            (
                NodeObjectType::TransactionNode,
                vec![3, 4],
                Uint256::from_array([2; 32]),
                1,
            ),
        ];

        assert_eq!(
            database.store_batch(objects),
            Err("injected batch failure".to_owned())
        );
        assert_eq!(database.get_store_count(), 0);
        assert_eq!(database.get_store_size(), 0);
    }

    #[test]
    fn checked_batch_deduplicates_conflicting_hashes_first_wins() {
        let captured = Arc::new(Mutex::new(Vec::new()));
        let database = DatabaseNodeImp::new(
            Arc::new(RejectingScheduler {
                attempts: Arc::new(AtomicUsize::new(0)),
            }),
            1,
            Arc::new(CapturingBatchBackend {
                batch: Arc::clone(&captured),
            }),
            &Section::new("node_db"),
            Arc::new(NullJournal),
        )
        .expect("database node adapter");
        let hash = Uint256::from_array([0x51; 32]);
        database
            .store_batch(vec![
                (NodeObjectType::AccountNode, vec![1, 2], hash, 10),
                (NodeObjectType::TransactionNode, vec![9, 9, 9], hash, 11),
            ])
            .expect("deduplicated batch");

        let batch = captured.lock().expect("captured batch mutex");
        assert_eq!(batch.len(), 1);
        assert_eq!(batch[0].object_type(), NodeObjectType::AccountNode);
        assert_eq!(batch[0].data(), &[1, 2]);
        assert_eq!(database.get_store_count(), 1);
        assert_eq!(database.get_store_size(), 2);
    }
}
