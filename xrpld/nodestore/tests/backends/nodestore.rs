use basics::base_uint::Uint256;
use basics::basic_config::Section;
use nodestore::{
    AsyncReadWork, BATCH_WRITE_PREALLOCATION_SIZE, Backend, DatabaseDelegate, DatabaseRotatingImp,
    DatabaseRuntime, DatabaseSource, DecodedBlob, DummyScheduler, EncodedBlob, Factory,
    FetchReport, JournalLevel, Manager, ManagerImp, MemoryFactory, NodeObject, NodeObjectType,
    NodeStoreJournal, NullJournal, Status, filter_inner, nodeobject_compress,
    nodeobject_decompress,
};
use protocol::hash_prefix::HashPrefix;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc;
use std::time::Duration;

fn config(path: &str) -> Section {
    let mut section = Section::new("node_db");
    section.set("type", "Memory");
    section.set("path", path);
    section
}

fn hash(byte: u8) -> Uint256 {
    Uint256::from_array([byte; 32])
}

fn import_hash(index: usize) -> Uint256 {
    let mut bytes = [0u8; 32];
    bytes[..8].copy_from_slice(&(index as u64).to_be_bytes());
    Uint256::from_array(bytes)
}

#[derive(Default)]
struct NoopJournal;

impl NodeStoreJournal for NoopJournal {
    fn log(&self, _level: JournalLevel, _message: &str) {}
}

struct ImportDelegate;

impl DatabaseDelegate for ImportDelegate {
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
        None
    }
}

struct ImportSource {
    objects: Vec<Arc<NodeObject>>,
}

impl DatabaseSource for ImportSource {
    fn for_each(&self, callback: &mut dyn FnMut(Arc<NodeObject>)) {
        for object in &self.objects {
            callback(Arc::clone(object));
        }
    }
}

struct FailingBatchBackend {
    calls: AtomicUsize,
    batch_lengths: Mutex<Vec<usize>>,
}

impl Default for FailingBatchBackend {
    fn default() -> Self {
        Self {
            calls: AtomicUsize::new(0),
            batch_lengths: Mutex::new(Vec::new()),
        }
    }
}

impl Backend for FailingBatchBackend {
    fn get_name(&self) -> String {
        "failing".to_owned()
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
        (vec![None; hashes.len()], Status::Ok)
    }

    fn store(&self, _object: Arc<NodeObject>) -> Result<(), String> {
        Ok(())
    }

    fn store_batch(&self, batch: &nodestore::Batch) {
        let call = self.calls.fetch_add(1, Ordering::Relaxed);
        self.batch_lengths
            .lock()
            .expect("batch lengths mutex")
            .push(batch.len());
        if call == 0 {
            panic!("storeBatch failed");
        }
    }

    fn store_batch_result(&self, batch: &nodestore::Batch) -> Result<(), String> {
        // `import_internal` writes through the checked batch API, so the
        // recording and first-call failure injection live here (mirroring the
        // reference importInternal contract). The first attempt panics so the
        // importer must preserve the batch and retry it intact; the retry then
        // includes one additional accumulated object.
        let call = self.calls.fetch_add(1, Ordering::Relaxed);
        self.batch_lengths
            .lock()
            .expect("batch lengths mutex")
            .push(batch.len());
        if call == 0 {
            panic!("storeBatch failed");
        }
        Ok(())
    }

    fn sync(&self) {}

    fn sync_result(&self) -> Result<(), String> {
        Err("injected sync failure".to_owned())
    }

    fn for_each(&self, _callback: &mut dyn FnMut(Arc<NodeObject>)) {}

    fn get_write_load(&self) -> i32 {
        0
    }

    fn set_delete_path(&self) {}

    fn fd_required(&self) -> i32 {
        0
    }
}

#[test]
fn checked_sync_exposes_backend_durability_failure() {
    let backend = FailingBatchBackend::default();
    assert_eq!(
        backend.sync_result(),
        Err("injected sync failure".to_owned()),
        "lifecycle owners must be able to reject a failed final durability barrier"
    );
}

#[test]
fn manager_and_factory_lookup_are_case_insensitive() {
    let manager = ManagerImp::new();
    assert!(manager.find("memory").is_some());
    assert!(manager.find("MeMoRy").is_some());
    assert!(manager.find("MEMORY").is_some());
    assert!(manager.find("none").is_some());
    assert_eq!(
        manager
            .find("NuDB")
            .expect("NuDB factory should remain available")
            .get_name(),
        "NuDB"
    );
    assert_eq!(
        manager
            .find("rocksdb")
            .expect("rocksdb factory should remain available")
            .get_name(),
        "RocksDB"
    );
}

#[test]
fn memory_backend_store_fetch_and_batch_match_cpp_behavior() {
    let factory = MemoryFactory::new();
    let scheduler: Arc<dyn nodestore::Scheduler> = Arc::new(DummyScheduler);
    let journal: Arc<dyn nodestore::NodeStoreJournal> = Arc::new(NullJournal);
    let backend = factory
        .create_instance(
            NodeObject::KEY_BYTES,
            &config("mem-a"),
            0,
            scheduler,
            journal,
        )
        .expect("memory backend must be created");
    backend.open(true).expect("memory backend must open");

    let first = NodeObject::create_object(NodeObjectType::Ledger, vec![1, 2, 3], hash(0x11));
    let duplicate = NodeObject::create_object(NodeObjectType::Ledger, vec![9, 9, 9], hash(0x11));
    let second = NodeObject::create_object(NodeObjectType::TransactionNode, vec![4, 5], hash(0x22));

    backend.store(Arc::clone(&first));
    backend.store(duplicate);
    backend.store(Arc::clone(&second));

    let (fetched, status) = backend.fetch(first.hash());
    assert_eq!(status, nodestore::Status::Ok);
    let fetched = fetched.expect("stored object must be found");
    assert_eq!(fetched.data(), &[1, 2, 3]);

    let (batch, batch_status) = backend.fetch_batch(&[hash(0x11), hash(0x22), hash(0x33)]);
    assert_eq!(batch_status, nodestore::Status::Ok);
    assert_eq!(batch.len(), 3);
    assert_eq!(
        batch[0]
            .as_ref()
            .expect("first batch item must exist")
            .data(),
        &[1, 2, 3]
    );
    assert_eq!(
        batch[1]
            .as_ref()
            .expect("second batch item must exist")
            .data(),
        &[4, 5]
    );
    assert!(batch[2].is_none());

    backend.close().expect("memory backend close must succeed");
}

#[test]
fn memory_backend_named_paths_reopen_same_db_but_reject_concurrent_open() {
    let factory = MemoryFactory::new();
    let scheduler: Arc<dyn nodestore::Scheduler> = Arc::new(DummyScheduler);
    let journal: Arc<dyn nodestore::NodeStoreJournal> = Arc::new(NullJournal);
    let backend_a = factory
        .create_instance(
            NodeObject::KEY_BYTES,
            &config("Case/Path"),
            0,
            Arc::clone(&scheduler),
            Arc::clone(&journal),
        )
        .expect("memory backend must be created");
    let backend_b = factory
        .create_instance(
            NodeObject::KEY_BYTES,
            &config("case/path"),
            0,
            scheduler,
            journal,
        )
        .expect("memory backend must be created");

    backend_a.open(true).expect("first open must succeed");
    assert_eq!(
        backend_b
            .open(true)
            .expect_err("concurrent named open must fail"),
        "already open"
    );

    let object = NodeObject::create_object(NodeObjectType::Ledger, vec![5, 6, 7], hash(0x55));
    backend_a.store(Arc::clone(&object));
    backend_a.close().expect("close must succeed");

    backend_b.open(true).expect("reopen must succeed");
    let (fetched, status) = backend_b.fetch(object.hash());
    assert_eq!(status, nodestore::Status::Ok);
    assert_eq!(
        fetched
            .expect("reopened named database should retain data")
            .data(),
        object.data()
    );
}

#[test]
fn encoded_and_decoded_blob_match_legacy_format() {
    let object = NodeObject::create_object(
        NodeObjectType::AccountNode,
        vec![0xAA, 0xBB, 0xCC],
        hash(0x44),
    );
    let encoded = EncodedBlob::new(&object);

    assert_eq!(encoded.get_size(), 12);
    assert_eq!(&encoded.get_data()[..8], &[0; 8]);
    assert_eq!(encoded.get_data()[8], NodeObjectType::AccountNode as u8);
    assert_eq!(&encoded.get_data()[9..], &[0xAA, 0xBB, 0xCC]);
    assert_eq!(encoded.get_key(), &[0x44; 32]);

    let decoded = DecodedBlob::new(encoded.get_key(), encoded.get_data());
    assert!(decoded.was_ok());
    let recreated = decoded.create_object();
    assert_eq!(recreated.object_type(), NodeObjectType::AccountNode);
    assert_eq!(recreated.hash(), &hash(0x44));
    assert_eq!(recreated.data(), &[0xAA, 0xBB, 0xCC]);
}

#[test]
fn codec_round_trip_matches_inner_node_filtering_behavior() {
    let mut inner = vec![0u8; 525];
    inner[8] = NodeObjectType::Ledger as u8;
    inner[9..13].copy_from_slice(&HashPrefix::InnerNode.as_u32().to_be_bytes());
    inner[13..45].copy_from_slice(&[0x10; 32]);
    inner[13 + 5 * 32..13 + 6 * 32].copy_from_slice(&[0x60; 32]);

    let compressed = nodeobject_compress(&inner).expect("inner node compression must succeed");
    let decoded = nodeobject_decompress(&compressed).expect("inner node decompression must work");

    filter_inner(&mut inner);
    assert_eq!(decoded, inner);
}

#[test]
fn import_internal_keeps_the_batch_intact_after_a_failed_store_batch() {
    let scheduler: Arc<dyn nodestore::Scheduler> = Arc::new(DummyScheduler);
    let journal: Arc<dyn NodeStoreJournal> = Arc::new(NoopJournal);
    let database = DatabaseRuntime::new(
        Arc::new(ImportDelegate),
        Arc::clone(&scheduler),
        1,
        &Section::new("node_db"),
        Arc::clone(&journal),
    )
    .expect("database must be created");

    let source = ImportSource {
        objects: (0..=BATCH_WRITE_PREALLOCATION_SIZE)
            .map(|index| {
                NodeObject::create_object(
                    NodeObjectType::Ledger,
                    vec![(index & 0xff) as u8],
                    import_hash(index),
                )
            })
            .collect(),
    };
    let backend = Arc::new(FailingBatchBackend::default());

    database.import_internal(backend.as_ref(), &source);

    assert_eq!(
        *backend.batch_lengths.lock().expect("batch lengths mutex"),
        vec![
            BATCH_WRITE_PREALLOCATION_SIZE,
            BATCH_WRITE_PREALLOCATION_SIZE + 1,
        ]
    );

    database.stop();
}

struct BlobChannelReadWork {
    sender: mpsc::Sender<Option<Vec<u8>>>,
    panic_after_send: bool,
}

impl AsyncReadWork for BlobChannelReadWork {
    fn complete(&mut self, object: Option<Arc<NodeObject>>) {
        self.sender
            .send(object.map(|node| node.data().clone()))
            .expect("typed async read channel send must succeed");
        if self.panic_after_send {
            panic!("async fetch work panic");
        }
    }
}

#[test]
fn database_async_fetch_uses_backend_object_and_updates_metrics() {
    let manager = ManagerImp::new();
    let scheduler: Arc<dyn nodestore::Scheduler> = Arc::new(DummyScheduler);
    let journal = Arc::new(NullJournal);
    let database = manager
        .make_database(0, scheduler, 1, &config("db-a"), journal)
        .expect("database must be created");

    let item_hash = hash(0x77);
    database.store(NodeObjectType::Ledger, vec![7, 7, 7], item_hash, 1);
    let sync_fetched = database
        .fetch_node_object(&item_hash, 1, nodestore::FetchType::Synchronous, false)
        .expect("sync fetch must succeed");
    assert_eq!(sync_fetched.data(), &[7, 7, 7]);

    let (tx, rx) = mpsc::channel();
    database.async_fetch(
        item_hash,
        1,
        Box::new(BlobChannelReadWork {
            sender: tx,
            panic_after_send: false,
        }),
    );
    let async_fetched = rx
        .recv_timeout(Duration::from_secs(2))
        .expect("async fetch must complete")
        .expect("async object must exist");
    assert_eq!(async_fetched, vec![7, 7, 7]);
    assert!(database.get_fetch_total_count() >= 2);
    assert!(database.get_fetch_hit_count() >= 2);

    database.stop();
}

#[test]
fn database_async_fetch_isolates_a_panicking_callback_from_others() {
    // A callback that panics must not abort delivery of other queued callbacks
    // for the same hash. The worker catches and logs each callback panic
    // individually (see deliver_async_work), so a faulty consumer cannot starve
    // or drop unrelated async reads. This is the intended robustness contract.
    let manager = ManagerImp::new();
    let scheduler: Arc<dyn nodestore::Scheduler> = Arc::new(DummyScheduler);
    let journal = Arc::new(NullJournal);
    let database = manager
        .make_database(0, scheduler, 1, &config("db-panic"), journal)
        .expect("database must be created");

    let item_hash = hash(0x88);
    database.store(NodeObjectType::Ledger, vec![8, 8, 8], item_hash, 1);

    let (first_tx, first_rx) = mpsc::channel();
    let (second_tx, second_rx) = mpsc::channel();
    database.async_fetch(
        item_hash,
        1,
        Box::new(BlobChannelReadWork {
            sender: first_tx,
            panic_after_send: true,
        }),
    );
    database.async_fetch(
        item_hash,
        1,
        Box::new(BlobChannelReadWork {
            sender: second_tx,
            panic_after_send: false,
        }),
    );

    assert_eq!(
        first_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("first callback must run")
            .expect("first callback object must exist"),
        vec![8, 8, 8]
    );
    // The second callback must still run: the first callback's panic is caught
    // and isolated, not allowed to swallow subsequent deliveries.
    assert_eq!(
        second_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("second callback must still run after the first panicked")
            .expect("second callback object must exist"),
        vec![8, 8, 8]
    );

    database.stop();
}

#[test]
fn rotating_database_duplicates_archive_hits_and_rotates_backend_names() {
    let manager = ManagerImp::new();
    let scheduler: Arc<dyn nodestore::Scheduler> = Arc::new(DummyScheduler);
    let journal: Arc<dyn nodestore::NodeStoreJournal> = Arc::new(NullJournal);

    let writable_config = config("rotating-writable");
    let archive_config = config("rotating-archive");
    let writable_backend: Arc<dyn nodestore::Backend> = Arc::from(
        manager
            .make_backend(
                &writable_config,
                0,
                Arc::clone(&scheduler),
                Arc::clone(&journal),
            )
            .expect("writable backend"),
    );
    writable_backend.open(true).expect("writable open");

    let archive_backend: Arc<dyn nodestore::Backend> = Arc::from(
        manager
            .make_backend(
                &archive_config,
                0,
                Arc::clone(&scheduler),
                Arc::clone(&journal),
            )
            .expect("archive backend"),
    );
    archive_backend.open(true).expect("archive open");

    let rotating = DatabaseRotatingImp::new(
        Arc::clone(&scheduler),
        1,
        Arc::clone(&writable_backend),
        Arc::clone(&archive_backend),
        &writable_config,
        Arc::clone(&journal),
    )
    .expect("rotating database");

    let item = NodeObject::create_object(NodeObjectType::Ledger, vec![9, 8, 7], hash(0xAA));
    archive_backend.store(Arc::clone(&item));

    let fetched = rotating
        .fetch_node_object(item.hash(), 0, nodestore::FetchType::Synchronous, true)
        .expect("archive fetch");
    assert_eq!(fetched.data(), &[9, 8, 7]);
    assert_eq!(
        writable_backend
            .fetch(item.hash())
            .0
            .expect("writable duplicate")
            .data(),
        &[9, 8, 7]
    );

    let mut next_config = config("rotating-next");
    next_config.set("path", "rotating-next");
    let new_backend = manager
        .make_backend(
            &next_config,
            0,
            Arc::clone(&scheduler),
            Arc::clone(&journal),
        )
        .expect("next backend");
    new_backend.open(true).expect("next open");
    let callback = Arc::new(std::sync::Mutex::new(None));
    let seen = Arc::clone(&callback);
    rotating.rotate(new_backend, move |writable_name, archive_name| {
        *seen.lock().expect("callback mutex") =
            Some((writable_name.to_owned(), archive_name.to_owned()));
    });

    assert_eq!(rotating.get_name(), "rotating-next");
    assert_eq!(
        callback.lock().expect("callback mutex").clone(),
        Some(("rotating-next".to_owned(), "rotating-writable".to_owned()))
    );

    rotating.stop();
}
