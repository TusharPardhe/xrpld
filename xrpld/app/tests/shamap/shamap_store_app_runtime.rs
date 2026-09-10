use app::{
    LedgerMasterCloseTimeProvider, NetworkOpsOperatingMode, NullSHAMapStoreCopyRuntime,
    SHAMAP_STORE_COPY_CHECK_HEALTH_INTERVAL, SHAMapStoreAppRuntime, SHAMapStoreCloseTimeProvider,
    SHAMapStoreComponentRuntime, SHAMapStoreCopyDisposition, SHAMapStoreHealthPolicy,
    SHAMapStoreHealthRuntime, SHAMapStoreLedgerRuntime, SHAMapStoreNodeFamilyCacheRuntime,
    SHAMapStoreNodeStoreRuntime, SHAMapStoreOperatingMode, SHAMapStoreRotatingBackendFactory,
    SHAMapStoreRuntime, SHAMapStoreTransactionCacheRuntime, SharedLedgerMasterState,
    SharedNetworkOpsState, SharedSHAMapStoreHealthState, ValidatedLedgerCopyRuntime,
};
use basics::base_uint::Uint256;
use basics::intrusive_pointer::make_shared_intrusive;
use basics::sha_map_hash::SHAMapHash;
use ledger::{Ledger, LedgerHeader};
use nodestore::{Backend, Batch, NodeObject, Status};
use shamap::item::SHAMapItem;
use shamap::mutation::MutableTree;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::traversal::TraversalError;
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

#[derive(Default)]
struct RecordingLedger {
    events: Mutex<Vec<String>>,
}

impl SHAMapStoreLedgerRuntime for RecordingLedger {
    fn clear_prior_ledgers(&self, last_rotated: u32) {
        self.events
            .lock()
            .expect("events mutex must not be poisoned")
            .push(format!("clear-prior:{last_rotated}"));
    }

    fn clear_online_delete_caches(&self, validated_seq: u32) {
        self.events
            .lock()
            .expect("events mutex must not be poisoned")
            .push(format!("clear-caches:{validated_seq}"));
    }
}

struct RecordingNodeFamily {
    keys: Vec<Uint256>,
    cleared: Mutex<usize>,
}

impl SHAMapStoreNodeFamilyCacheRuntime for RecordingNodeFamily {
    fn tree_node_cache_keys(&self) -> Vec<Uint256> {
        self.keys.clone()
    }

    fn clear_full_below_cache(&self) {
        *self
            .cleared
            .lock()
            .expect("cleared mutex must not be poisoned") += 1;
    }

    fn visit_state_map_nodes(
        &self,
        ledger: &Ledger,
        visit: &mut dyn FnMut(
            &basics::memory::intrusive_pointer::SharedIntrusive<shamap::tree_node::SHAMapTreeNode>,
        ) -> bool,
    ) -> Result<(), TraversalError> {
        ledger
            .state_map()
            .visit_nodes(&mut |_| None, &mut |node| visit(node))
    }
}

struct RecordingTransactions {
    keys: Vec<Uint256>,
}

impl SHAMapStoreTransactionCacheRuntime for RecordingTransactions {
    fn cache_keys(&self) -> Vec<Uint256> {
        self.keys.clone()
    }
}

#[derive(Default)]
struct RecordingNodeStore {
    fetches: Mutex<Vec<Uint256>>,
}

impl SHAMapStoreNodeStoreRuntime for RecordingNodeStore {
    fn fetch_node_object(&self, hash: &Uint256, _ledger_seq: u32) -> bool {
        self.fetches
            .lock()
            .expect("fetches mutex must not be poisoned")
            .push(*hash);
        true
    }

    fn rotate_with(&self, new_backend: Box<dyn Backend>) -> (String, String) {
        (new_backend.get_name(), "archive.prev".to_owned())
    }
}

struct TestBackend(&'static str);

impl Backend for TestBackend {
    fn get_name(&self) -> String {
        self.0.to_owned()
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
        (Vec::new(), Status::NotFound)
    }

    fn store(&self, _object: Arc<NodeObject>) -> Result<(), String> {
        Ok(())
    }

    fn store_batch(&self, _batch: &Batch) {}

    fn sync(&self) {}

    fn for_each(&self, _callback: &mut dyn FnMut(Arc<NodeObject>)) {}

    fn get_write_load(&self) -> i32 {
        0
    }

    fn set_delete_path(&self) {}

    fn fd_required(&self) -> i32 {
        1
    }
}

#[derive(Debug)]
struct RecordingFactory;

impl SHAMapStoreRotatingBackendFactory for RecordingFactory {
    fn make_backend(&self) -> Result<Box<dyn Backend>, String> {
        Ok(Box::new(TestBackend("writable.next")))
    }
}

#[derive(Debug)]
struct FixedCloseTimeProvider {
    now_close_time: AtomicU32,
}

impl FixedCloseTimeProvider {
    fn new(now_close_time: u32) -> Self {
        Self {
            now_close_time: AtomicU32::new(now_close_time),
        }
    }
}

impl SHAMapStoreCloseTimeProvider for FixedCloseTimeProvider {
    fn current_close_time(&self) -> u32 {
        self.now_close_time.load(Ordering::Acquire)
    }
}

impl LedgerMasterCloseTimeProvider for FixedCloseTimeProvider {
    fn current_close_time(&self) -> u32 {
        self.now_close_time.load(Ordering::Acquire)
    }
}

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

fn uint256_from_u32(value: u32) -> Uint256 {
    let mut bytes = [0u8; 32];
    bytes[28..].copy_from_slice(&value.to_be_bytes());
    Uint256::from_array(bytes)
}

fn build_state_ledger(
    keys: impl IntoIterator<Item = Uint256>,
    seq: u32,
    backed: bool,
) -> Arc<Ledger> {
    let mut tree = MutableTree::new(seq.max(1));
    for key in keys {
        tree.add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![0x11; 20]),
        )
        .expect("state item insertion should succeed");
    }

    Arc::new(Ledger::from_maps(
        LedgerHeader {
            seq,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            tree.root(),
            SHAMapType::State,
            backed,
            seq,
            SyncState::Immutable,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, backed, seq),
    ))
}

#[test]
fn shamap_store_app_runtime_preserves_cache_freshen_and_clear_order() {
    let ledger: Arc<RecordingLedger> = Arc::default();
    let node_family = Arc::new(RecordingNodeFamily {
        keys: vec![
            Uint256::from_array([0x11; 32]),
            Uint256::from_array([0x22; 32]),
        ],
        cleared: Mutex::new(0),
    });
    let transactions = Arc::new(RecordingTransactions {
        keys: vec![Uint256::from_array([0x33; 32])],
    });
    let node_store: Arc<RecordingNodeStore> = Arc::default();

    let mut runtime = SHAMapStoreAppRuntime::new(
        ledger.clone(),
        node_family.clone(),
        transactions,
        node_store.clone(),
        Arc::new(RecordingFactory),
        None,
        Arc::new(NullSHAMapStoreCopyRuntime),
    );

    runtime.freshen_caches().expect("freshen");
    runtime.clear_caches(1156).expect("clear caches");

    assert_eq!(
        *node_store
            .fetches
            .lock()
            .expect("fetches mutex must not be poisoned"),
        vec![
            Uint256::from_array([0x11; 32]),
            Uint256::from_array([0x22; 32]),
            Uint256::from_array([0x33; 32]),
        ]
    );
    assert_eq!(
        *ledger
            .events
            .lock()
            .expect("events mutex must not be poisoned"),
        vec!["clear-caches:1156".to_owned()]
    );
    assert_eq!(
        *node_family
            .cleared
            .lock()
            .expect("cleared mutex must not be poisoned"),
        1
    );
}

#[test]
fn shamap_store_app_runtime_tracks_health_and_rotates_prepared_backend() {
    let mut runtime = SHAMapStoreAppRuntime::new(
        Arc::new(RecordingLedger::default()),
        Arc::new(RecordingNodeFamily {
            keys: Vec::new(),
            cleared: Mutex::new(0),
        }),
        Arc::new(RecordingTransactions { keys: Vec::new() }),
        Arc::new(RecordingNodeStore::default()),
        Arc::new(RecordingFactory),
        None,
        Arc::new(NullSHAMapStoreCopyRuntime),
    );

    runtime.set_operating_mode(SHAMapStoreOperatingMode::Full);
    runtime.set_validated_ledger_age(Duration::from_secs(3));
    runtime.start_background_work();
    runtime.prepare_rotation().expect("prepare");
    let result = runtime.rotate_backends().expect("rotate");
    runtime.stop_background_work();

    assert_eq!(
        result,
        ("writable.next".to_owned(), "archive.prev".to_owned())
    );
    assert!(runtime.is_stopping());
    assert_eq!(runtime.operating_mode(), SHAMapStoreOperatingMode::Full);
    assert_eq!(runtime.validated_ledger_age(), Duration::from_secs(3));
}

#[test]
fn shamap_store_app_runtime_reads_live_health_from_shared_app_state() {
    let close_time = Arc::new(FixedCloseTimeProvider::new(120));
    let health = Arc::new(SharedSHAMapStoreHealthState::new(close_time.clone()));
    let runtime = SHAMapStoreAppRuntime::new_with_health_state(
        Arc::new(RecordingLedger::default()),
        Arc::new(RecordingNodeFamily {
            keys: Vec::new(),
            cleared: Mutex::new(0),
        }),
        Arc::new(RecordingTransactions { keys: Vec::new() }),
        Arc::new(RecordingNodeStore::default()),
        Arc::new(RecordingFactory),
        None,
        Arc::new(NullSHAMapStoreCopyRuntime),
        health.clone(),
    );

    health.set_operating_mode(SHAMapStoreOperatingMode::Full);
    health.note_validated_ledger(Arc::new(Ledger::from_ledger_seq_and_close_time(
        1_156, 100, false,
    )));
    assert_eq!(runtime.operating_mode(), SHAMapStoreOperatingMode::Full);
    assert_eq!(runtime.validated_ledger_age(), Duration::from_secs(20));

    close_time.now_close_time.store(126, Ordering::Release);
    assert_eq!(runtime.validated_ledger_age(), Duration::from_secs(26));
}

#[test]
fn shamap_store_app_runtime_maps_live_network_ops_state_into_health_gate() {
    let close_time = Arc::new(FixedCloseTimeProvider::new(120));
    let network_ops = Arc::new(SharedNetworkOpsState::new(
        NetworkOpsOperatingMode::Disconnected,
    ));
    let health = Arc::new(SharedSHAMapStoreHealthState::new_with_network_ops(
        close_time.clone(),
        network_ops.clone(),
    ));
    let runtime = SHAMapStoreAppRuntime::new_with_health_state(
        Arc::new(RecordingLedger::default()),
        Arc::new(RecordingNodeFamily {
            keys: Vec::new(),
            cleared: Mutex::new(0),
        }),
        Arc::new(RecordingTransactions { keys: Vec::new() }),
        Arc::new(RecordingNodeStore::default()),
        Arc::new(RecordingFactory),
        None,
        Arc::new(NullSHAMapStoreCopyRuntime),
        health,
    );

    assert_eq!(runtime.operating_mode(), SHAMapStoreOperatingMode::Other);

    network_ops.set_operating_mode(NetworkOpsOperatingMode::Tracking);
    assert_eq!(runtime.operating_mode(), SHAMapStoreOperatingMode::Other);

    network_ops.set_operating_mode(NetworkOpsOperatingMode::Full);
    assert_eq!(runtime.operating_mode(), SHAMapStoreOperatingMode::Full);
}

#[test]
fn shamap_store_app_runtime_reads_validated_age_from_shared_ledger_master_state() {
    let close_time = Arc::new(FixedCloseTimeProvider::new(120));
    let network_ops = Arc::new(SharedNetworkOpsState::new(NetworkOpsOperatingMode::Full));
    let ledger_master = Arc::new(SharedLedgerMasterState::new(close_time.clone()));
    let health = Arc::new(SharedSHAMapStoreHealthState::new_with_app_state(
        close_time.clone(),
        network_ops,
        ledger_master.clone(),
    ));
    let runtime = SHAMapStoreAppRuntime::new_with_health_state(
        Arc::new(RecordingLedger::default()),
        Arc::new(RecordingNodeFamily {
            keys: Vec::new(),
            cleared: Mutex::new(0),
        }),
        Arc::new(RecordingTransactions { keys: Vec::new() }),
        Arc::new(RecordingNodeStore::default()),
        Arc::new(RecordingFactory),
        None,
        Arc::new(NullSHAMapStoreCopyRuntime),
        health,
    );

    ledger_master.note_validated_ledger(Arc::new(Ledger::from_ledger_seq_and_close_time(
        1_156, 100, false,
    )));

    assert_eq!(runtime.validated_ledger_age(), Duration::from_secs(20));

    close_time.now_close_time.store(126, Ordering::Release);
    assert_eq!(runtime.validated_ledger_age(), Duration::from_secs(26));
}

#[test]
fn shamap_store_app_runtime_copies_validated_state_map_in_preorder() {
    let ledger = build_state_ledger(
        [
            Uint256::from_array([0x11; 32]),
            Uint256::from_array([0x22; 32]),
            Uint256::from_array([0x33; 32]),
        ],
        1_156,
        false,
    );
    let mut expected = Vec::new();
    ledger
        .state_map()
        .visit_nodes(&mut |_| None, &mut |node| {
            expected.push(*node.get_hash().as_uint256());
            true
        })
        .expect("expected traversal should succeed");

    let node_store: Arc<RecordingNodeStore> = Arc::default();
    let mut runtime = SHAMapStoreAppRuntime::new(
        Arc::new(RecordingLedger::default()),
        Arc::new(RecordingNodeFamily {
            keys: Vec::new(),
            cleared: Mutex::new(0),
        }),
        Arc::new(RecordingTransactions { keys: Vec::new() }),
        node_store.clone(),
        Arc::new(RecordingFactory),
        None,
        Arc::new(ValidatedLedgerCopyRuntime),
    );

    let result = runtime
        .copy_validated_ledger(
            Arc::clone(&ledger),
            SHAMapStoreHealthPolicy {
                age_threshold: Duration::from_secs(60),
                recovery_wait: Duration::from_secs(5),
            },
        )
        .expect("copy should complete");

    assert_eq!(
        result,
        SHAMapStoreCopyDisposition::Completed {
            node_count: expected.len() as u64
        }
    );
    assert_eq!(
        *node_store
            .fetches
            .lock()
            .expect("fetches mutex must not be poisoned"),
        expected
    );
}

#[test]
fn shamap_store_app_runtime_stops_copy_at_health_checkpoint() {
    let ledger = build_state_ledger(
        (0..SHAMAP_STORE_COPY_CHECK_HEALTH_INTERVAL)
            .map(|index| uint256_from_u32(index as u32 + 1)),
        1_156,
        false,
    );
    let node_store: Arc<RecordingNodeStore> = Arc::default();
    let mut runtime = SHAMapStoreAppRuntime::new(
        Arc::new(RecordingLedger::default()),
        Arc::new(RecordingNodeFamily {
            keys: Vec::new(),
            cleared: Mutex::new(0),
        }),
        Arc::new(RecordingTransactions { keys: Vec::new() }),
        node_store.clone(),
        Arc::new(RecordingFactory),
        None,
        Arc::new(ValidatedLedgerCopyRuntime),
    );
    runtime.set_stopping(true);

    let result = runtime
        .copy_validated_ledger(
            Arc::clone(&ledger),
            SHAMapStoreHealthPolicy {
                age_threshold: Duration::from_secs(60),
                recovery_wait: Duration::from_secs(5),
            },
        )
        .expect("copy should stop cleanly");

    assert_eq!(
        result,
        SHAMapStoreCopyDisposition::Stopped {
            node_count: SHAMAP_STORE_COPY_CHECK_HEALTH_INTERVAL
        }
    );
    assert_eq!(
        node_store
            .fetches
            .lock()
            .expect("fetches mutex must not be poisoned")
            .len() as u64,
        SHAMAP_STORE_COPY_CHECK_HEALTH_INTERVAL
    );
}

#[test]
fn shamap_store_app_runtime_surfaces_missing_state_node_without_rotating() {
    let root = SHAMapTreeNode::new_inner(0);
    root.set_child_hash(0, sample_hash(0xAB));
    let ledger = Arc::new(Ledger::from_maps(
        LedgerHeader {
            seq: 1_156,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(root, SHAMapType::State, true, 1_156, SyncState::Immutable),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 1_156),
    ));
    let node_store: Arc<RecordingNodeStore> = Arc::default();
    let mut runtime = SHAMapStoreAppRuntime::new(
        Arc::new(RecordingLedger::default()),
        Arc::new(RecordingNodeFamily {
            keys: Vec::new(),
            cleared: Mutex::new(0),
        }),
        Arc::new(RecordingTransactions { keys: Vec::new() }),
        node_store.clone(),
        Arc::new(RecordingFactory),
        None,
        Arc::new(ValidatedLedgerCopyRuntime),
    );

    let result = runtime
        .copy_validated_ledger(
            Arc::clone(&ledger),
            SHAMapStoreHealthPolicy {
                age_threshold: Duration::from_secs(60),
                recovery_wait: Duration::from_secs(5),
            },
        )
        .expect("copy should report missing node");

    assert_eq!(
        result,
        SHAMapStoreCopyDisposition::MissingNode {
            hash: *sample_hash(0xAB).as_uint256(),
            node_count: 1
        }
    );
    assert_eq!(
        *node_store
            .fetches
            .lock()
            .expect("fetches mutex must not be poisoned"),
        vec![*ledger.state_map().root().get_hash().as_uint256()]
    );
}
