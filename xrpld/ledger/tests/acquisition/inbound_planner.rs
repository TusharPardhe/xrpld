use basics::base_uint::Uint256;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{
    Ledger, LedgerHeader, needed_hashes_with_family, needed_hashes_with_family_and_first_child,
};
use parking_lot::Mutex;
use shamap::family::{MissingNodeReporter, NullFullBelowCache, SHAMapFamily, SHAMapNodeFetcher};
use shamap::fetch::SHAMapSyncFilter;
use shamap::item::SHAMapItem;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use shamap::tree_node_cache::TreeNodeCache;
use std::collections::HashMap;
use std::sync::Arc;
use time::Duration;

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

fn sample_uint256(fill: u8) -> Uint256 {
    Uint256::from_array([fill; 32])
}

#[derive(Debug, Default)]
struct RecordingFetcher {
    expected: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
    fetches: Mutex<Vec<SHAMapHash>>,
}

impl SHAMapNodeFetcher for RecordingFetcher {
    fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        self.fetches.lock().push(hash);
        self.expected.get(&hash).cloned()
    }
}

#[derive(Debug, Default)]
struct RecordingMissingNodeReporter {
    by_seq: Vec<(u32, Uint256)>,
}

#[derive(Debug)]
struct SharedReporter(Arc<Mutex<RecordingMissingNodeReporter>>);

impl MissingNodeReporter for SharedReporter {
    fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
        self.0.lock().by_seq.push((ref_num, node_hash));
    }

    fn missing_node_acquire_by_hash(&self, _ref_hash: Uint256, _ref_num: u32) {}
}

#[test]
fn needed_hashes_returns_root_when_loaded_map_hash_is_zero() {
    let root = sample_hash(0xA1);
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "needed-hashes-root",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(18),
        RecordingFetcher::default(),
        SharedReporter(reporter.clone()),
    );
    let mut map = SyncTree::new_with_type(SHAMapType::State, true, 900);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    let needed = needed_hashes_with_family(root, &mut map, 8, &mut no_filter, &family);

    assert_eq!(needed, vec![*root.as_uint256()]);
    family.with_fetcher(|fetcher| assert!(fetcher.fetches.lock().is_empty()));
    assert!(reporter.lock().by_seq.is_empty());
}

#[test]
fn needed_state_hashes_returns_empty_for_zero_root() {
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "needed-state-zero-root",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(18),
        RecordingFetcher::default(),
        SharedReporter(reporter.clone()),
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 901,
            account_hash: SHAMapHash::default(),
            ..LedgerHeader::default()
        },
        SyncTree::new_with_type(SHAMapType::State, true, 901),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 901),
    );
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    let needed = ledger.needed_state_hashes_with_family(8, &mut no_filter, &family);

    assert!(needed.is_empty());
    family.with_fetcher(|fetcher| assert!(fetcher.fetches.lock().is_empty()));
    assert!(reporter.lock().by_seq.is_empty());
}

#[test]
fn needed_state_hashes_returns_missing_child_hashes_in_scan_order() {
    let missing_a = sample_hash(0xB1);
    let missing_b = sample_hash(0xB2);
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, missing_a);
    root.set_child_hash(10, missing_b);
    root.update_hash();

    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "needed-state-missing",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(18),
        RecordingFetcher::default(),
        SharedReporter(reporter.clone()),
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 902,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            root.clone(),
            SHAMapType::State,
            true,
            902,
            SyncState::Synching,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 902),
    );
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    let needed = needed_hashes_with_family_and_first_child(
        root.get_hash(),
        ledger.state_map_mut(),
        8,
        &mut no_filter,
        &family,
        &mut || 10,
    );

    assert_eq!(
        needed,
        vec![*missing_b.as_uint256(), *missing_a.as_uint256()]
    );
    // Each unresolved child is resolved once at deferred completion; the
    // request frontier remains in randomized scan order.
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![missing_b, missing_a]);
    });
    // A deferred backing-store miss is represented by the peer frontier; it
    // does not emit an owner-level synchronous local-miss report.
    assert!(reporter.lock().by_seq.is_empty());
}

#[test]
fn needed_tx_hashes_clears_synching_when_tree_is_complete() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x44), vec![0x55; 16]),
        0,
    );
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "needed-tx-complete",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(18),
        RecordingFetcher::default(),
        SharedReporter(reporter.clone()),
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 903,
            tx_hash: tx_root.get_hash(),
            ..LedgerHeader::default()
        },
        SyncTree::new_with_type(SHAMapType::State, true, 903),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            903,
            SyncState::Synching,
        ),
    );
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    let needed = ledger.needed_tx_hashes_with_family(8, &mut no_filter, &family);

    assert!(needed.is_empty());
    assert_eq!(ledger.tx_map().state(), SyncState::Modifying);
    family.with_fetcher(|fetcher| assert!(fetcher.fetches.lock().is_empty()));
    assert!(reporter.lock().by_seq.is_empty());
}

#[test]
fn needed_state_hashes_stays_empty_when_complete_subtree_is_only_in_backed_fetch_path() {
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x91), vec![0xA5; 16]),
        0,
    );
    let fetched_inner = SHAMapTreeNode::new_inner(1);
    fetched_inner.set_child_hash(4, leaf.get_hash());
    fetched_inner.share_child(4, &leaf);
    fetched_inner.update_hash_deep();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(7, fetched_inner.get_hash());
    root.update_hash();

    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let mut fetcher = RecordingFetcher::default();
    fetcher
        .expected
        .insert(fetched_inner.get_hash(), fetched_inner);
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "needed-state-backed-complete",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(19),
        fetcher,
        SharedReporter(reporter.clone()),
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 904,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            root.clone(),
            SHAMapType::State,
            true,
            904,
            SyncState::Synching,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 904),
    );
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    let first = ledger.needed_state_hashes_with_family(8, &mut no_filter, &family);
    let second = ledger.needed_state_hashes_with_family(8, &mut no_filter, &family);

    assert!(first.is_empty());
    assert!(second.is_empty());
    assert_eq!(ledger.state_map().state(), SyncState::Modifying);
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![root.get_child_hash(7)])
    });
    assert!(reporter.lock().by_seq.is_empty());
}
