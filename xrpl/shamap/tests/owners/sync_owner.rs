use crate::support::{sample_hash, sample_uint256};
use basics::base_uint::Uint256;
use basics::blob::Blob;
use basics::hardened_hash::HardenedHashBuilder;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use parking_lot::Mutex;
use shamap::compare::Delta;
use shamap::family::{
    FullBelowCache, JournalLevel, MissingNodeReporter, NullFullBelowCache, NullMissingNodeReporter,
    NullNodeFetcher, SHAMapFamily, SHAMapJournal, SHAMapNodeFetcher,
};
use shamap::fetch::SHAMapSyncFilter;
use shamap::item::SHAMapItem;
use shamap::node_id::SHAMapNodeId;
use shamap::node_object::NodeObject;
use shamap::search::NodePathEntry;
use shamap::storage::NodeObjectType;
use shamap::sync::{SHAMapMissingNode, SHAMapType, SyncState, SyncTree};
use shamap::traversal::TraversalError;
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use shamap::tree_node_cache::TreeNodeCache;
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;
use time::Duration;

#[derive(Default)]
struct RecordingFullBelowCache {
    generation: u32,
    known: std::sync::Mutex<BTreeSet<Uint256>>,
    inserted: std::sync::Mutex<Vec<Uint256>>,
}

impl RecordingFullBelowCache {
    fn new(generation: u32) -> Self {
        Self {
            generation,
            known: std::sync::Mutex::new(BTreeSet::new()),
            inserted: std::sync::Mutex::new(Vec::new()),
        }
    }
}

impl FullBelowCache for RecordingFullBelowCache {
    fn generation(&self) -> u32 {
        self.generation
    }

    fn touch_if_exists(&self, hash: Uint256) -> bool {
        self.known.lock().unwrap().contains(&hash)
    }

    fn insert(&self, hash: Uint256) {
        self.known.lock().unwrap().insert(hash);
        self.inserted.lock().unwrap().push(hash);
    }
}

#[derive(Default)]
struct RecordingNodeFetcher {
    expected: Vec<(SHAMapHash, SharedIntrusive<SHAMapTreeNode>)>,
    fetches: Mutex<Vec<SHAMapHash>>,
}

impl RecordingNodeFetcher {
    fn with_leaf(hash: SHAMapHash, leaf: &SHAMapTreeNode) -> Self {
        Self {
            expected: vec![(hash, leaf.clone_with_cowid(0))],
            fetches: Mutex::new(Vec::new()),
        }
    }
}

impl SHAMapNodeFetcher for RecordingNodeFetcher {
    fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        self.fetches.lock().push(hash);
        self.expected
            .iter()
            .find(|(expected_hash, _)| *expected_hash == hash)
            .map(|(_, node)| node.clone())
    }
}

#[derive(Debug, Default)]
struct RecordingJournal {
    entries: Mutex<Vec<(JournalLevel, String)>>,
}

impl RecordingJournal {
    fn entries(&self) -> Vec<(JournalLevel, String)> {
        self.entries.lock().clone()
    }
}

impl SHAMapJournal for RecordingJournal {
    fn log(&self, level: JournalLevel, message: &str) {
        self.entries.lock().push((level, message.to_owned()));
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

#[derive(Debug, Clone, Copy)]
enum BlobFetchMode {
    InvalidBlob,
    Missing,
}

#[derive(Debug)]
struct SharedBlobFetcher(Arc<Mutex<BlobFetchMode>>);

impl SHAMapNodeFetcher for SharedBlobFetcher {
    fn fetch_node_blob(&self, _hash: SHAMapHash) -> Option<Blob> {
        match *self.0.lock() {
            BlobFetchMode::InvalidBlob => Some(vec![0x00, 0xAB, 0xCD]),
            BlobFetchMode::Missing => None,
        }
    }
}

struct RecordingFilter {
    node_blob: Option<Blob>,
    got: Vec<(bool, SHAMapHash, u32, SHAMapNodeType)>,
}

impl SHAMapSyncFilter for RecordingFilter {
    fn got_node(
        &mut self,
        from_filter: bool,
        node_hash: SHAMapHash,
        ledger_seq: u32,
        _node_data: Blob,
        node_type: SHAMapNodeType,
    ) {
        self.got
            .push((from_filter, node_hash, ledger_seq, node_type));
    }

    fn get_node(&mut self, _node_hash: SHAMapHash) -> Option<Blob> {
        self.node_blob.take()
    }
}

fn make_logging_family(
    cache_name: &str,
    journal: Arc<RecordingJournal>,
) -> SHAMapFamily<
    ManualClock,
    HardenedHashBuilder,
    NullFullBelowCache,
    NullNodeFetcher,
    NullMissingNodeReporter,
> {
    SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            cache_name,
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        NullNodeFetcher,
        NullMissingNodeReporter,
        journal,
    )
}

#[test]
fn shamap_sync_tree_add_root_node_with_family_reuses_shared_cache_identity() {
    let key = sample_uint256(0x21);
    let canonical = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![2; 12]),
        0,
    );
    let duplicate = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![2; 12]),
        0,
    );
    let root_wire = duplicate
        .serialize_for_wire()
        .expect("leaf wire serialization should succeed");

    let cache = Arc::new(TreeNodeCache::new(
        "sync-root-cache",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));
    let mut cached = canonical.clone();
    assert!(!cache.canonicalize_replace_client(canonical.get_hash().as_uint256(), &mut cached));

    let family = SHAMapFamily::new(
        cache.clone(),
        NullFullBelowCache::new(1),
        NullNodeFetcher,
        NullMissingNodeReporter,
    );
    let mut tree = SyncTree::new(true, 54);
    tree.set_synching();
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    let result =
        tree.add_root_node_with_family(canonical.get_hash(), &root_wire, &mut no_filter, &family);

    assert!(result.is_useful());
    assert_eq!(tree.state(), SyncState::Modifying);
    let accepted_root = tree.root();
    assert!(std::ptr::eq(&*accepted_root, &*canonical));
    let cached_root = family
        .cache_lookup(canonical.get_hash())
        .expect("family cache should expose the canonicalized root");
    assert!(std::ptr::eq(&*cached_root, &*accepted_root));
}

#[test]
fn shamap_sync_tree_add_known_node_with_family_populates_shared_cache() {
    let key = Uint256::from_hex("3000000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![4; 12]),
        0,
    );
    let raw_leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        leaf.peek_item().expect("leaf should carry an item"),
        0,
        leaf.get_hash(),
    );
    let raw_wire = raw_leaf
        .serialize_for_wire()
        .expect("leaf wire serialization should succeed");

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(3, leaf.get_hash());
    root.update_hash();

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-known-node-cache",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(2),
        NullNodeFetcher,
        NullMissingNodeReporter,
    );
    let mut tree = SyncTree::from_root(root.clone(), true, 55, SyncState::Synching);
    let target = SHAMapNodeId::default()
        .get_child_node_id(3)
        .expect("child id should exist");
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    let result = tree.add_known_node_with_family(target, &raw_wire, &mut no_filter, &family);

    assert!(result.is_useful());
    let attached = root
        .get_child(3)
        .expect("accepted node should attach to the parent branch");
    let cached_leaf = family
        .cache_lookup(leaf.get_hash())
        .expect("family cache should retain the accepted child");
    assert!(std::ptr::eq(&*cached_leaf, &*attached));
}

#[test]
fn shamap_sync_tree_add_root_node_with_family_logs_duplicate_root_trace() {
    let root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x44), vec![1; 12]),
        0,
    );
    let root_wire = root
        .serialize_for_wire()
        .expect("leaf wire serialization should succeed");
    let journal = Arc::new(RecordingJournal::default());
    let family = make_logging_family("sync-root-duplicate-log", journal.clone());
    let mut tree = SyncTree::from_root(root.clone(), true, 70, SyncState::Synching);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    let result =
        tree.add_root_node_with_family(root.get_hash(), &root_wire, &mut no_filter, &family);

    assert!(result.is_good());
    assert!(!result.is_useful());
    assert!(!result.is_invalid());
    assert_eq!(
        journal.entries(),
        vec![(
            JournalLevel::Trace,
            "got root node, already have one".to_owned(),
        )]
    );
}

#[test]
fn shamap_sync_tree_add_known_node_with_family_logs_not_synching_trace() {
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x45), vec![2; 12]),
        0,
    );
    let raw_wire = leaf
        .serialize_for_wire()
        .expect("leaf wire serialization should succeed");
    let journal = Arc::new(RecordingJournal::default());
    let family = make_logging_family("sync-known-not-synching-log", journal.clone());
    let mut tree = SyncTree::new(true, 71);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let target = SHAMapNodeId::default()
        .get_child_node_id(1)
        .expect("child id should exist");

    let result = tree.add_known_node_with_family(target, &raw_wire, &mut no_filter, &family);

    assert!(result.is_good());
    assert!(!result.is_useful());
    assert!(!result.is_invalid());
    assert_eq!(
        journal.entries(),
        vec![(
            JournalLevel::Trace,
            "AddKnownNode while not synching".to_owned(),
        )]
    );
}

#[test]
fn shamap_sync_tree_add_known_node_with_family_logs_empty_branch_warn() {
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x46), vec![3; 12]),
        0,
    );
    let raw_wire = leaf
        .serialize_for_wire()
        .expect("leaf wire serialization should succeed");
    let journal = Arc::new(RecordingJournal::default());
    let family = make_logging_family("sync-known-empty-branch-log", journal.clone());
    let root = SHAMapTreeNode::new_inner(1);
    let mut tree = SyncTree::from_root(root, true, 72, SyncState::Synching);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let target = SHAMapNodeId::default()
        .get_child_node_id(5)
        .expect("child id should exist");

    let result = tree.add_known_node_with_family(target, &raw_wire, &mut no_filter, &family);

    assert!(result.is_invalid());
    let entries = journal.entries();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].0, JournalLevel::Warn);
    assert_eq!(
        entries[0].1,
        format!("Add known node for empty branch{target}")
    );
}

#[test]
fn shamap_sync_tree_add_known_node_with_family_logs_corrupt_node_warn() {
    let expected_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x47), vec![4; 12]),
        0,
    );
    let wrong_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x48), vec![5; 12]),
        0,
    );
    let raw_wire = wrong_leaf
        .serialize_for_wire()
        .expect("leaf wire serialization should succeed");
    let journal = Arc::new(RecordingJournal::default());
    let family = make_logging_family("sync-known-corrupt-log", journal.clone());
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(6, expected_leaf.get_hash());
    root.update_hash();
    let mut tree = SyncTree::from_root(root, true, 73, SyncState::Synching);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let target = SHAMapNodeId::default()
        .get_child_node_id(6)
        .expect("child id should exist");

    let result = tree.add_known_node_with_family(target, &raw_wire, &mut no_filter, &family);

    assert!(result.is_invalid());
    assert_eq!(
        journal.entries(),
        vec![(JournalLevel::Warn, "Corrupt node received".to_owned())]
    );
}

#[test]
fn shamap_sync_tree_add_known_node_with_family_logs_leaf_position_mismatch_debug() {
    let key = Uint256::from_hex("3000000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![6; 12]),
        0,
    );
    let raw_wire = leaf
        .serialize_for_wire()
        .expect("leaf wire serialization should succeed");
    let journal = Arc::new(RecordingJournal::default());
    let family = make_logging_family("sync-known-leaf-position-log", journal.clone());
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(4, leaf.get_hash());
    root.update_hash();
    let mut tree = SyncTree::from_root(root, true, 74, SyncState::Synching);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let target = SHAMapNodeId::default()
        .get_child_node_id(4)
        .expect("child id should exist");
    let expected = SHAMapNodeId::create_id(target.get_depth(), key)
        .expect("expected node id should be derivable from the leaf key");

    let result = tree.add_known_node_with_family(target, &raw_wire, &mut no_filter, &family);

    assert!(result.is_invalid());
    let entries = journal.entries();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].0, JournalLevel::Debug);
    assert_eq!(
        entries[0].1,
        format!(
            "Leaf node position mismatch: expected={}, actual={}",
            expected.get_node_id(),
            target.get_node_id()
        )
    );
}

#[test]
fn shamap_sync_tree_full_gate_survives_invalid_blob_and_reports_only_true_miss_once() {
    let requested = sample_hash(0xA1);
    let journal = Arc::new(RecordingJournal::default());
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let mode = Arc::new(Mutex::new(BlobFetchMode::InvalidBlob));
    let family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "sync-full-gate-invalid-blob",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(16),
        SharedBlobFetcher(mode.clone()),
        SharedReporter(reporter.clone()),
        journal.clone(),
    );
    let mut tree = SyncTree::new_with_type(SHAMapType::State, true, 95);
    tree.set_full();
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    assert!(!tree.fetch_root_with_family(requested, &mut no_filter, &family));
    assert!(tree.is_full());
    assert!(reporter.lock().by_seq.is_empty());
    let entries = journal.entries();
    assert_eq!(entries.len(), 2);
    assert_eq!(entries[0].0, JournalLevel::Trace);
    assert_eq!(entries[0].1, format!("Fetch root STATE node {requested}"));
    assert_eq!(entries[1].0, JournalLevel::Warn);
    assert!(entries[1].1.contains("invalid fetched node blob"));

    *mode.lock() = BlobFetchMode::Missing;

    assert!(!tree.fetch_root_with_family(requested, &mut no_filter, &family));
    assert!(!tree.fetch_root_with_family(requested, &mut no_filter, &family));
    assert!(!tree.is_full());
    let reporter = reporter.lock();
    assert_eq!(reporter.by_seq, vec![(95, *requested.as_uint256())]);
}

#[test]
fn shamap_sync_tree_owner_config_updates_fetch_policy() {
    #[derive(Debug, Default)]
    struct RecordingFetcher {
        fetches: Mutex<Vec<SHAMapHash>>,
    }

    impl SHAMapNodeFetcher for RecordingFetcher {
        fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.fetches.lock().push(hash);
            None
        }
    }

    let requested = sample_hash(0xA2);
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-owner-config",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(17),
        RecordingFetcher::default(),
        SharedReporter(reporter.clone()),
    );
    let mut tree = SyncTree::new_with_type(SHAMapType::State, true, 95);
    tree.set_ledger_seq(205);
    tree.set_full();
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    assert!(!tree.fetch_root_with_family(requested, &mut no_filter, &family));
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![requested]);
    });
    let reporter_state = reporter.lock();
    assert_eq!(reporter_state.by_seq, vec![(205, *requested.as_uint256())]);
    drop(reporter_state);

    tree.set_unbacked();
    assert!(!tree.fetch_root_with_family(requested, &mut no_filter, &family));
    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![requested],
            "set_unbacked should stop later family fetch attempts"
        );
    });
    let reporter_state = reporter.lock();
    assert_eq!(reporter_state.by_seq, vec![(205, *requested.as_uint256())]);
}

#[test]
fn shamap_sync_tree_fetch_root_can_decode_node_objects_with_owner_ledger_seq() {
    #[derive(Debug, Default)]
    struct RecordingObjectFetcher {
        object: Option<NodeObject>,
        fetches: Mutex<Vec<(SHAMapHash, u32)>>,
    }

    impl SHAMapNodeFetcher for RecordingObjectFetcher {
        fn fetch_node_object(&self, hash: SHAMapHash, ledger_seq: u32) -> Option<NodeObject> {
            self.fetches.lock().push((hash, ledger_seq));
            self.object.clone()
        }
    }

    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x52), vec![0x35; 12]),
        0,
    );
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-fetch-root-node-object",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(18),
        RecordingObjectFetcher {
            object: Some(NodeObject::new(
                NodeObjectType::AccountNode,
                leaf.serialize_with_prefix()
                    .expect("leaf should serialize with prefix"),
                *leaf.get_hash().as_uint256(),
            )),
            fetches: Mutex::new(Vec::new()),
        },
        NullMissingNodeReporter,
    );
    let mut tree = SyncTree::new_with_type(SHAMapType::State, true, 206);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    assert!(tree.fetch_root_with_family(leaf.get_hash(), &mut no_filter, &family));
    assert_eq!(tree.root().get_hash(), leaf.get_hash());
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![(leaf.get_hash(), 206)]);
    });
}

#[test]
fn shamap_sync_tree_direct_read_and_iteration_wrappers_use_owner_backed_policy() {
    let first_key =
        Uint256::from_hex("2000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let second_key =
        Uint256::from_hex("A000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let first_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(first_key, vec![0x21; 12]),
        0,
    );
    let second_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(second_key, vec![0xA2; 12]),
        0,
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(2, first_leaf.get_hash());
    root.set_child_hash(10, second_leaf.get_hash());
    root.update_hash();

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-owner-read-iteration",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(18),
        RecordingNodeFetcher {
            expected: vec![
                (first_leaf.get_hash(), first_leaf.clone_with_cowid(0)),
                (second_leaf.get_hash(), second_leaf.clone_with_cowid(0)),
            ],
            fetches: Mutex::new(Vec::new()),
        },
        NullMissingNodeReporter,
    );
    let tree = SyncTree::from_root(root.clone(), true, 107, SyncState::Modifying);

    assert!(
        tree.has_item_with_family(first_key, &family)
            .expect("owner-backed has_item should succeed")
    );
    assert_eq!(
        tree.peek_item_with_family(first_key, &family)
            .expect("owner-backed peek_item should succeed"),
        Some(SHAMapItem::new(first_key, vec![0x21; 12]))
    );
    let resolved = tree
        .peek_item_with_hash_and_family(first_key, &family)
        .expect("owner-backed peek_item_with_hash should succeed")
        .expect("stored item should resolve");
    assert_eq!(resolved.0, SHAMapItem::new(first_key, vec![0x21; 12]));
    assert_eq!(resolved.1, first_leaf.get_hash());

    let found = tree
        .find_key_with_family(second_key, &family)
        .expect("owner-backed find_key should succeed")
        .expect("second key should resolve");
    assert_eq!(found.get_hash(), second_leaf.get_hash());

    let mut stack: Vec<NodePathEntry> = Vec::new();
    let first = tree
        .peek_first_item_with_family(&mut stack, &family)
        .expect("owner-backed peek_first_item should succeed")
        .expect("tree should have a first leaf");
    assert_eq!(first.get_hash(), first_leaf.get_hash());

    let next = tree
        .peek_next_item_with_family(first_key, &mut stack, &family)
        .expect("owner-backed peek_next_item should succeed")
        .expect("tree should have a second leaf");
    assert_eq!(next.get_hash(), second_leaf.get_hash());

    let upper = tree
        .upper_bound_with_family(first_key, &family)
        .expect("owner-backed upper_bound should succeed")
        .expect("upper_bound should find the next leaf");
    assert_eq!(upper.get_hash(), second_leaf.get_hash());

    let lower = tree
        .lower_bound_with_family(second_key, &family)
        .expect("owner-backed lower_bound should succeed")
        .expect("lower_bound should find the previous leaf");
    assert_eq!(lower.get_hash(), first_leaf.get_hash());

    assert!(root.get_child(2).is_some());
    assert!(root.get_child(10).is_some());
    family.with_fetcher(|fetcher| {
        assert!(fetcher.fetches.lock().contains(&first_leaf.get_hash()));
        assert!(fetcher.fetches.lock().contains(&second_leaf.get_hash()));
    });
}

#[test]
fn shamap_sync_tree_direct_read_wrappers_report_missing_once_while_full() {
    let missing_key =
        Uint256::from_hex("2000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let missing_hash = sample_hash(0x93);
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-owner-read-full-gate",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(19),
        NullNodeFetcher,
        SharedReporter(reporter.clone()),
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(2, missing_hash);
    root.update_hash();

    let tree = SyncTree::from_root(root, true, 108, SyncState::Modifying);
    tree.set_full();

    let first = tree
        .has_item_with_family(missing_key, &family)
        .expect_err("missing backed child should surface as a traversal error");
    let second = tree
        .has_item_with_family(missing_key, &family)
        .expect_err("repeated missing backed child should still surface as a traversal error");

    assert_eq!(first, TraversalError::MissingNode(missing_hash));
    assert_eq!(second, TraversalError::MissingNode(missing_hash));
    assert!(!tree.is_full());
    let reporter = reporter.lock();
    assert_eq!(reporter.by_seq, vec![(108, *missing_hash.as_uint256())]);
}

#[test]
fn shamap_sync_tree_owner_fetch_wrappers_preserve_backed_miss_then_filter_fallback() {
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x66), vec![0x42; 12]),
        0,
    );
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-owner-fetch-filter-fallback",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(20),
        NullNodeFetcher,
        SharedReporter(reporter.clone()),
    );
    let tree = SyncTree::new_with_type(SHAMapType::State, true, 220);
    tree.set_full();
    let mut filter = RecordingFilter {
        node_blob: Some(
            leaf.serialize_with_prefix()
                .expect("leaf should serialize with prefix"),
        ),
        got: Vec::new(),
    };
    let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);

    let fetched = tree
        .fetch_node_nt_filtered_with_family(leaf.get_hash(), &mut filter_ref, &family)
        .expect("filter fallback should still resolve the node");

    assert_eq!(fetched.get_hash(), leaf.get_hash());
    let cached = family
        .cache_lookup(leaf.get_hash())
        .expect("backed filter fallback should canonicalize into the family cache");
    assert!(std::ptr::eq(&*cached, &*fetched));
    assert_eq!(
        filter.got,
        vec![(true, leaf.get_hash(), 220, SHAMapNodeType::AccountState)]
    );
    assert!(!tree.is_full());
    let reporter = reporter.lock();
    assert_eq!(reporter.by_seq, vec![(220, *leaf.get_hash().as_uint256())]);
}

#[test]
fn shamap_sync_tree_owner_fetch_node_reports_shamap_missing_node_once() {
    let missing_hash = sample_hash(0x94);
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-owner-fetch-throw",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(21),
        NullNodeFetcher,
        SharedReporter(reporter.clone()),
    );
    let tree = SyncTree::new_with_type(SHAMapType::State, true, 221);
    tree.set_full();

    let first = tree
        .fetch_node_with_family(missing_hash, &family)
        .expect_err("missing backed fetch should surface as SHAMapMissingNode");
    let second = tree
        .fetch_node_with_family(missing_hash, &family)
        .expect_err("repeated backed miss should keep surfacing as SHAMapMissingNode");

    assert_eq!(
        first,
        SHAMapMissingNode::from_hash(SHAMapType::State, missing_hash)
    );
    assert_eq!(
        second,
        SHAMapMissingNode::from_hash(SHAMapType::State, missing_hash)
    );
    assert!(!tree.is_full());
    let reporter = reporter.lock();
    assert_eq!(reporter.by_seq, vec![(221, *missing_hash.as_uint256())]);
}

#[test]
fn shamap_sync_tree_owner_descend_wrappers_preserve_attach_and_no_store_roles() {
    let child = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x67), vec![0x51; 12]),
        0,
    );
    let attach_parent = SHAMapTreeNode::new_inner(1);
    attach_parent.set_child_hash(7, child.get_hash());
    let no_store_parent = SHAMapTreeNode::new_inner(1);
    no_store_parent.set_child_hash(3, child.get_hash());
    let tree = SyncTree::new_with_type(SHAMapType::State, true, 222);
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-owner-descend-roles",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(22),
        RecordingNodeFetcher {
            expected: vec![
                (child.get_hash(), child.clone_with_cowid(0)),
                (child.get_hash(), child.clone_with_cowid(0)),
            ],
            fetches: Mutex::new(Vec::new()),
        },
        NullMissingNodeReporter,
    );

    let attached = tree
        .descend_with_family(&attach_parent, 7, &family)
        .expect("owner-backed descend should resolve the child");
    assert_eq!(attached.get_hash(), child.get_hash());
    assert!(attach_parent.get_child(7).is_some());

    let detached = tree
        .descend_no_store_with_family(&no_store_parent, 3, &family)
        .expect("owner-backed descend_no_store should resolve the child")
        .expect("descend_no_store should return the fetched child");
    assert_eq!(detached.get_hash(), child.get_hash());
    assert!(no_store_parent.get_child(3).is_none());
}

#[test]
fn shamap_sync_tree_owner_throw_and_async_descend_wrappers_match_cpp_roles() {
    let missing_hash = sample_hash(0x95);
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-owner-descend-throw-async",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(23),
        NullNodeFetcher,
        SharedReporter(reporter.clone()),
    );
    let throw_parent = SHAMapTreeNode::new_inner(1);
    throw_parent.set_child_hash(5, missing_hash);
    let throw_tree = SyncTree::new_with_type(SHAMapType::Transaction, true, 223);
    throw_tree.set_full();

    let error = throw_tree
        .descend_throw_with_family(&throw_parent, 5, &family)
        .expect_err("missing backed descendThrow should surface as SHAMapMissingNode");
    assert_eq!(
        error,
        SHAMapMissingNode::from_hash(SHAMapType::Transaction, missing_hash)
    );
    assert!(!throw_tree.is_full());
    let reporter = reporter.lock();
    assert_eq!(reporter.by_seq, vec![(223, *missing_hash.as_uint256())]);
    drop(reporter);

    let async_parent = SHAMapTreeNode::new_inner(1);
    async_parent.set_child_hash(9, missing_hash);
    let async_tree = SyncTree::new_with_type(SHAMapType::Transaction, true, 224);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let mut requests = Vec::new();

    let pending = async_tree.descend_async_with_family(
        &async_parent,
        9,
        &mut no_filter,
        &family,
        &mut |hash, ledger_seq| requests.push((hash, ledger_seq)),
    );

    match pending {
        shamap::fetch::AsyncDescendResult::Pending(hash) => assert_eq!(hash, missing_hash),
        shamap::fetch::AsyncDescendResult::Ready(_) => {
            panic!("missing backed descend_async should stay pending")
        }
    }
    assert_eq!(requests, vec![(missing_hash, 224)]);
}

#[test]
fn shamap_sync_tree_visitor_and_difference_wrappers_preserve_owner_behavior() {
    let shared_key =
        Uint256::from_hex("2000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let only_self_key =
        Uint256::from_hex("A000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let shared_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(shared_key, vec![0x31; 12]),
        0,
    );
    let only_self_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(only_self_key, vec![0x91; 12]),
        0,
    );

    let self_root = SHAMapTreeNode::new_inner(1);
    self_root.set_child_hash(2, shared_leaf.get_hash());
    self_root.set_child_hash(10, only_self_leaf.get_hash());
    self_root.update_hash();

    let have_root = SHAMapTreeNode::new_inner(1);
    have_root.set_child_hash(2, shared_leaf.get_hash());
    have_root.share_child(2, &shared_leaf);
    have_root.update_hash();

    let self_family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-owner-visit-diff-self",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(20),
        RecordingNodeFetcher {
            expected: vec![
                (shared_leaf.get_hash(), shared_leaf.clone_with_cowid(0)),
                (
                    only_self_leaf.get_hash(),
                    only_self_leaf.clone_with_cowid(0),
                ),
            ],
            fetches: Mutex::new(Vec::new()),
        },
        NullMissingNodeReporter,
    );
    let have_family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-owner-visit-diff-have",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(21),
        RecordingNodeFetcher::default(),
        NullMissingNodeReporter,
    );
    let self_tree = SyncTree::from_root(self_root.clone(), true, 109, SyncState::Modifying);
    let have_tree = SyncTree::from_root(have_root, false, 109, SyncState::Modifying);

    let mut visited_nodes = Vec::new();
    self_tree
        .visit_nodes_with_family(&self_family, &mut |node| {
            visited_nodes.push(node.get_hash());
            true
        })
        .expect("owner-backed visit_nodes should succeed");
    assert_eq!(visited_nodes[0], self_root.get_hash());
    assert!(visited_nodes.contains(&shared_leaf.get_hash()));
    assert!(visited_nodes.contains(&only_self_leaf.get_hash()));
    assert!(self_root.get_child(2).is_none());
    assert!(self_root.get_child(10).is_none());

    let mut visited_leaves = Vec::new();
    self_tree
        .visit_leaves_with_family(&self_family, &mut |item| {
            visited_leaves.push(item.key());
        })
        .expect("owner-backed visit_leaves should succeed");
    assert_eq!(visited_leaves, vec![shared_key, only_self_key]);

    let mut diff_hashes = Vec::new();
    self_tree
        .visit_differences_with_families(
            Some(&have_tree),
            &self_family,
            Some(&have_family),
            &mut |node| {
                diff_hashes.push(node.get_hash());
                true
            },
        )
        .expect("owner-backed visit_differences should succeed");
    assert_eq!(diff_hashes[0], self_root.get_hash());
    assert!(diff_hashes.contains(&only_self_leaf.get_hash()));
    assert!(!diff_hashes.contains(&shared_leaf.get_hash()));
}

#[test]
fn shamap_sync_tree_add_known_node_with_family_logs_unable_to_hook_sequence() {
    let missing_grandchild_hash = sample_hash(0x61);
    let incoming_inner = SHAMapTreeNode::new_inner(1);
    incoming_inner.set_child_hash(4, missing_grandchild_hash);
    incoming_inner.update_hash();
    let raw_wire = incoming_inner
        .serialize_for_wire()
        .expect("inner wire serialization should succeed");
    let journal = Arc::new(RecordingJournal::default());
    let family = make_logging_family("sync-known-unhook-log", journal.clone());
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, incoming_inner.get_hash());
    root.update_hash();
    let mut tree = SyncTree::from_root(root.clone(), true, 75, SyncState::Synching);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let target = SHAMapNodeId::default()
        .get_child_node_id(1)
        .expect("child id should exist")
        .get_child_node_id(4)
        .expect("grandchild id should exist");
    let stuck = SHAMapNodeId::default()
        .get_child_node_id(1)
        .expect("child id should exist");

    let result = tree.add_known_node_with_family(target, &raw_wire, &mut no_filter, &family);

    assert!(result.is_useful());
    assert!(root.get_child(1).is_none());
    assert_eq!(
        journal.entries(),
        vec![
            (JournalLevel::Warn, format!("unable to hook node {target}"),),
            (JournalLevel::Info, format!(" stuck at {stuck}"),),
            (JournalLevel::Info, "got depth=2, walked to= 1".to_owned(),),
        ]
    );
}

#[test]
fn shamap_sync_tree_add_known_node_with_family_logs_late_duplicate_trace() {
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x49), vec![7; 12]),
        0,
    );
    let raw_wire = leaf
        .serialize_for_wire()
        .expect("leaf wire serialization should succeed");
    let journal = Arc::new(RecordingJournal::default());
    let family = make_logging_family("sync-known-late-duplicate-log", journal.clone());
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(4, leaf.get_hash());
    root.share_child(4, &leaf);
    root.update_hash_deep();
    let mut tree = SyncTree::from_root(root, true, 76, SyncState::Synching);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let target = SHAMapNodeId::default()
        .get_child_node_id(4)
        .expect("child id should exist");

    let result = tree.add_known_node_with_family(target, &raw_wire, &mut no_filter, &family);

    assert!(result.is_good());
    assert!(!result.is_useful());
    assert!(!result.is_invalid());
    assert_eq!(
        journal.entries(),
        vec![(
            JournalLevel::Trace,
            "got node, already had it (late)".to_owned(),
        )]
    );
}

#[test]
fn shamap_sync_tree_state_and_root_wire_match_narrow_cpp_roles() {
    let mut tree = SyncTree::new(true, 12);
    assert_eq!(tree.map_type(), SHAMapType::Free);
    assert_eq!(tree.state(), SyncState::Modifying);
    assert!(tree.is_valid());
    assert!(tree.serialize_root().is_err());

    tree.set_synching();
    assert!(tree.is_synching());

    tree.clear_synching();
    assert_eq!(tree.state(), SyncState::Modifying);

    tree.set_immutable();
    assert_eq!(tree.state(), SyncState::Immutable);

    tree.clear_synching();
    assert_eq!(tree.state(), SyncState::Modifying);

    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x12), vec![5; 12]),
        0,
    );
    let tree = SyncTree::from_root(leaf.clone(), true, 12, SyncState::Immutable);
    assert_eq!(
        tree.serialize_root()
            .expect("root wire serialization should succeed"),
        leaf.serialize_for_wire()
            .expect("tree-node wire serialization should succeed")
    );

    let invalid_root = SHAMapTreeNode::new_inner(0);
    let mut invalid_tree = SyncTree::from_root(invalid_root, false, 0, SyncState::Invalid);
    assert!(!invalid_tree.is_valid());
    invalid_tree.clear_synching();
    assert_eq!(invalid_tree.state(), SyncState::Modifying);

    let typed_tree = SyncTree::new_with_type(SHAMapType::Transaction, true, 13);
    assert_eq!(typed_tree.map_type(), SHAMapType::Transaction);
}

#[test]
fn shamap_sync_tree_hash_materializes_zero_root_owner() {
    let key = sample_uint256(0x34);
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![9; 12]),
        0,
    );
    let root = SHAMapTreeNode::new_inner(0);
    root.set_child_hash(3, leaf.get_hash());

    let mut tree = SyncTree::from_root(root.clone(), true, 14, SyncState::Modifying);
    assert!(tree.root().get_hash().is_zero());

    let hash = tree.hash();

    assert!(!hash.is_zero());
    assert_eq!(tree.root().get_hash(), hash);
    assert_eq!(tree.hash(), hash);
}

#[test]
fn shamap_sync_tree_get_missing_nodes_updates_sync_state() {
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x31), vec![7; 12]),
        0,
    );
    let mut complete_tree = SyncTree::from_root(leaf, true, 0, SyncState::Synching);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let mut full_below = NullFullBelowCache::new(15);
    let complete_missing = complete_tree.get_missing_nodes(
        8,
        &mut no_filter,
        &mut full_below,
        &mut |_| None,
        &mut || 0,
    );
    assert!(complete_missing.is_empty());
    assert_eq!(complete_tree.state(), SyncState::Modifying);

    let incomplete_root = SHAMapTreeNode::new_inner(1);
    incomplete_root.set_child_hash(6, sample_hash(0x66));
    incomplete_root.update_hash();
    let mut incomplete_tree = SyncTree::from_root(incomplete_root, true, 0, SyncState::Synching);
    let mut null_cache = NullFullBelowCache::new(16);
    let missing = incomplete_tree.get_missing_nodes(
        8,
        &mut no_filter,
        &mut null_cache,
        &mut |_| None,
        &mut || 0,
    );
    assert_eq!(missing.len(), 1);
    assert!(incomplete_tree.is_synching());
}

#[test]
fn shamap_sync_tree_deferred_missing_node_driver_matches_narrow_cpp_restart_role() {
    let missing_leaf_hash = sample_hash(0x67);
    let fetched_inner = SHAMapTreeNode::new_inner(1);
    fetched_inner.set_child_hash(8, missing_leaf_hash);
    fetched_inner.update_hash_deep();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(5, fetched_inner.get_hash());
    root.update_hash();

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "parity-deferred-missing-driver",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(17),
        NullNodeFetcher,
        NullMissingNodeReporter,
    );
    let mut tree = SyncTree::from_root(root, true, 93, SyncState::Synching);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let mut scheduled = Vec::new();
    let mut completed = Vec::new();

    let missing = tree.get_missing_nodes_deferred_with_family(
        8,
        &mut no_filter,
        &family,
        8,
        &mut || 0,
        &mut |hash, ledger_seq| scheduled.push((hash, ledger_seq)),
        &mut |pending| {
            let batch = pending
                .iter()
                .map(|request| (request.hash(), request.ledger_seq()))
                .collect::<Vec<_>>();
            completed.push(batch.clone());

            if batch == vec![(fetched_inner.get_hash(), 93)] {
                vec![Some(fetched_inner.clone())]
            } else if batch == vec![(missing_leaf_hash, 93)] {
                vec![None]
            } else {
                panic!("unexpected deferred batch: {batch:?}");
            }
        },
    );

    assert_eq!(
        missing,
        vec![(
            SHAMapNodeId::default()
                .get_child_node_id(5)
                .expect("child id should exist")
                .get_child_node_id(8)
                .expect("grandchild id should exist"),
            *missing_leaf_hash.as_uint256(),
        )]
    );
    assert!(tree.is_synching());
    assert_eq!(
        scheduled,
        vec![(fetched_inner.get_hash(), 93), (missing_leaf_hash, 93)]
    );
    assert_eq!(
        completed,
        vec![
            vec![(fetched_inner.get_hash(), 93)],
            vec![(missing_leaf_hash, 93)],
        ]
    );
}

#[test]
fn shamap_sync_tree_deferred_missing_node_completion_marks_full_subtrees() {
    let fetched_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x7f), vec![6; 12]),
        0,
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(3, fetched_leaf.get_hash());
    root.update_hash();

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-tree-deferred-complete",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        RecordingFullBelowCache::new(18),
        NullNodeFetcher,
        NullMissingNodeReporter,
    );
    let mut tree = SyncTree::from_root(root.clone(), true, 92, SyncState::Synching);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let mut requested = Vec::new();

    let missing = tree.get_missing_nodes_deferred_with_family(
        8,
        &mut no_filter,
        &family,
        8,
        &mut || 0,
        &mut |hash, ledger_seq| requested.push((hash, ledger_seq)),
        &mut |pending| {
            assert_eq!(
                pending
                    .iter()
                    .map(|request| (request.hash(), request.ledger_seq()))
                    .collect::<Vec<_>>(),
                vec![(fetched_leaf.get_hash(), 92)]
            );
            vec![Some(fetched_leaf.clone())]
        },
    );

    assert!(missing.is_empty());
    assert_eq!(tree.state(), SyncState::Modifying);
    assert_eq!(requested, vec![(fetched_leaf.get_hash(), 92)]);
    assert!(root.is_full_below(18));
    family.with_full_below_cache(|full_below_cache| {
        assert_eq!(
            full_below_cache.inserted.lock().unwrap().clone(),
            vec![*root.get_hash().as_uint256()]
        );
    });
}

#[test]
fn shamap_sync_tree_get_missing_nodes_with_family_reports_deferred_backed_miss_once() {
    let missing_hash = sample_hash(0x80);
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-owner-deferred-miss-report",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(20),
        NullNodeFetcher,
        SharedReporter(reporter.clone()),
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(4, missing_hash);
    root.update_hash();

    let mut tree = SyncTree::from_root(root, true, 109, SyncState::Synching);
    tree.set_full();
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    let missing = tree.get_missing_nodes_with_family(8, &mut no_filter, &family, &mut || 0);

    assert_eq!(
        missing,
        vec![(
            SHAMapNodeId::default()
                .get_child_node_id(4)
                .expect("child id should exist"),
            *missing_hash.as_uint256(),
        )]
    );
    assert!(tree.is_synching());
    assert!(!tree.is_full());
    let reporter = reporter.lock();
    assert_eq!(reporter.by_seq, vec![(109, *missing_hash.as_uint256())]);
}

#[test]
fn shamap_sync_tree_family_logging_matches_owner_surface_roles() {
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x11), vec![1; 12]),
        0,
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, leaf.get_hash());
    root.share_child(1, &leaf);
    root.update_hash_deep();

    let journal = Arc::new(RecordingJournal::default());
    let family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "sync-get-node-fat-missing",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        NullNodeFetcher,
        NullMissingNodeReporter,
        journal.clone(),
    );

    let mut data = Vec::new();
    let found = SyncTree::from_root(root.clone(), true, 0, SyncState::Modifying)
        .get_node_fat(
            SHAMapNodeId::default()
                .get_child_node_id(2)
                .expect("child id should exist"),
            &mut data,
            true,
            1,
            &mut |_| None,
        )
        .expect("missing sibling branch should not error");
    assert!(!found);
    assert!(data.is_empty());

    let deeper_wanted = SHAMapNodeId::default()
        .get_child_node_id(1)
        .expect("child id should exist")
        .get_child_node_id(3)
        .expect("grandchild id should exist");
    let found = SyncTree::from_root(root, true, 0, SyncState::Modifying)
        .get_node_fat_with_family(deeper_wanted, &mut data, true, 1, &family)
        .expect("deeper missing path should not error");

    assert!(!found);
    assert!(data.is_empty());
    assert_eq!(journal.entries().len(), 1);
    assert_eq!(journal.entries()[0].0, JournalLevel::Info);
    assert!(
        journal.entries()[0]
            .1
            .contains("peer requested node that is not in the map")
    );

    let empty_root = SHAMapTreeNode::new_inner(1);
    empty_root.update_hash();
    let empty_journal = Arc::new(RecordingJournal::default());
    let empty_family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "sync-get-node-fat-empty",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        NullNodeFetcher,
        NullMissingNodeReporter,
        empty_journal.clone(),
    );

    let found = SyncTree::from_root(empty_root, true, 0, SyncState::Modifying)
        .get_node_fat_with_family(SHAMapNodeId::default(), &mut data, true, 1, &empty_family)
        .expect("empty inner check should not error");

    assert!(!found);
    assert!(data.is_empty());
    assert_eq!(empty_journal.entries().len(), 1);
    assert_eq!(empty_journal.entries()[0].0, JournalLevel::Warn);
    assert!(
        empty_journal.entries()[0]
            .1
            .contains("peer requests empty node")
    );
}

#[test]
fn shamap_sync_tree_fetch_root_with_family_logs_state_trace() {
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x5b), vec![8; 12]),
        0,
    );
    let leaf_blob = leaf
        .serialize_with_prefix()
        .expect("leaf prefix serialization should succeed");
    let journal = Arc::new(RecordingJournal::default());
    let family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "fetch-root-state-log",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        NullNodeFetcher,
        NullMissingNodeReporter,
        journal.clone(),
    );
    let mut tree = SyncTree::new_with_type(SHAMapType::State, true, 89);
    let mut filter = RecordingFilter {
        node_blob: Some(leaf_blob),
        got: Vec::new(),
    };
    let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);

    assert!(tree.fetch_root_with_family(leaf.get_hash(), &mut filter_ref, &family));
    assert_eq!(tree.root().get_hash(), leaf.get_hash());
    assert_eq!(
        filter.got,
        vec![(true, leaf.get_hash(), 89, SHAMapNodeType::AccountState)]
    );
    assert_eq!(
        journal.entries(),
        vec![(
            JournalLevel::Trace,
            format!("Fetch root STATE node {}", leaf.get_hash()),
        )]
    );
}

#[test]
fn shamap_sync_tree_fetch_root_with_family_legacy_constructor_uses_free_trace_label() {
    let requested = sample_hash(0x5c);
    let journal = Arc::new(RecordingJournal::default());
    let family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "fetch-root-free-log",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        NullNodeFetcher,
        NullMissingNodeReporter,
        journal.clone(),
    );
    let mut tree = SyncTree::new(true, 90);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    assert!(!tree.fetch_root_with_family(requested, &mut no_filter, &family));
    assert_eq!(
        journal.entries(),
        vec![(
            JournalLevel::Trace,
            format!("Fetch root SHAMap node {requested}"),
        )]
    );
}

#[test]
fn shamap_sync_tree_walk_and_serve_use_owner_backed_policy() {
    let fetched_inner = SHAMapTreeNode::new_inner(1);
    fetched_inner.set_child_hash(7, sample_hash(0x77));

    let walk_root = SHAMapTreeNode::new_inner(1);
    walk_root.set_child_hash(2, sample_hash(0x22));
    walk_root.update_hash();

    let walk_tree = SyncTree::from_root(walk_root.clone(), true, 0, SyncState::Modifying);
    let mut missing = Vec::new();
    walk_tree.walk_map(SHAMapType::Transaction, &mut missing, 8, &mut |hash| {
        if hash == sample_hash(0x22) {
            Some(fetched_inner.clone())
        } else {
            None
        }
    });
    assert_eq!(
        missing,
        vec![SHAMapMissingNode::from_hash(
            SHAMapType::Transaction,
            sample_hash(0x77)
        )]
    );
    assert!(walk_root.get_child(2).is_none());

    let served_leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x41), vec![9; 12]),
        0,
        sample_hash(0x99),
    );
    let serve_root = SHAMapTreeNode::new_inner(1);
    serve_root.set_child_hash(9, sample_hash(0x99));
    serve_root.update_hash();
    let wanted = SHAMapNodeId::default()
        .get_child_node_id(9)
        .expect("child id should exist");

    let backed_tree = SyncTree::from_root(serve_root.clone(), true, 0, SyncState::Modifying);
    let mut data = Vec::new();
    let found = backed_tree
        .get_node_fat(wanted, &mut data, true, 1, &mut |_| {
            Some(served_leaf.clone())
        })
        .expect("backed owner should fetch missing child");
    assert!(found);
    assert_eq!(data.len(), 1);
    assert!(serve_root.get_child(9).is_some());

    let unbacked_root = SHAMapTreeNode::new_inner(1);
    unbacked_root.set_child_hash(9, sample_hash(0x99));
    unbacked_root.update_hash();
    let unbacked_tree = SyncTree::from_root(unbacked_root, false, 0, SyncState::Modifying);
    let mut none = Vec::new();
    let error = unbacked_tree
        .get_node_fat(wanted, &mut none, true, 1, &mut |_| {
            Some(served_leaf.clone())
        })
        .expect_err("unbacked owner should not fetch missing child");
    assert_eq!(error, TraversalError::MissingNode(sample_hash(0x99)));
}

#[test]
fn shamap_sync_tree_walk_map_with_family_uses_owner_fetch_policy() {
    #[derive(Debug, Default)]
    struct RecordingObjectFetcher {
        objects: HashMap<SHAMapHash, NodeObject>,
        fetches: Mutex<Vec<(SHAMapHash, u32)>>,
    }

    impl SHAMapNodeFetcher for RecordingObjectFetcher {
        fn fetch_node_object(&self, hash: SHAMapHash, ledger_seq: u32) -> Option<NodeObject> {
            self.fetches.lock().push((hash, ledger_seq));
            self.objects.get(&hash).cloned()
        }
    }

    let missing_hash = sample_hash(0x88);
    let fetched_inner = SHAMapTreeNode::new_inner(1);
    fetched_inner.set_child_hash(7, missing_hash);
    fetched_inner.update_hash();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(2, fetched_inner.get_hash());
    root.update_hash();

    let mut objects = HashMap::new();
    objects.insert(
        fetched_inner.get_hash(),
        NodeObject::new(
            NodeObjectType::AccountNode,
            fetched_inner
                .serialize_with_prefix()
                .expect("inner node should serialize with prefix"),
            *fetched_inner.get_hash().as_uint256(),
        ),
    );

    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-tree-owner-walk-map-family",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingObjectFetcher {
            objects,
            fetches: Mutex::new(Vec::new()),
        },
        SharedReporter(reporter.clone()),
    );
    let mut tree = SyncTree::from_root(root.clone(), true, 97, SyncState::Modifying);
    tree.set_ledger_seq(207);
    tree.set_full();

    let mut first_missing = Vec::new();
    tree.walk_map_with_family(SHAMapType::State, &mut first_missing, 8, &family);
    let mut second_missing = Vec::new();
    tree.walk_map_with_family(SHAMapType::State, &mut second_missing, 8, &family);

    assert_eq!(
        first_missing,
        vec![SHAMapMissingNode::from_hash(
            SHAMapType::State,
            missing_hash
        )]
    );
    assert_eq!(
        second_missing,
        vec![SHAMapMissingNode::from_hash(
            SHAMapType::State,
            missing_hash
        )]
    );
    assert!(!tree.is_full());
    assert!(root.get_child(2).is_none());
    let reporter_state = reporter.lock();
    assert_eq!(
        reporter_state.by_seq,
        vec![(207, *missing_hash.as_uint256())]
    );
    drop(reporter_state);

    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![
                (fetched_inner.get_hash(), 207),
                (missing_hash, 207),
                (missing_hash, 207),
            ]
        );
    });
}

#[test]
fn shamap_sync_tree_walk_map_parallel_with_family_uses_owner_fetch_policy() {
    #[derive(Debug, Default)]
    struct RecordingObjectFetcher {
        objects: HashMap<SHAMapHash, NodeObject>,
        fetches: Mutex<Vec<(SHAMapHash, u32)>>,
    }

    impl SHAMapNodeFetcher for RecordingObjectFetcher {
        fn fetch_node_object(&self, hash: SHAMapHash, ledger_seq: u32) -> Option<NodeObject> {
            self.fetches.lock().push((hash, ledger_seq));
            self.objects.get(&hash).cloned()
        }
    }

    let missing_hash = sample_hash(0x89);
    let fetched_inner = SHAMapTreeNode::new_inner(1);
    fetched_inner.set_child_hash(7, missing_hash);
    fetched_inner.update_hash();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(2, fetched_inner.get_hash());
    root.update_hash();

    let mut objects = HashMap::new();
    objects.insert(
        fetched_inner.get_hash(),
        NodeObject::new(
            NodeObjectType::AccountNode,
            fetched_inner
                .serialize_with_prefix()
                .expect("inner node should serialize with prefix"),
            *fetched_inner.get_hash().as_uint256(),
        ),
    );

    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let journal = Arc::new(RecordingJournal::default());
    let family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "sync-tree-owner-walk-map-parallel-family",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingObjectFetcher {
            objects,
            fetches: Mutex::new(Vec::new()),
        },
        SharedReporter(reporter.clone()),
        journal.clone(),
    );
    let mut tree = SyncTree::from_root(root.clone(), true, 98, SyncState::Modifying);
    tree.set_ledger_seq(208);
    tree.set_full();

    let mut first_missing = Vec::new();
    assert!(tree.walk_map_parallel_with_family(SHAMapType::State, &mut first_missing, 8, &family,));
    let mut second_missing = Vec::new();
    assert!(
        tree.walk_map_parallel_with_family(SHAMapType::State, &mut second_missing, 8, &family,)
    );

    assert_eq!(
        first_missing,
        vec![SHAMapMissingNode::from_hash(
            SHAMapType::State,
            missing_hash
        )]
    );
    assert_eq!(
        second_missing,
        vec![SHAMapMissingNode::from_hash(
            SHAMapType::State,
            missing_hash
        )]
    );
    assert!(!tree.is_full());
    assert!(root.get_child(2).is_none());
    let reporter_state = reporter.lock();
    assert_eq!(
        reporter_state.by_seq,
        vec![(208, *missing_hash.as_uint256())]
    );
    drop(reporter_state);

    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![
                (fetched_inner.get_hash(), 208),
                (missing_hash, 208),
                (missing_hash, 208),
            ]
        );
    });
    assert_eq!(
        journal.entries(),
        vec![
            (JournalLevel::Debug, "starting worker 2".to_owned()),
            (JournalLevel::Debug, "starting worker 2".to_owned()),
        ]
    );
}

#[test]
fn shamap_sync_tree_walk_map_parallel_with_family_respects_shared_missing_limit() {
    #[derive(Debug, Default)]
    struct BlockingObjectFetcher {
        fetches: Mutex<Vec<SHAMapHash>>,
    }

    impl SHAMapNodeFetcher for BlockingObjectFetcher {
        fn fetch_node_object(&self, hash: SHAMapHash, _ledger_seq: u32) -> Option<NodeObject> {
            self.fetches.lock().push(hash);
            None
        }
    }

    let left_inner = SHAMapTreeNode::new_inner(1);
    left_inner.set_child_hash(5, sample_hash(0x91));
    left_inner.update_hash();

    let right_inner = SHAMapTreeNode::new_inner(1);
    right_inner.set_child_hash(6, sample_hash(0x92));
    right_inner.update_hash();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(2, left_inner.get_hash());
    root.share_child(2, &left_inner);
    root.set_child_hash(7, right_inner.get_hash());
    root.share_child(7, &right_inner);
    root.update_hash();

    let journal = Arc::new(RecordingJournal::default());
    let family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "sync-tree-owner-walk-map-parallel-limit",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        BlockingObjectFetcher {
            fetches: Mutex::new(Vec::new()),
        },
        NullMissingNodeReporter,
        journal.clone(),
    );
    let tree = SyncTree::from_root(root.clone(), true, 100, SyncState::Modifying);
    let mut missing = Vec::new();

    assert!(tree.walk_map_parallel_with_family(SHAMapType::State, &mut missing, 1, &family,));
    assert_eq!(missing.len(), 1);
    assert!(root.get_child(2).is_some());
    assert!(root.get_child(7).is_some());
    assert_eq!(
        journal.entries()[0],
        (JournalLevel::Debug, "starting worker 2".to_owned())
    );
}

#[test]
fn shamap_sync_tree_walk_map_parallel_with_family_logs_worker_panics() {
    #[derive(Debug, Default)]
    struct PanicObjectFetcher {
        objects: HashMap<SHAMapHash, NodeObject>,
        panic_hash: Option<SHAMapHash>,
    }

    impl SHAMapNodeFetcher for PanicObjectFetcher {
        fn fetch_node_object(&self, hash: SHAMapHash, _ledger_seq: u32) -> Option<NodeObject> {
            if self.panic_hash == Some(hash) {
                panic!("parallel fetch panic");
            }
            self.objects.get(&hash).cloned()
        }
    }

    let panic_hash = sample_hash(0x8A);
    let fetched_inner = SHAMapTreeNode::new_inner(1);
    fetched_inner.set_child_hash(7, panic_hash);
    fetched_inner.update_hash();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(2, fetched_inner.get_hash());
    root.update_hash();

    let mut objects = HashMap::new();
    objects.insert(
        fetched_inner.get_hash(),
        NodeObject::new(
            NodeObjectType::AccountNode,
            fetched_inner
                .serialize_with_prefix()
                .expect("inner node should serialize with prefix"),
            *fetched_inner.get_hash().as_uint256(),
        ),
    );

    let journal = Arc::new(RecordingJournal::default());
    let family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "sync-tree-owner-walk-map-parallel-panic",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        PanicObjectFetcher {
            objects,
            panic_hash: Some(panic_hash),
        },
        NullMissingNodeReporter,
        journal.clone(),
    );
    let tree = SyncTree::from_root(root.clone(), true, 99, SyncState::Modifying);
    let mut missing = Vec::new();

    assert!(!tree.walk_map_parallel_with_family(SHAMapType::State, &mut missing, 8, &family,));
    assert!(missing.is_empty());
    assert!(root.get_child(2).is_none());
    assert_eq!(
        journal.entries()[0],
        (JournalLevel::Debug, "starting worker 2".to_owned())
    );
    assert_eq!(journal.entries()[1].0, JournalLevel::Error);
    assert!(
        journal.entries()[1]
            .1
            .contains("Exception(s) in ledger load: parallel fetch panic, ")
    );
}

#[test]
fn shamap_sync_tree_owner_lookup_wrappers_use_family_policy() {
    #[derive(Debug, Default)]
    struct RecordingFetcher {
        node: Option<SharedIntrusive<SHAMapTreeNode>>,
        fetches: Mutex<Vec<SHAMapHash>>,
    }

    impl SHAMapNodeFetcher for RecordingFetcher {
        fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.fetches.lock().push(hash);
            self.node.clone()
        }
    }

    let key = Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
        .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![8; 12]),
        0,
    );
    let inner = SHAMapTreeNode::new_inner(1);
    inner.set_child_hash(2, leaf.get_hash());
    inner.share_child(2, &leaf);
    inner.update_hash_deep();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, inner.get_hash());
    root.update_hash();

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-tree-proof-path",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(19),
        RecordingFetcher {
            node: Some(inner.clone()),
            fetches: Mutex::new(Vec::new()),
        },
        NullMissingNodeReporter,
    );
    let tree = SyncTree::from_root(root.clone(), true, 95, SyncState::Modifying);
    let target = SHAMapNodeId::default()
        .get_child_node_id(1)
        .expect("child id should exist");

    assert!(
        tree.has_inner_node_with_family(target, inner.get_hash(), &family)
            .expect("owner backed lookup should succeed")
    );
    assert!(
        tree.has_leaf_node_with_family(key, leaf.get_hash(), &family)
            .expect("owner backed lookup should succeed")
    );
    let path = tree
        .get_proof_path_with_family(key, &family)
        .expect("owner backed lookup should succeed")
        .expect("key should produce a proof path");

    assert_eq!(
        path,
        vec![
            leaf.serialize_for_wire()
                .expect("leaf wire serialization should succeed"),
            inner
                .serialize_for_wire()
                .expect("inner wire serialization should succeed"),
            root.serialize_for_wire()
                .expect("root wire serialization should succeed"),
        ]
    );
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![inner.get_hash()]);
    });
}

#[test]
fn shamap_sync_tree_compare_uses_owner_backed_policy() {
    let key = Uint256::from_hex("6000000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let left_leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![1; 12]),
        0,
        sample_hash(0xA1),
    );
    let right_leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![2; 12]),
        0,
        sample_hash(0xB2),
    );

    let left_root = SHAMapTreeNode::new_inner(1);
    left_root.set_child_hash(6, left_leaf.get_hash());
    left_root.update_hash();

    let right_root = SHAMapTreeNode::new_inner(1);
    right_root.set_child_hash(6, right_leaf.get_hash());
    right_root.share_child(6, &right_leaf);
    right_root.update_hash();

    let left_tree = SyncTree::from_root(left_root.clone(), true, 0, SyncState::Modifying);
    let right_tree = SyncTree::from_root(right_root, false, 0, SyncState::Modifying);
    let mut delta = Delta::new();

    let complete = left_tree
        .compare(
            &right_tree,
            &mut delta,
            8,
            &mut |hash| (hash == left_leaf.get_hash()).then(|| left_leaf.clone()),
            &mut |_| panic!("loaded right branch should not fetch"),
        )
        .expect("backed owner should fetch missing compare children");

    assert!(complete);
    assert!(left_root.get_child(6).is_some());
    assert_eq!(
        delta.get(&key),
        Some(&(
            Some(SHAMapItem::new(key, vec![1; 12])),
            Some(SHAMapItem::new(key, vec![2; 12])),
        ))
    );

    let loaded_left_root = SHAMapTreeNode::new_inner(1);
    loaded_left_root.set_child_hash(6, left_leaf.get_hash());
    loaded_left_root.share_child(6, &left_leaf);
    loaded_left_root.update_hash();
    let loaded_left_tree = SyncTree::from_root(loaded_left_root, false, 0, SyncState::Modifying);

    let missing_right_root = SHAMapTreeNode::new_inner(1);
    missing_right_root.set_child_hash(6, right_leaf.get_hash());
    missing_right_root.update_hash();
    let missing_right_tree =
        SyncTree::from_root(missing_right_root.clone(), false, 0, SyncState::Modifying);

    let error = loaded_left_tree
        .compare(
            &missing_right_tree,
            &mut Delta::new(),
            8,
            &mut |_| None,
            &mut |_| Some(right_leaf.clone()),
        )
        .expect_err("unbacked owner should not fetch missing compare children");
    assert_eq!(error, TraversalError::MissingNode(right_leaf.get_hash()));
    assert!(missing_right_root.get_child(6).is_none());
}

#[test]
fn shamap_sync_tree_deep_compare_uses_owner_backed_policy() {
    let key = Uint256::from_hex("7000000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![7; 12]),
        0,
        sample_hash(0xC3),
    );

    let backed_root = SHAMapTreeNode::new_inner(1);
    backed_root.set_child_hash(7, leaf.get_hash());
    backed_root.update_hash();

    let loaded_root = SHAMapTreeNode::new_inner(1);
    loaded_root.set_child_hash(7, leaf.get_hash());
    loaded_root.share_child(7, &leaf);
    loaded_root.update_hash();

    let backed_tree = SyncTree::from_root(backed_root.clone(), true, 0, SyncState::Modifying);
    let loaded_tree = SyncTree::from_root(loaded_root, false, 0, SyncState::Modifying);

    assert!(backed_tree.deep_compare(
        &loaded_tree,
        &mut |hash| (hash == leaf.get_hash()).then(|| leaf.clone()),
        &mut |_| panic!("loaded right branch should not fetch"),
    ));
    assert!(backed_root.get_child(7).is_some());

    let missing_root = SHAMapTreeNode::new_inner(1);
    missing_root.set_child_hash(7, leaf.get_hash());
    missing_root.update_hash();
    let unbacked_tree = SyncTree::from_root(missing_root, false, 0, SyncState::Modifying);

    assert!(!loaded_tree.deep_compare(&unbacked_tree, &mut |_| None, &mut |_| Some(leaf.clone())));
}

#[test]
fn shamap_sync_tree_family_compare_paths_capture_cache_aware_behavior() {
    let key = sample_uint256(0x81);
    let left_leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![1; 12]),
        0,
        sample_hash(0xD1),
    );
    let right_leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![2; 12]),
        0,
        sample_hash(0xE2),
    );

    let left_root = SHAMapTreeNode::new_inner(1);
    left_root.set_child_hash(8, left_leaf.get_hash());
    left_root.update_hash();

    let right_root = SHAMapTreeNode::new_inner(1);
    right_root.set_child_hash(8, right_leaf.get_hash());
    right_root.share_child(8, &right_leaf);
    right_root.update_hash();

    let left_tree = SyncTree::from_root(left_root.clone(), true, 0, SyncState::Modifying);
    let right_tree = SyncTree::from_root(right_root, false, 0, SyncState::Modifying);
    let left_family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "left-family",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        RecordingNodeFetcher::with_leaf(left_leaf.get_hash(), &left_leaf),
        NullMissingNodeReporter,
    );
    let right_family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "right-family",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        RecordingNodeFetcher::default(),
        NullMissingNodeReporter,
    );

    let mut delta = Delta::new();
    let complete = left_tree
        .compare_with_families(&right_tree, &mut delta, 8, &left_family, &right_family)
        .expect("family-backed compare should fetch missing left child");

    assert!(complete);
    assert_eq!(
        left_root.get_child(8).map(|node| node.get_hash()),
        Some(left_leaf.get_hash())
    );
    left_family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![left_leaf.get_hash()]);
    });
    assert_eq!(
        delta.get(&key),
        Some(&(
            Some(SHAMapItem::new(key, vec![1; 12])),
            Some(SHAMapItem::new(key, vec![2; 12])),
        ))
    );

    let deep_key = sample_uint256(0x82);
    let deep_leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(deep_key, vec![7; 12]),
        0,
        sample_hash(0xF3),
    );
    let backed_root = SHAMapTreeNode::new_inner(1);
    backed_root.set_child_hash(7, deep_leaf.get_hash());
    backed_root.update_hash();
    let backed_tree = SyncTree::from_root(backed_root.clone(), true, 0, SyncState::Modifying);

    let loaded_root = SHAMapTreeNode::new_inner(1);
    loaded_root.set_child_hash(7, deep_leaf.get_hash());
    loaded_root.share_child(7, &deep_leaf);
    loaded_root.update_hash();
    let loaded_tree = SyncTree::from_root(loaded_root, false, 0, SyncState::Modifying);

    let cache = Arc::new(TreeNodeCache::new(
        "deep-compare",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));
    let mut cached = deep_leaf.clone();
    assert!(!cache.canonicalize_replace_client(deep_leaf.get_hash().as_uint256(), &mut cached));
    let family = SHAMapFamily::new(
        cache,
        NullFullBelowCache::new(1),
        RecordingNodeFetcher::with_leaf(deep_leaf.get_hash(), &deep_leaf),
        NullMissingNodeReporter,
    );
    let right_family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "deep-compare-right",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        RecordingNodeFetcher::default(),
        NullMissingNodeReporter,
    );

    assert!(backed_tree.deep_compare_with_families(&loaded_tree, &family, &right_family));
    assert_eq!(
        backed_root.get_child(7).map(|node| node.get_hash()),
        Some(deep_leaf.get_hash())
    );
    family.with_fetcher(|fetcher| assert!(fetcher.fetches.lock().is_empty()));
}

#[test]
fn shamap_sync_tree_deep_compare_with_families_logs_inner_fetch_miss() {
    let key = sample_uint256(0x83);
    let leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![8; 12]),
        0,
        sample_hash(0x83),
    );
    let left_root = SHAMapTreeNode::new_inner(1);
    left_root.set_child_hash(8, leaf.get_hash());
    left_root.update_hash();
    let left_tree = SyncTree::from_root(left_root, true, 0, SyncState::Modifying);

    let right_root = SHAMapTreeNode::new_inner(1);
    right_root.set_child_hash(8, leaf.get_hash());
    right_root.share_child(8, &leaf);
    right_root.update_hash();
    let right_tree = SyncTree::from_root(right_root, false, 0, SyncState::Modifying);

    let journal = Arc::new(RecordingJournal::default());
    let left_family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "sync-deep-compare-log-left",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        RecordingNodeFetcher::default(),
        NullMissingNodeReporter,
        journal.clone(),
    );
    let right_family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-deep-compare-log-right",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        RecordingNodeFetcher::default(),
        NullMissingNodeReporter,
    );

    assert!(!left_tree.deep_compare_with_families(&right_tree, &left_family, &right_family));
    assert_eq!(
        journal.entries(),
        vec![(JournalLevel::Warn, "unable to fetch inner node".to_owned())]
    );
}
