use crate::support::sample_hash;
use basics::base_uint::Uint256;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use parking_lot::Mutex;
use shamap::compare::Delta;
use shamap::family::{
    JournalLevel, MissingNodeReporter, NullFullBelowCache, NullMissingNodeReporter,
    NullNodeFetcher, SHAMapFamily, SHAMapJournal, SHAMapNodeFetcher,
};
use shamap::item::SHAMapItem;
use shamap::node_id::SHAMapNodeId;
use shamap::node_object::NodeObject;
use shamap::search::NodePathEntry;
use shamap::storage::{NodeObjectType, NodeStoreSink, StorageTree, StoredNode};
use shamap::sync::{SHAMapMissingNode, SHAMapType};
use shamap::traversal::TraversalError;
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use shamap::tree_node_cache::TreeNodeCache;
use std::collections::HashMap;
use std::sync::Arc;
use time::Duration;

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

#[test]
fn shamap_storage_tree_direct_reads_use_owner_backed_policy() {
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

    let key = Uint256::from_hex("2000000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![42; 12]),
        0,
    );
    let cache = Arc::new(TreeNodeCache::new(
        "storage-tree-read",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(2, leaf.get_hash());
    root.update_hash();

    let family = SHAMapFamily::new(
        cache.clone(),
        NullFullBelowCache::new(22),
        RecordingFetcher {
            node: Some(leaf.clone()),
            fetches: Mutex::new(Vec::new()),
        },
        NullMissingNodeReporter,
    );
    let tree = StorageTree::from_loaded_root_with_family(root.clone(), 2, true, 103, &family);

    assert!(
        tree.has_item_with_family(key, &family)
            .expect("owner-backed has_item should succeed")
    );
    assert_eq!(
        tree.peek_item_with_family(key, &family)
            .expect("owner-backed peek_item should succeed"),
        Some(SHAMapItem::new(key, vec![42; 12]))
    );
    let resolved = tree
        .peek_item_with_hash_and_family(key, &family)
        .expect("owner-backed peek_item_with_hash should succeed")
        .expect("stored item should resolve");
    assert_eq!(resolved.0, SHAMapItem::new(key, vec![42; 12]));
    assert_eq!(resolved.1, leaf.get_hash());
    assert!(root.get_child(2).is_some());
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![leaf.get_hash()]);
    });
}

#[test]
fn shamap_storage_tree_family_backed_flush_stays_backend_agnostic() {
    // RocksDB is the Rust storage policy below this seam. SHAMap only sees
    // the generic node-store sink so the caller contract stays portable.
    #[derive(Default)]
    struct RecordingNodeStore {
        stored: Vec<StoredNode>,
    }

    impl NodeStoreSink for RecordingNodeStore {
        fn store(&mut self, node: StoredNode) {
            self.stored.push(node);
        }
    }

    let key = Uint256::from_hex("2300000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let cache = Arc::new(TreeNodeCache::new(
        "storage-tree-node-store",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));
    let canonical = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![0x23; 12]),
        0,
    );
    let mut cached = canonical.clone();
    assert!(!cache.canonicalize_replace_client(canonical.get_hash().as_uint256(), &mut cached));
    let duplicate = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        canonical
            .peek_item()
            .expect("canonical leaf should carry an item"),
        1,
        canonical.get_hash(),
    );
    let family = SHAMapFamily::new_with_node_store(
        cache,
        NullFullBelowCache::new(27),
        NullNodeFetcher,
        NullMissingNodeReporter,
        RecordingNodeStore::default(),
    );
    let mut tree = StorageTree::new_with_family(4, true, 301, &family);
    tree.root().set_child(4, Some(duplicate));
    tree.root().update_hash_deep();

    tree.flush_dirty_with_family(NodeObjectType::AccountNode, &family)
        .expect("family-backed flush should succeed");

    family.with_node_store(|node_store| {
        assert_eq!(node_store.stored.len(), 2);
        assert!(
            node_store
                .stored
                .iter()
                .all(|stored| stored.ledger_seq() == 301)
        );
    });
}

#[test]
fn shamap_storage_tree_direct_reads_can_decode_node_objects_with_owner_ledger_seq() {
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

    let key = Uint256::from_hex("2200000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![0x24; 12]),
        0,
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(2, leaf.get_hash());
    root.update_hash();

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "storage-tree-read-node-object",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(23),
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
    let tree = StorageTree::from_loaded_root_with_family(root.clone(), 2, true, 203, &family);

    assert_eq!(
        tree.peek_item_with_family(key, &family)
            .expect("owner-backed node-object read should succeed"),
        Some(SHAMapItem::new(key, vec![0x24; 12]))
    );
    assert!(root.get_child(2).is_some());
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![(leaf.get_hash(), 203)]);
    });
}

#[test]
fn shamap_storage_tree_walk_map_with_family_uses_owner_fetch_policy() {
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

    let missing_hash = sample_hash(0x95);
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
            "storage-tree-owner-walk-map-family",
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
    let tree = StorageTree::from_loaded_root_with_family(root.clone(), 2, true, 205, &family);
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
        vec![(205, *missing_hash.as_uint256())]
    );
    drop(reporter_state);

    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![
                (fetched_inner.get_hash(), 205),
                (missing_hash, 205),
                (missing_hash, 205),
            ]
        );
    });
}

#[test]
fn shamap_storage_tree_walk_map_parallel_with_family_respects_shared_missing_limit() {
    #[derive(Debug, Default)]
    struct BlockingObjectFetcher {
        fetches: Mutex<Vec<(SHAMapHash, u32)>>,
    }

    impl SHAMapNodeFetcher for BlockingObjectFetcher {
        fn fetch_node_object(&self, hash: SHAMapHash, ledger_seq: u32) -> Option<NodeObject> {
            self.fetches.lock().push((hash, ledger_seq));
            None
        }
    }

    let left_inner = SHAMapTreeNode::new_inner(1);
    left_inner.set_child_hash(1, sample_hash(0x97));
    left_inner.update_hash();

    let right_inner = SHAMapTreeNode::new_inner(1);
    right_inner.set_child_hash(2, sample_hash(0x98));
    right_inner.update_hash();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(3, left_inner.get_hash());
    root.share_child(3, &left_inner);
    root.set_child_hash(6, right_inner.get_hash());
    root.share_child(6, &right_inner);
    root.update_hash();

    let journal = Arc::new(RecordingJournal::default());
    let family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "storage-tree-owner-walk-map-parallel-limit",
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
    let tree = StorageTree::from_loaded_root_with_family(root.clone(), 2, true, 206, &family);
    let mut missing = Vec::new();

    assert!(tree.walk_map_parallel_with_family(SHAMapType::State, &mut missing, 1, &family,));
    assert_eq!(missing.len(), 1);
    assert!(root.get_child(3).is_some());
    assert!(root.get_child(6).is_some());
    assert_eq!(
        journal.entries()[0],
        (JournalLevel::Debug, "starting worker 3".to_owned())
    );
}

#[test]
fn shamap_storage_tree_walk_map_parallel_with_family_logs_worker_panics() {
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

    let panic_hash = sample_hash(0x96);
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
            "storage-tree-owner-walk-map-parallel-panic",
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
    let tree = StorageTree::from_loaded_root_with_family(root.clone(), 2, true, 206, &family);
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
fn shamap_storage_tree_reports_missing_backed_node_only_once_while_full() {
    let key = Uint256::from_hex("2000000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let missing_hash = sample_hash(0x91);
    let cache = Arc::new(TreeNodeCache::new(
        "storage-tree-full-gate",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(2, missing_hash);
    root.update_hash();

    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        cache,
        NullFullBelowCache::new(25),
        NullNodeFetcher,
        SharedReporter(reporter.clone()),
    );
    let tree = StorageTree::from_loaded_root_with_family(root, 2, true, 106, &family);
    tree.set_full();

    let first = tree
        .has_item_with_family(key, &family)
        .expect_err("missing backed child should surface as a traversal error");
    let second = tree
        .has_item_with_family(key, &family)
        .expect_err("repeated missing backed child should still surface as a traversal error");

    assert_eq!(first, TraversalError::MissingNode(missing_hash));
    assert_eq!(second, TraversalError::MissingNode(missing_hash));
    assert!(!tree.is_full());
    let reporter = reporter.lock();
    assert_eq!(reporter.by_seq, vec![(106, *missing_hash.as_uint256())]);
}

#[test]
fn shamap_storage_tree_owner_config_updates_fetch_policy() {
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

    let key = Uint256::from_hex("2100000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let missing_hash = sample_hash(0x92);
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(2, missing_hash);
    root.update_hash();

    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "storage-tree-owner-config",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(26),
        RecordingFetcher::default(),
        SharedReporter(reporter.clone()),
    );
    let mut tree = StorageTree::from_loaded_root_with_family(root, 2, true, 106, &family);
    tree.set_ledger_seq(206);
    tree.set_full();

    let first = tree
        .has_item_with_family(key, &family)
        .expect_err("backed owner should still surface missing branches");
    assert_eq!(first, TraversalError::MissingNode(missing_hash));
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![missing_hash]);
    });
    let reporter_state = reporter.lock();
    assert_eq!(
        reporter_state.by_seq,
        vec![(206, *missing_hash.as_uint256())]
    );
    drop(reporter_state);

    tree.set_unbacked();
    let second = tree
        .has_item_with_family(key, &family)
        .expect_err("unbacked owner should not fetch missing branches");
    assert_eq!(second, TraversalError::MissingNode(missing_hash));
    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![missing_hash],
            "set_unbacked should stop later family fetch attempts"
        );
    });
    let reporter_state = reporter.lock();
    assert_eq!(
        reporter_state.by_seq,
        vec![(206, *missing_hash.as_uint256())]
    );
}

#[test]
fn shamap_storage_tree_lookup_wrappers_use_owner_backed_policy() {
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
        SHAMapItem::new(key, vec![43; 12]),
        0,
    );
    let inner = SHAMapTreeNode::new_inner(1);
    inner.set_child_hash(2, leaf.get_hash());
    inner.share_child(2, &leaf);
    inner.update_hash_deep();

    let cache = Arc::new(TreeNodeCache::new(
        "storage-tree-lookup",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, inner.get_hash());
    root.update_hash();

    let family = SHAMapFamily::new(
        cache.clone(),
        NullFullBelowCache::new(23),
        RecordingFetcher {
            node: Some(inner.clone()),
            fetches: Mutex::new(Vec::new()),
        },
        NullMissingNodeReporter,
    );
    let tree = StorageTree::from_loaded_root_with_family(root.clone(), 2, true, 104, &family);
    let target = SHAMapNodeId::default()
        .get_child_node_id(1)
        .expect("child id should exist");

    assert!(
        tree.has_inner_node_with_family(target, inner.get_hash(), &family)
            .expect("owner-backed has_inner_node should succeed")
    );
    assert!(
        tree.has_leaf_node_with_family(key, leaf.get_hash(), &family)
            .expect("owner-backed has_leaf_node should succeed")
    );
    let path = tree
        .get_proof_path_with_family(key, &family)
        .expect("owner-backed get_proof_path should succeed")
        .expect("stored key should produce a proof path");
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
fn shamap_storage_tree_search_and_iteration_wrappers_use_owner_backed_policy() {
    #[derive(Debug, Default)]
    struct RecordingFetcher {
        nodes: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
        fetches: Mutex<Vec<SHAMapHash>>,
    }

    impl SHAMapNodeFetcher for RecordingFetcher {
        fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.fetches.lock().push(hash);
            self.nodes.get(&hash).cloned()
        }
    }

    let low_key =
        Uint256::from_hex("1000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let high_key =
        Uint256::from_hex("9000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let low_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(low_key, vec![11; 12]),
        0,
    );
    let high_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(high_key, vec![12; 12]),
        0,
    );

    let cache = Arc::new(TreeNodeCache::new(
        "storage-tree-search",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, low_leaf.get_hash());
    root.set_child_hash(9, high_leaf.get_hash());
    root.update_hash();

    let mut nodes = HashMap::new();
    nodes.insert(low_leaf.get_hash(), low_leaf.clone());
    nodes.insert(high_leaf.get_hash(), high_leaf.clone());
    let family = SHAMapFamily::new(
        cache.clone(),
        NullFullBelowCache::new(24),
        RecordingFetcher {
            nodes,
            fetches: Mutex::new(Vec::new()),
        },
        NullMissingNodeReporter,
    );
    let tree = StorageTree::from_loaded_root_with_family(root.clone(), 2, true, 105, &family);

    let found = tree
        .find_key_with_family(low_key, &family)
        .expect("owner-backed find_key should succeed")
        .expect("exact key should resolve");
    assert_eq!(
        found.peek_item().expect("leaf should carry an item"),
        SHAMapItem::new(low_key, vec![11; 12])
    );

    let mut stack: Vec<NodePathEntry> = Vec::new();
    let first = tree
        .peek_first_item_with_family(&mut stack, &family)
        .expect("owner-backed peek_first_item should succeed")
        .expect("first leaf should exist");
    assert_eq!(
        first.peek_item().expect("leaf should carry an item"),
        SHAMapItem::new(low_key, vec![11; 12])
    );

    let upper = tree
        .upper_bound_with_family(low_key, &family)
        .expect("owner-backed upper_bound should succeed")
        .expect("upper bound should exist");
    assert_eq!(
        upper.peek_item().expect("leaf should carry an item"),
        SHAMapItem::new(high_key, vec![12; 12])
    );

    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![low_leaf.get_hash(), high_leaf.get_hash()]
        );
    });
}

#[test]
fn shamap_storage_tree_visit_wrappers_use_owner_backed_policy() {
    let key = Uint256::from_hex("3100000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![3; 12]),
        0,
    );
    let inner = SHAMapTreeNode::new_inner(1);
    inner.set_child_hash(1, leaf.get_hash());
    inner.update_hash();

    let cache = Arc::new(TreeNodeCache::new(
        "storage-tree-visit",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(3, inner.get_hash());
    root.update_hash();
    let tree = StorageTree::from_loaded_root(root.clone(), 2, true, 106, cache);

    let mut visited_nodes = Vec::new();
    tree.visit_nodes(
        &mut |hash| match hash {
            h if h == inner.get_hash() => Some(inner.clone()),
            h if h == leaf.get_hash() => Some(leaf.clone()),
            _ => None,
        },
        &mut |node| {
            visited_nodes.push((node.is_leaf(), node.peek_item().map(|item| item.key())));
            true
        },
    )
    .expect("backed owner should fetch missing visit nodes without attaching");
    assert_eq!(visited_nodes.len(), 3);
    assert_eq!(visited_nodes[0], (false, None));
    assert_eq!(visited_nodes[1], (false, None));
    assert_eq!(visited_nodes[2], (true, Some(key)));
    assert!(root.get_child(3).is_none());

    let mut visited_leaves = Vec::new();
    tree.visit_leaves(
        &mut |hash| match hash {
            h if h == inner.get_hash() => Some(inner.clone()),
            h if h == leaf.get_hash() => Some(leaf.clone()),
            _ => None,
        },
        &mut |item| visited_leaves.push(item.key()),
    )
    .expect("backed owner should visit fetched leaves without attaching");
    assert_eq!(visited_leaves, vec![key]);
    assert!(root.get_child(3).is_none());

    let unbacked_tree = StorageTree::from_loaded_root(
        root,
        3,
        false,
        106,
        Arc::new(TreeNodeCache::new(
            "storage-tree-visit-unbacked",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
    );
    let error = unbacked_tree
        .visit_nodes(&mut |_| Some(inner.clone()), &mut |_| true)
        .expect_err("unbacked owner should not fetch missing visit nodes");
    assert_eq!(error, TraversalError::MissingNode(inner.get_hash()));
}

#[test]
fn shamap_storage_tree_compare_and_deep_compare_wrappers_use_owner_backed_policy() {
    let key = Uint256::from_hex("6200000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
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
    left_root.set_child_hash(6, left_leaf.get_hash());
    left_root.update_hash();

    let right_root = SHAMapTreeNode::new_inner(1);
    right_root.set_child_hash(6, right_leaf.get_hash());
    right_root.share_child(6, &right_leaf);
    right_root.update_hash();

    let left_tree = StorageTree::from_loaded_root(
        left_root.clone(),
        2,
        true,
        107,
        Arc::new(TreeNodeCache::new(
            "storage-tree-compare-left",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
    );
    let right_tree = StorageTree::from_loaded_root(
        right_root,
        3,
        false,
        107,
        Arc::new(TreeNodeCache::new(
            "storage-tree-compare-right",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
    );

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
    assert_eq!(
        left_root.get_child(6).map(|node| node.get_hash()),
        Some(left_leaf.get_hash())
    );
    assert_eq!(
        delta.get(&key),
        Some(&(
            Some(SHAMapItem::new(key, vec![1; 12])),
            Some(SHAMapItem::new(key, vec![2; 12])),
        ))
    );

    let equal_right_root = SHAMapTreeNode::new_inner(1);
    equal_right_root.set_child_hash(6, left_leaf.get_hash());
    equal_right_root.share_child(6, &left_leaf);
    equal_right_root.update_hash();
    let equal_right_tree = StorageTree::from_loaded_root(
        equal_right_root,
        4,
        false,
        107,
        Arc::new(TreeNodeCache::new(
            "storage-tree-deep-compare-right",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
    );
    assert!(left_tree.deep_compare(
        &equal_right_tree,
        &mut |hash| (hash == left_leaf.get_hash()).then(|| left_leaf.clone()),
        &mut |_| panic!("loaded right branch should not fetch"),
    ));

    let loaded_left_root = SHAMapTreeNode::new_inner(1);
    loaded_left_root.set_child_hash(6, left_leaf.get_hash());
    loaded_left_root.share_child(6, &left_leaf);
    loaded_left_root.update_hash();
    let loaded_left_tree = StorageTree::from_loaded_root(
        loaded_left_root,
        5,
        false,
        107,
        Arc::new(TreeNodeCache::new(
            "storage-tree-compare-loaded-left",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
    );

    let missing_right_root = SHAMapTreeNode::new_inner(1);
    missing_right_root.set_child_hash(6, right_leaf.get_hash());
    missing_right_root.update_hash();
    let missing_right_tree = StorageTree::from_loaded_root(
        missing_right_root.clone(),
        6,
        false,
        107,
        Arc::new(TreeNodeCache::new(
            "storage-tree-compare-missing-right",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
    );

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
    assert!(
        !loaded_left_tree.deep_compare(&missing_right_tree, &mut |_| None, &mut |_| Some(
            right_leaf.clone()
        ),)
    );
}

#[test]
fn shamap_storage_tree_deep_compare_with_families_logs_hash_mismatch() {
    let left_leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_hex("6300000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            vec![4; 12],
        ),
        0,
        sample_hash(0x63),
    );
    let right_leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_hex("6400000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            vec![5; 12],
        ),
        0,
        sample_hash(0x64),
    );

    let journal = Arc::new(RecordingJournal::default());
    let left_family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "storage-deep-compare-log-left",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        NullNodeFetcher,
        NullMissingNodeReporter,
        journal.clone(),
    );
    let right_family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "storage-deep-compare-log-right",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        NullNodeFetcher,
        NullMissingNodeReporter,
    );

    let left_tree =
        StorageTree::from_loaded_root_with_family(left_leaf, 7, false, 108, &left_family);
    let right_tree =
        StorageTree::from_loaded_root_with_family(right_leaf, 8, false, 108, &right_family);

    assert!(!left_tree.deep_compare_with_families(&right_tree, &left_family, &right_family));
    assert_eq!(
        journal.entries(),
        vec![(JournalLevel::Warn, "node hash mismatch".to_owned())]
    );
}

#[test]
fn shamap_storage_tree_difference_wrappers_use_owner_backed_policy() {
    let shared_key =
        Uint256::from_hex("1000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let deep_key =
        Uint256::from_hex("4100000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let top_leaf_key =
        Uint256::from_hex("9000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");

    let shared_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(shared_key, vec![1; 12]),
        0,
    );
    let deep_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(deep_key, vec![2; 12]),
        0,
    );
    let top_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(top_leaf_key, vec![3; 12]),
        0,
    );

    let differing_inner = SHAMapTreeNode::new_inner(1);
    differing_inner.set_child_hash(1, deep_leaf.get_hash());
    differing_inner.share_child(1, &deep_leaf);
    differing_inner.update_hash_deep();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, shared_leaf.get_hash());
    root.share_child(1, &shared_leaf);
    root.set_child_hash(4, differing_inner.get_hash());
    root.set_child_hash(9, top_leaf.get_hash());
    root.share_child(9, &top_leaf);
    root.update_hash();

    let have = SHAMapTreeNode::new_inner(1);
    have.set_child_hash(1, shared_leaf.get_hash());
    have.update_hash();

    let tree = StorageTree::from_loaded_root(
        root.clone(),
        2,
        true,
        108,
        Arc::new(TreeNodeCache::new(
            "storage-tree-diff-self",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
    );
    let have_tree = StorageTree::from_loaded_root(
        have,
        3,
        true,
        108,
        Arc::new(TreeNodeCache::new(
            "storage-tree-diff-have",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
    );

    let mut visited = Vec::new();
    tree.visit_differences(
        Some(&have_tree),
        &mut |hash| (hash == differing_inner.get_hash()).then(|| differing_inner.clone()),
        &mut |hash| (hash == shared_leaf.get_hash()).then(|| shared_leaf.clone()),
        &mut |node| {
            visited.push((node.is_inner(), node.peek_item().map(|item| item.key())));
            true
        },
    )
    .expect("backed owner should fetch self and have difference nodes");

    assert_eq!(visited.len(), 4);
    assert_eq!(visited[0], (true, None));
    assert_eq!(visited[1], (false, Some(top_leaf_key)));
    assert_eq!(visited[2], (true, None));
    assert_eq!(visited[3], (false, Some(deep_key)));
    assert_eq!(
        root.get_child(4).map(|node| node.get_hash()),
        Some(differing_inner.get_hash())
    );
}

#[test]
fn shamap_storage_tree_mutation_wrappers_match_loaded_mutation_roles() {
    let first_key =
        Uint256::from_hex("3100000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let second_key =
        Uint256::from_hex("3200000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let cache = Arc::new(TreeNodeCache::new(
        "storage-tree-mutation",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));
    let mut tree = StorageTree::new(1, true, 109, cache);

    assert!(
        tree.add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(first_key, vec![5; 12]),
        )
        .expect("first insert should succeed")
    );
    assert!(
        !tree
            .add_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(first_key, vec![5; 12]),
            )
            .expect("duplicate insert should not error")
    );
    assert!(
        tree.add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(second_key, vec![6; 12]),
        )
        .expect("second insert should succeed")
    );
    assert_eq!(
        tree.peek_item(first_key, &mut |_| None)
            .expect("loaded lookup should succeed"),
        Some(SHAMapItem::new(first_key, vec![5; 12]))
    );

    assert!(
        tree.update_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(first_key, vec![7; 12]),
        )
        .expect("exact update should succeed")
    );
    assert_eq!(
        tree.peek_item(first_key, &mut |_| None)
            .expect("updated lookup should succeed"),
        Some(SHAMapItem::new(first_key, vec![7; 12]))
    );

    assert!(
        tree.delete_item(second_key)
            .expect("delete should succeed for an existing key")
    );
    assert!(
        !tree
            .delete_item(second_key)
            .expect("delete should report false when already absent")
    );
    assert_eq!(
        tree.peek_item(second_key, &mut |_| None)
            .expect("post-delete lookup should succeed"),
        None
    );
}

#[test]
fn shamap_storage_tree_hash_unshares_zero_root_owner() {
    let key = Uint256::from_hex("3400000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let cache = Arc::new(TreeNodeCache::new(
        "storage-tree-hash",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));
    let mut tree = StorageTree::new(1, true, 111, cache);
    tree.root().set_child(
        3,
        Some(SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![10; 12]),
            1,
        )),
    );

    assert!(tree.root().get_hash().is_zero());
    assert_eq!(tree.root().cowid(), 1);

    let hash = tree.hash();

    assert!(!hash.is_zero());
    assert_eq!(tree.root().cowid(), 0);
    assert_eq!(tree.hash(), hash);
}

#[test]
fn shamap_storage_tree_mutable_snapshot_preserves_owner_config_and_resets_full() {
    let key = Uint256::from_hex("3300000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let cache = Arc::new(TreeNodeCache::new(
        "storage-tree-snapshot",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));
    let mut original = StorageTree::new(1, true, 110, cache);
    original
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![8; 12]),
        )
        .expect("insert should succeed");
    original.set_full();

    let mut snapshot = original.mutable_snapshot(2);

    assert!(original.is_full());
    assert!(!snapshot.is_full());
    assert!(snapshot.backed());
    assert_eq!(snapshot.ledger_seq(), 110);
    assert_eq!(original.root().cowid(), 1);
    assert_eq!(snapshot.root().cowid(), 0);
    assert_eq!(
        snapshot
            .peek_item(key, &mut |_| None)
            .expect("snapshot lookup should succeed"),
        Some(SHAMapItem::new(key, vec![8; 12]))
    );

    assert!(
        snapshot
            .update_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(key, vec![9; 12]),
            )
            .expect("snapshot update should succeed")
    );

    assert_eq!(snapshot.root().cowid(), 2);
    assert_eq!(original.root().cowid(), 1);
    assert_eq!(
        original
            .peek_item(key, &mut |_| None)
            .expect("original lookup should succeed"),
        Some(SHAMapItem::new(key, vec![8; 12]))
    );
    assert_eq!(
        snapshot
            .peek_item(key, &mut |_| None)
            .expect("updated snapshot lookup should succeed"),
        Some(SHAMapItem::new(key, vec![9; 12]))
    );
}
