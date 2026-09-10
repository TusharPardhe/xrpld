//! Integration tests for the narrowed `xrpl/shamap` migration slice.

use basics::base_uint::Uint256;
use basics::blob::Blob;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use parking_lot::Mutex;
use shamap::compare::{Delta, compare, deep_compare};
use shamap::difference::visit_differences;
use shamap::family::{
    JournalLevel, MissingNodeReporter, NullFullBelowCache, NullMissingNodeReporter,
    NullNodeFetcher, SHAMapFamily, SHAMapJournal, SHAMapNodeFetcher,
};
use shamap::fetch::{AsyncDescendResult, SHAMapSyncFilter, descend_async_with_family};
use shamap::item::SHAMapItem;
use shamap::iteration::{lower_bound, peek_first_item, peek_next_item, upper_bound};
use shamap::mutation::{MutableTree, MutationError, add_item, delete_item, update_item};
use shamap::node_id::SHAMapNodeId;
use shamap::node_object::NodeObject;
use shamap::proof_path::{get_proof_path, has_leaf_node, verify_proof_path};
use shamap::read::{has_item, peek_item, peek_item_with_hash};
use shamap::search::{NodePathEntry, find_key, walk_towards_key_with_path};
use shamap::storage::{
    CanonicalNodeWriter, NodeObjectType, NodeStoreSink, StorageTree, StoredNode,
};
use shamap::sync::{
    FullBelowCache, SHAMapAddNode, SHAMapMissingNode, SHAMapType, SyncState, SyncTree,
    get_missing_nodes, get_node_fat, walk_map,
};
use shamap::traversal::{TraversalError, descend, descend_no_store, descend_throw};
use shamap::tree_node::{
    SHAMapCodecError, SHAMapNodeType, SHAMapTreeNode, WIRE_TYPE_ACCOUNT_STATE,
    WIRE_TYPE_TRANSACTION,
};
use shamap::tree_node_cache::TreeNodeCache;
use shamap::visitor::{visit_leaves, visit_nodes};
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;
use time::Duration;

fn sample_uint256(fill: u8) -> Uint256 {
    Uint256::from_array([fill; 32])
}

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(sample_uint256(fill))
}

fn same_node(left: &SHAMapTreeNode, right: &SHAMapTreeNode) -> bool {
    std::ptr::eq(left, right)
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

#[derive(Default)]
struct RecordingNodeStore {
    stored: Vec<StoredNode>,
}

impl NodeStoreSink for RecordingNodeStore {
    fn store(&mut self, node: StoredNode) {
        self.stored.push(node);
    }
}

#[test]
fn shamap_tree_node_and_cache_match_narrow_cpp_roles() {
    let clock = ManualClock::new(0);
    let cache = TreeNodeCache::new("tree", 1, Duration::seconds(1), clock);
    let hash = sample_hash(7);
    let key = *hash.as_uint256();

    let mut node = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(9), vec![1; 12]),
        0,
        hash,
    );
    assert!(!cache.canonicalize_replace_client(&key, &mut node));
    drop(node);

    let fetched = cache.fetch(&key).expect("tree node should be cached");
    assert!(fetched.is_leaf());
    assert_eq!(fetched.get_type(), SHAMapNodeType::AccountState);
    assert_eq!(fetched.get_hash(), hash);

    cache.clock().advance_seconds(1);
    cache.sweep();
    assert_eq!(cache.get_cache_size(), 0);
    assert_eq!(cache.get_track_size(), 1);

    drop(fetched);
    cache.clock().advance_seconds(1);
    cache.sweep();
    assert_eq!(cache.get_track_size(), 0);
}

#[test]
fn shamap_wire_and_prefix_round_trip_match_narrow_cpp_roles() {
    let key = sample_uint256(0x33);
    let hash = sample_hash(0x55);
    let payload = vec![4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    let leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, payload.clone()),
        0,
        hash,
    );

    let wire = leaf
        .serialize_for_wire()
        .expect("wire serialization should succeed");
    let prefix = leaf
        .serialize_with_prefix()
        .expect("prefix serialization should succeed");

    let parsed_wire = SHAMapTreeNode::make_from_wire(&wire)
        .expect("wire decoding should succeed")
        .expect("wire decoding should produce a node");
    let parsed_prefix =
        SHAMapTreeNode::make_from_prefix(&prefix, hash).expect("prefix decoding should succeed");

    assert_eq!(parsed_wire.get_type(), SHAMapNodeType::AccountState);
    assert_eq!(
        parsed_wire
            .peek_item()
            .expect("wire-decoded node should have an item"),
        SHAMapItem::new(key, payload.clone())
    );
    assert_eq!(parsed_prefix.get_hash(), hash);
    assert_eq!(
        parsed_prefix
            .peek_item()
            .expect("prefix-decoded node should have an item"),
        SHAMapItem::new(key, payload)
    );
}

#[test]
fn shamap_leaf_nodes_reject_short_payloads() {
    let tx_wire = vec![0xAA, 0xBB, 0xCC, WIRE_TYPE_TRANSACTION];
    assert_eq!(
        SHAMapTreeNode::make_from_wire(&tx_wire).expect_err("short tx leaf should be rejected"),
        SHAMapCodecError::ShortLeafNode {
            node_type: SHAMapNodeType::TransactionNm,
            len: 3,
        }
    );

    let state_key = sample_uint256(0x22);
    let mut state_wire = vec![0xAA; 11];
    state_wire.extend_from_slice(state_key.data());
    state_wire.push(WIRE_TYPE_ACCOUNT_STATE);
    assert_eq!(
        SHAMapTreeNode::make_from_wire(&state_wire)
            .expect_err("short account-state leaf should be rejected"),
        SHAMapCodecError::ShortLeafNode {
            node_type: SHAMapNodeType::AccountState,
            len: 11,
        }
    );
}

#[test]
fn shamap_add_node_and_missing_node_helpers_match_cpp_roles() {
    let mut status = SHAMapAddNode::default();
    assert_eq!(status.get_good(), 0);
    assert_eq!(status.get(), "no nodes processed");
    assert!(!status.is_good());
    assert!(!status.is_invalid());
    assert!(!status.is_useful());

    status += SHAMapAddNode::useful();
    status += SHAMapAddNode::duplicate();
    status.inc_invalid();
    status.inc_duplicate();
    status.inc_useful();

    assert_eq!(status.get_good(), 2);
    assert!(status.is_good());
    assert!(status.is_invalid());
    assert!(status.is_useful());
    assert_eq!(status.get(), "good:2 bad:1 dupe:2");

    status.reset();
    assert_eq!(status.get(), "no nodes processed");
    assert_eq!(SHAMapAddNode::invalid().get(), "bad:1");

    let hash_missing = SHAMapMissingNode::from_hash(SHAMapType::State, sample_hash(0x91));
    assert_eq!(
        hash_missing.to_string(),
        format!("Missing Node: State Tree: hash {}", sample_hash(0x91))
    );

    let id = sample_uint256(0x37);
    let id_missing = SHAMapMissingNode::from_id(SHAMapType::Transaction, id);
    assert_eq!(
        id_missing.to_string(),
        format!("Missing Node: Transaction Tree: id {}", id)
    );
}

#[test]
fn shamap_proof_path_verification_matches_narrow_cpp_roles() {
    let key = Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
        .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![3; 12]),
        0,
    );
    let root = SHAMapTreeNode::new_inner(0);
    root.set_child_hash(1, leaf.get_hash());
    root.update_hash();

    let leaf_wire = leaf
        .serialize_for_wire()
        .expect("leaf wire serialization should succeed");
    let root_wire = root
        .serialize_for_wire()
        .expect("root wire serialization should succeed");

    assert!(verify_proof_path(
        *root.get_hash().as_uint256(),
        key,
        &[leaf_wire.clone(), root_wire.clone()]
    ));

    let mut broken_root_wire = root_wire;
    broken_root_wire[0] ^= 0x01;
    assert!(!verify_proof_path(
        *root.get_hash().as_uint256(),
        key,
        &[leaf_wire, broken_root_wire]
    ));
}

#[test]
fn shamap_loaded_tree_lookup_helpers_match_narrow_cpp_roles() {
    let key = Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
        .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![4; 12]),
        0,
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, leaf.get_hash());
    root.share_child(1, &leaf);
    root.update_hash();

    assert!(has_leaf_node(&root, key, leaf.get_hash()));
    assert_eq!(
        get_proof_path(&root, key).expect("loaded tree should produce a proof path"),
        vec![
            leaf.serialize_for_wire()
                .expect("leaf wire serialization should succeed"),
            root.serialize_for_wire()
                .expect("root wire serialization should succeed"),
        ]
    );
}

#[test]
fn shamap_fetch_backed_descend_helpers_match_narrow_cpp_roles() {
    let child = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x44), vec![6; 12]),
        0,
        sample_hash(0x88),
    );
    let parent = SHAMapTreeNode::new_inner(1);
    parent.set_child_hash(7, sample_hash(0x88));

    let mut fetch_calls = 0;
    let fetched = descend(&parent, 7, true, &mut |_| {
        fetch_calls += 1;
        Some(child.clone())
    })
    .expect("fetch-backed descend should resolve the child");
    assert_eq!(fetch_calls, 1);
    assert_eq!(fetched.get_hash(), child.get_hash());

    let no_store_parent = SHAMapTreeNode::new_inner(1);
    no_store_parent.set_child_hash(3, sample_hash(0x88));
    let fetched_no_store =
        descend_no_store(&no_store_parent, 3, true, &mut |_| Some(child.clone()))
            .expect("descend_no_store should return the fetched child");
    assert_eq!(fetched_no_store.get_hash(), child.get_hash());
    assert!(no_store_parent.get_child(3).is_none());

    let missing =
        descend_throw(&parent, 2, true, &mut |_| None).expect("empty branches should not error");
    assert!(missing.is_none());

    let throwing_parent = SHAMapTreeNode::new_inner(1);
    throwing_parent.set_child_hash(5, sample_hash(0x99));
    let error = descend_throw(&throwing_parent, 5, true, &mut |_| None)
        .expect_err("missing non-empty branch should error");
    assert_eq!(error, TraversalError::MissingNode(sample_hash(0x99)));
}

#[test]
fn shamap_async_descend_matches_narrow_cpp_roles() {
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x45), vec![7; 12]),
        0,
    );
    let leaf_blob = leaf
        .serialize_with_prefix()
        .expect("prefix serialization should succeed");
    let parent = SHAMapTreeNode::new_inner(1);
    parent.set_child_hash(8, leaf.get_hash());

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "async-descend-parity",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        NullNodeFetcher,
        NullMissingNodeReporter,
    );

    #[derive(Default)]
    struct Filter {
        blob: Option<Blob>,
    }

    impl SHAMapSyncFilter for Filter {
        fn got_node(
            &mut self,
            _from_filter: bool,
            _node_hash: SHAMapHash,
            _ledger_seq: u32,
            _node_data: Blob,
            _node_type: SHAMapNodeType,
        ) {
        }

        fn get_node(&mut self, _node_hash: SHAMapHash) -> Option<Blob> {
            self.blob.take()
        }
    }

    let mut filter = Filter {
        blob: Some(leaf_blob),
    };
    let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);
    let mut async_requests = Vec::new();

    let resolved = descend_async_with_family(
        &parent,
        8,
        true,
        77,
        &family,
        &mut filter_ref,
        &mut |hash, ledger_seq| async_requests.push((hash, ledger_seq)),
    );

    match resolved {
        AsyncDescendResult::Ready(Some(node)) => assert_eq!(node.get_hash(), leaf.get_hash()),
        _ => panic!("filter should satisfy async descend before any deferred fetch"),
    }
    assert!(async_requests.is_empty());

    let pending_parent = SHAMapTreeNode::new_inner(1);
    pending_parent.set_child_hash(9, sample_hash(0xAB));
    let mut no_filter = None;

    let pending = descend_async_with_family(
        &pending_parent,
        9,
        true,
        78,
        &family,
        &mut no_filter,
        &mut |hash, ledger_seq| async_requests.push((hash, ledger_seq)),
    );

    match pending {
        AsyncDescendResult::Pending(hash) => assert_eq!(hash, sample_hash(0xAB)),
        _ => panic!("backed miss should produce a deferred-read request"),
    }
    assert_eq!(async_requests, vec![(sample_hash(0xAB), 78)]);
}

#[test]
fn shamap_key_directed_search_helpers_match_narrow_cpp_roles() {
    let stored_key =
        Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
            .expect("hex should parse");
    let requested_key =
        Uint256::from_hex("1F34567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
            .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(stored_key, vec![7; 12]),
        0,
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, leaf.get_hash());
    root.share_child(1, &leaf);
    root.update_hash();

    let (resolved, path) = walk_towards_key_with_path(&root, stored_key, false, &mut |_| None)
        .expect("loaded key walk should succeed");
    let resolved = resolved.expect("leaf should be reached");
    assert!(same_node(&resolved, &leaf));
    assert_eq!(path.len(), 2);
    assert!(path[0].node.is_inner());
    assert!(path[1].node.is_leaf());
    assert_eq!(path[0].node_id.get_depth(), 0);
    assert_eq!(path[1].node_id.get_depth(), 1);

    let found = find_key(&root, stored_key, false, &mut |_| None)
        .expect("exact-key lookup should succeed")
        .expect("stored key should resolve");
    assert!(same_node(&found, &leaf));

    let mismatched = find_key(&root, requested_key, false, &mut |_| None)
        .expect("mismatched lookup should still walk successfully");
    assert!(mismatched.is_none());
}

#[test]
fn shamap_ordered_iteration_helpers_match_narrow_cpp_roles() {
    let low_key =
        Uint256::from_hex("1000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let mid_key =
        Uint256::from_hex("4000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let high_key =
        Uint256::from_hex("9000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let between_mid_and_high =
        Uint256::from_hex("7000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");

    let low_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(low_key, vec![1; 12]),
        0,
    );
    let mid_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(mid_key, vec![2; 12]),
        0,
    );
    let high_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(high_key, vec![3; 12]),
        0,
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, low_leaf.get_hash());
    root.share_child(1, &low_leaf);
    root.set_child_hash(4, mid_leaf.get_hash());
    root.share_child(4, &mid_leaf);
    root.set_child_hash(9, high_leaf.get_hash());
    root.share_child(9, &high_leaf);

    let mut stack = Vec::new();
    let first = peek_first_item(&root, &mut stack, false, &mut |_| None)
        .expect("first leaf lookup should succeed")
        .expect("first leaf should exist");
    assert!(same_node(&first, &low_leaf));

    let second = peek_next_item(low_key, &mut stack, false, &mut |_| None)
        .expect("next leaf lookup should succeed")
        .expect("second leaf should exist");
    assert!(same_node(&second, &mid_leaf));

    let third = peek_next_item(mid_key, &mut stack, false, &mut |_| None)
        .expect("third leaf lookup should succeed")
        .expect("third leaf should exist");
    assert!(same_node(&third, &high_leaf));

    assert!(
        peek_next_item(high_key, &mut stack, false, &mut |_| None)
            .expect("iteration end should not error")
            .is_none()
    );

    let upper = upper_bound(&root, between_mid_and_high, false, &mut |_| None)
        .expect("upper bound should succeed")
        .expect("higher leaf should exist");
    assert!(same_node(&upper, &high_leaf));

    let lower = lower_bound(&root, between_mid_and_high, false, &mut |_| None)
        .expect("lower bound should succeed")
        .expect("lower leaf should exist");
    assert!(same_node(&lower, &mid_leaf));
}

#[test]
fn shamap_visit_helpers_match_narrow_cpp_roles() {
    let left_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_hex("1000000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            vec![1; 12],
        ),
        0,
    );
    let deep_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_hex("4100000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            vec![2; 12],
        ),
        0,
    );
    let right_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_hex("9000000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            vec![3; 12],
        ),
        0,
    );

    let middle_inner = SHAMapTreeNode::new_inner(1);
    middle_inner.set_child_hash(1, deep_leaf.get_hash());
    middle_inner.share_child(1, &deep_leaf);
    middle_inner.update_hash_deep();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, left_leaf.get_hash());
    root.share_child(1, &left_leaf);
    root.set_child_hash(4, middle_inner.get_hash());
    root.share_child(4, &middle_inner);
    root.set_child_hash(9, right_leaf.get_hash());
    root.share_child(9, &right_leaf);
    root.update_hash_deep();

    let mut preorder = Vec::new();
    visit_nodes(&root, false, &mut |_| None, &mut |node| {
        preorder.push((node.is_inner(), node.peek_item().map(|item| item.key())));
        true
    })
    .expect("node visit should succeed");

    assert_eq!(preorder.len(), 5);
    assert_eq!(preorder[0], (true, None));
    assert_eq!(
        preorder[1],
        (
            false,
            Some(
                Uint256::from_hex(
                    "1000000000000000000000000000000000000000000000000000000000000000"
                )
                .expect("hex should parse"),
            ),
        )
    );
    assert_eq!(preorder[2], (true, None));
    assert_eq!(
        preorder[3],
        (
            false,
            Some(
                Uint256::from_hex(
                    "4100000000000000000000000000000000000000000000000000000000000000"
                )
                .expect("hex should parse"),
            ),
        )
    );
    assert_eq!(
        preorder[4],
        (
            false,
            Some(
                Uint256::from_hex(
                    "9000000000000000000000000000000000000000000000000000000000000000"
                )
                .expect("hex should parse"),
            ),
        )
    );

    let mut leaves = Vec::new();
    visit_leaves(&root, false, &mut |_| None, &mut |item| {
        leaves.push(item.key());
    })
    .expect("leaf visit should succeed");

    assert_eq!(
        leaves,
        vec![
            Uint256::from_hex("1000000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            Uint256::from_hex("4100000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            Uint256::from_hex("9000000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
        ]
    );
}

#[test]
fn shamap_direct_read_helpers_match_narrow_cpp_roles() {
    let stored_key =
        Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
            .expect("hex should parse");
    let missing_key =
        Uint256::from_hex("1F34567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
            .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(stored_key, vec![8; 12]),
        0,
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, leaf.get_hash());
    root.share_child(1, &leaf);
    root.update_hash_deep();

    assert!(has_item(&root, stored_key, false, &mut |_| None).expect("lookup should succeed"));
    assert!(
        !has_item(&root, missing_key, false, &mut |_| None).expect("missing lookup should succeed")
    );
    assert_eq!(
        peek_item(&root, stored_key, false, &mut |_| None).expect("peek should succeed"),
        Some(SHAMapItem::new(stored_key, vec![8; 12]))
    );
    assert_eq!(
        peek_item(&root, missing_key, false, &mut |_| None).expect("missing peek should succeed"),
        None
    );
    let with_hash = peek_item_with_hash(&root, stored_key, false, &mut |_| None)
        .expect("peek-with-hash should succeed")
        .expect("stored key should resolve");
    assert_eq!(with_hash.0, SHAMapItem::new(stored_key, vec![8; 12]));
    assert_eq!(with_hash.1, leaf.get_hash());
}

#[test]
fn shamap_difference_helpers_match_narrow_cpp_roles() {
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
    root.share_child(4, &differing_inner);
    root.set_child_hash(9, top_leaf.get_hash());
    root.share_child(9, &top_leaf);
    root.update_hash_deep();

    let have = SHAMapTreeNode::new_inner(1);
    have.set_child_hash(1, shared_leaf.get_hash());
    have.share_child(1, &shared_leaf);
    have.update_hash_deep();

    let mut visited = Vec::new();
    visit_differences(
        &root,
        Some(&have),
        false,
        &mut |_| None,
        false,
        &mut |_| None,
        &mut |node| {
            visited.push((node.is_inner(), node.peek_item().map(|item| item.key())));
            true
        },
    )
    .expect("difference walk should succeed");

    assert_eq!(visited.len(), 4);
    assert_eq!(visited[0], (true, None));
    assert_eq!(visited[1], (false, Some(top_leaf_key)));
    assert_eq!(visited[2], (true, None));
    assert_eq!(visited[3], (false, Some(deep_key)));
}

#[test]
fn shamap_walk_map_matches_narrow_cpp_sync_roles() {
    let left_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_hex("1000000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            vec![1; 12],
        ),
        0,
    );
    let right_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_hex("9000000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            vec![2; 12],
        ),
        0,
    );

    let loaded_root = SHAMapTreeNode::new_inner(1);
    loaded_root.set_child_hash(1, left_leaf.get_hash());
    loaded_root.share_child(1, &left_leaf);
    loaded_root.set_child_hash(9, right_leaf.get_hash());
    loaded_root.share_child(9, &right_leaf);
    loaded_root.update_hash_deep();

    let mut missing = Vec::new();
    walk_map(
        &loaded_root,
        SHAMapType::State,
        &mut missing,
        2048,
        false,
        &mut |_| None,
    );
    assert!(missing.is_empty());

    let fetched_inner = SHAMapTreeNode::new_inner(1);
    fetched_inner.set_child_hash(4, sample_hash(0x44));

    let fetch_backed_root = SHAMapTreeNode::new_inner(1);
    fetch_backed_root.set_child_hash(3, sample_hash(0x33));

    let mut fetch_backed_missing = Vec::new();
    walk_map(
        &fetch_backed_root,
        SHAMapType::Transaction,
        &mut fetch_backed_missing,
        32,
        true,
        &mut |hash| {
            if hash == sample_hash(0x33) {
                Some(fetched_inner.clone())
            } else {
                None
            }
        },
    );

    assert_eq!(
        fetch_backed_missing,
        vec![SHAMapMissingNode::from_hash(
            SHAMapType::Transaction,
            sample_hash(0x44)
        )]
    );
    assert!(fetch_backed_root.get_child(3).is_none());
}

#[test]
fn shamap_get_missing_nodes_matches_narrow_cpp_sync_roles() {
    struct TestFullBelowCache {
        generation: u32,
        known: std::sync::Mutex<BTreeSet<Uint256>>,
    }

    impl FullBelowCache for TestFullBelowCache {
        fn generation(&self) -> u32 {
            self.generation
        }

        fn touch_if_exists(&self, hash: Uint256) -> bool {
            self.known.lock().unwrap().contains(&hash)
        }

        fn insert(&self, hash: Uint256) {
            self.known.lock().unwrap().insert(hash);
        }
    }

    struct TestFilter {
        node_blob: Option<Blob>,
        got: Vec<(SHAMapHash, u32, SHAMapNodeType)>,
    }

    impl SHAMapSyncFilter for TestFilter {
        fn got_node(
            &mut self,
            from_filter: bool,
            node_hash: SHAMapHash,
            ledger_seq: u32,
            _node_data: Blob,
            node_type: SHAMapNodeType,
        ) {
            assert!(from_filter);
            self.got.push((node_hash, ledger_seq, node_type));
        }

        fn get_node(&mut self, _node_hash: SHAMapHash) -> Option<Blob> {
            self.node_blob.take()
        }
    }

    let inner = SHAMapTreeNode::new_inner(1);
    inner.set_child_hash(4, sample_hash(0x44));
    inner.update_hash_deep();
    let inner_blob = inner
        .serialize_with_prefix()
        .expect("inner prefix serialization should succeed");

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(3, inner.get_hash());
    root.update_hash_deep();

    let mut filter = TestFilter {
        node_blob: Some(inner_blob),
        got: Vec::new(),
    };
    let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);
    let mut full_below = TestFullBelowCache {
        generation: 12,
        known: std::sync::Mutex::new(BTreeSet::new()),
    };
    let missing = get_missing_nodes(
        &root,
        32,
        77,
        true,
        &mut |_| None,
        &mut filter_ref,
        &mut full_below,
        &mut || 0,
    );

    assert_eq!(
        missing,
        vec![(
            SHAMapNodeId::default()
                .get_child_node_id(3)
                .expect("child id should exist")
                .get_child_node_id(4)
                .expect("grandchild id should exist"),
            *sample_hash(0x44).as_uint256(),
        )]
    );
    assert!(root.get_child(3).is_some());
    assert_eq!(
        filter.got,
        vec![(inner.get_hash(), 77, SHAMapNodeType::Inner)]
    );

    let duplicate_hash = sample_hash(0x88);
    let duplicate_root = SHAMapTreeNode::new_inner(1);
    duplicate_root.set_child_hash(1, duplicate_hash);
    duplicate_root.set_child_hash(2, duplicate_hash);
    duplicate_root.update_hash();

    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let mut null_cache = NullFullBelowCache::new(13);
    let deduped = get_missing_nodes(
        &duplicate_root,
        32,
        0,
        true,
        &mut |_| None,
        &mut no_filter,
        &mut null_cache,
        &mut || 0,
    );

    assert_eq!(
        deduped,
        vec![(
            SHAMapNodeId::default()
                .get_child_node_id(1)
                .expect("child id should exist"),
            *duplicate_hash.as_uint256(),
        )]
    );
}

#[test]
fn shamap_get_node_fat_matches_narrow_cpp_sync_roles() {
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0xAA), vec![1; 12]),
        0,
    );
    let child_inner = SHAMapTreeNode::new_inner(1);
    child_inner.set_child_hash(2, leaf.get_hash());
    child_inner.share_child(2, &leaf);
    child_inner.update_hash_deep();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(3, child_inner.get_hash());
    root.share_child(3, &child_inner);
    root.update_hash_deep();

    let mut chain_data = Vec::new();
    let found = get_node_fat(
        &root,
        SHAMapNodeId::default(),
        &mut chain_data,
        true,
        0,
        false,
        &mut |_| None,
    )
    .expect("loaded get_node_fat should succeed");

    assert!(found);
    assert_eq!(chain_data.len(), 3);
    assert_eq!(chain_data[0].0, SHAMapNodeId::default());
    assert_eq!(
        chain_data[1].0,
        SHAMapNodeId::default()
            .get_child_node_id(3)
            .expect("child id should exist")
    );
    assert_eq!(
        chain_data[2].0,
        SHAMapNodeId::default()
            .get_child_node_id(3)
            .expect("child id should exist")
            .get_child_node_id(2)
            .expect("grandchild id should exist")
    );

    let direct_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x11), vec![2; 12]),
        0,
    );
    let deep_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x44), vec![3; 12]),
        0,
    );
    let branching_inner = SHAMapTreeNode::new_inner(1);
    branching_inner.set_child_hash(4, deep_leaf.get_hash());
    branching_inner.share_child(4, &deep_leaf);
    branching_inner.update_hash_deep();

    let branching_root = SHAMapTreeNode::new_inner(1);
    branching_root.set_child_hash(1, direct_leaf.get_hash());
    branching_root.share_child(1, &direct_leaf);
    branching_root.set_child_hash(4, branching_inner.get_hash());
    branching_root.share_child(4, &branching_inner);
    branching_root.update_hash_deep();

    let mut shallow_data = Vec::new();
    let shallow_found = get_node_fat(
        &branching_root,
        SHAMapNodeId::default(),
        &mut shallow_data,
        false,
        1,
        false,
        &mut |_| None,
    )
    .expect("loaded get_node_fat should succeed");

    assert!(shallow_found);
    assert_eq!(shallow_data.len(), 2);
    assert_eq!(shallow_data[0].0, SHAMapNodeId::default());
    assert_eq!(
        shallow_data[1].0,
        SHAMapNodeId::default()
            .get_child_node_id(4)
            .expect("child id should exist")
    );
}

#[test]
fn shamap_add_root_node_matches_narrow_cpp_sync_ingestion_roles() {
    struct RecordingFilter {
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
            None
        }
    }

    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x61), vec![8; 12]),
        0,
    );
    let wire = leaf
        .serialize_for_wire()
        .expect("leaf wire serialization should succeed");

    let mut tree = SyncTree::new(true, 91);
    tree.set_synching();
    let mut filter = RecordingFilter { got: Vec::new() };
    let accepted = {
        let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);
        tree.add_root_node(leaf.get_hash(), &wire, &mut filter_ref)
    };
    assert!(accepted.is_useful());
    assert!(!tree.is_synching());
    assert_eq!(tree.root().get_hash(), leaf.get_hash());
    assert_eq!(
        filter.got,
        vec![(false, leaf.get_hash(), 91, SHAMapNodeType::AccountState)]
    );

    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let duplicate = tree.add_root_node(leaf.get_hash(), &wire, &mut no_filter);
    assert!(duplicate.is_good());
    assert!(!duplicate.is_useful());
    assert!(!duplicate.is_invalid());

    let mut empty_tree = SyncTree::new(false, 0);
    let invalid = empty_tree.add_root_node(sample_hash(0xFE), &wire, &mut no_filter);
    assert!(invalid.is_invalid());
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

    let typed_tree = SyncTree::new_with_type(SHAMapType::State, true, 13);
    assert_eq!(typed_tree.map_type(), SHAMapType::State);
}

#[test]
fn shamap_sync_tree_hash_matches_narrow_cpp_owner_roles() {
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
fn shamap_sync_tree_family_missing_node_wrapper_matches_narrow_cpp_restart_role() {
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

    let missing_leaf_hash = sample_hash(0x68);
    let fetched_inner = SHAMapTreeNode::new_inner(1);
    fetched_inner.set_child_hash(10, missing_leaf_hash);
    fetched_inner.update_hash_deep();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(6, fetched_inner.get_hash());
    root.update_hash();

    let mut nodes = HashMap::new();
    nodes.insert(fetched_inner.get_hash(), fetched_inner.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "parity-family-missing-driver",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(18),
        RecordingFetcher {
            nodes,
            fetches: Mutex::new(Vec::new()),
        },
        NullMissingNodeReporter,
    );
    let mut tree = SyncTree::from_root(root, true, 94, SyncState::Synching);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;

    let missing = tree.get_missing_nodes_with_family(8, &mut no_filter, &family, &mut || 0);

    assert_eq!(
        missing,
        vec![(
            SHAMapNodeId::default()
                .get_child_node_id(6)
                .expect("child id should exist")
                .get_child_node_id(10)
                .expect("grandchild id should exist"),
            *missing_leaf_hash.as_uint256(),
        )]
    );
    assert!(tree.is_synching());
    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![fetched_inner.get_hash(), missing_leaf_hash]
        );
    });
}

#[test]
fn shamap_sync_tree_has_inner_node_matches_narrow_cpp_roles() {
    #[derive(Debug, Default)]
    struct RecordingFetcher {
        nodes: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
    }

    impl SHAMapNodeFetcher for RecordingFetcher {
        fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.nodes.get(&hash).cloned()
        }
    }

    let inner = SHAMapTreeNode::new_inner(1);
    inner.set_child_hash(11, sample_hash(0x69));
    inner.update_hash();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(7, inner.get_hash());
    root.update_hash();

    let mut nodes = HashMap::new();
    nodes.insert(inner.get_hash(), inner.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "parity-has-inner",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(19),
        RecordingFetcher { nodes },
        NullMissingNodeReporter,
    );
    let tree = SyncTree::from_root(root, true, 95, SyncState::Modifying);
    let target = SHAMapNodeId::default()
        .get_child_node_id(7)
        .expect("child id should exist");

    assert!(
        tree.has_inner_node_with_family(target, inner.get_hash(), &family)
            .expect("owner backed lookup should succeed")
    );
    assert!(
        !tree
            .has_inner_node_with_family(target, sample_hash(0x99), &family)
            .expect("owner backed lookup should succeed")
    );
}

#[test]
fn shamap_sync_tree_has_leaf_node_matches_narrow_cpp_roles() {
    #[derive(Debug, Default)]
    struct RecordingFetcher {
        nodes: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
    }

    impl SHAMapNodeFetcher for RecordingFetcher {
        fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.nodes.get(&hash).cloned()
        }
    }

    let key = Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
        .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![5; 12]),
        0,
    );
    let inner = SHAMapTreeNode::new_inner(1);
    inner.set_child_hash(2, leaf.get_hash());
    inner.share_child(2, &leaf);
    inner.update_hash_deep();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, inner.get_hash());
    root.update_hash();

    let mut nodes = HashMap::new();
    nodes.insert(inner.get_hash(), inner.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "parity-has-leaf",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(20),
        RecordingFetcher { nodes },
        NullMissingNodeReporter,
    );
    let tree = SyncTree::from_root(root, true, 96, SyncState::Modifying);

    assert!(
        tree.has_leaf_node_with_family(key, leaf.get_hash(), &family)
            .expect("owner backed lookup should succeed")
    );
    assert!(
        !tree
            .has_leaf_node_with_family(key, sample_hash(0x99), &family)
            .expect("owner backed lookup should succeed")
    );
}

#[test]
fn shamap_sync_tree_get_proof_path_matches_narrow_cpp_roles() {
    #[derive(Debug, Default)]
    struct RecordingFetcher {
        nodes: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
    }

    impl SHAMapNodeFetcher for RecordingFetcher {
        fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.nodes.get(&hash).cloned()
        }
    }

    let key = Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
        .expect("hex should parse");
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![6; 12]),
        0,
    );
    let inner = SHAMapTreeNode::new_inner(1);
    inner.set_child_hash(2, leaf.get_hash());
    inner.share_child(2, &leaf);
    inner.update_hash_deep();

    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(1, inner.get_hash());
    root.update_hash();

    let mut nodes = HashMap::new();
    nodes.insert(inner.get_hash(), inner.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "parity-proof-path",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(21),
        RecordingFetcher { nodes },
        NullMissingNodeReporter,
    );
    let tree = SyncTree::from_root(root.clone(), true, 97, SyncState::Modifying);

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
    assert!(
        tree.get_proof_path_with_family(sample_uint256(0xFF), &family)
            .expect("owner backed lookup should succeed")
            .is_none()
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
fn shamap_sync_tree_walk_map_with_family_matches_owner_fetch_roles() {
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

    let missing_hash = sample_hash(0xA4);
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
            "sync-walk-map-owner-parity",
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
    tree.set_ledger_seq(209);
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
    assert!(root.get_child(2).is_none());
    assert!(!tree.is_full());
    let reporter_state = reporter.lock();
    assert_eq!(
        reporter_state.by_seq,
        vec![(209, *missing_hash.as_uint256())]
    );
    drop(reporter_state);

    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![
                (fetched_inner.get_hash(), 209),
                (missing_hash, 209),
                (missing_hash, 209),
            ]
        );
    });
}

#[test]
fn shamap_sync_tree_walk_map_parallel_with_family_matches_owner_fetch_roles() {
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

    let missing_hash = sample_hash(0xA5);
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
            "sync-walk-map-parallel-owner-parity",
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
    tree.set_ledger_seq(210);
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
    assert!(root.get_child(2).is_none());
    assert!(!tree.is_full());
    let reporter_state = reporter.lock();
    assert_eq!(
        reporter_state.by_seq,
        vec![(210, *missing_hash.as_uint256())]
    );
    drop(reporter_state);

    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![
                (fetched_inner.get_hash(), 210),
                (missing_hash, 210),
                (missing_hash, 210),
            ]
        );
    });
}

#[test]
fn shamap_sync_tree_walk_map_parallel_with_family_logs_worker_failures() {
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

    let panic_hash = sample_hash(0xA6);
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
            "sync-walk-map-parallel-panic-parity",
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
    let tree = SyncTree::from_root(root.clone(), true, 97, SyncState::Modifying);
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
fn shamap_fetch_root_with_family_matches_narrow_cpp_roles() {
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

    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x5A), vec![8; 12]),
        0,
    );
    let leaf_blob = leaf
        .serialize_with_prefix()
        .expect("leaf prefix serialization should succeed");

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "fetch-root",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        NullNodeFetcher,
        NullMissingNodeReporter,
    );
    let mut tree = SyncTree::new_with_type(SHAMapType::State, true, 88);
    let mut filter = RecordingFilter {
        node_blob: Some(leaf_blob),
        got: Vec::new(),
    };
    let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);

    assert!(tree.fetch_root_with_family(leaf.get_hash(), &mut filter_ref, &family));
    assert_eq!(tree.root().get_hash(), leaf.get_hash());
    assert_eq!(
        filter.got,
        vec![(true, leaf.get_hash(), 88, SHAMapNodeType::AccountState)]
    );
}

#[test]
fn shamap_sync_tree_node_object_fetch_matches_narrow_cpp_roles() {
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
        SHAMapItem::new(sample_uint256(0x53), vec![0x36; 12]),
        0,
    );
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "node-object-fetch-parity",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
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
fn shamap_sync_tree_owner_full_gate_matches_narrow_cpp_fetch_roles() {
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

    let requested = sample_hash(0xA1);
    let journal = Arc::new(RecordingJournal::default());
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let mode = Arc::new(Mutex::new(BlobFetchMode::InvalidBlob));
    let family = SHAMapFamily::new_with_journal(
        Arc::new(TreeNodeCache::new(
            "fetch-root-full-gate",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
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
    assert_eq!(journal.entries()[0].0, JournalLevel::Trace);
    assert_eq!(
        journal.entries()[0].1,
        format!("Fetch root STATE node {requested}")
    );
    assert_eq!(journal.entries()[1].0, JournalLevel::Warn);
    assert!(journal.entries()[1].1.contains("invalid fetched node blob"));

    *mode.lock() = BlobFetchMode::Missing;

    assert!(!tree.fetch_root_with_family(requested, &mut no_filter, &family));
    assert!(!tree.fetch_root_with_family(requested, &mut no_filter, &family));
    assert!(!tree.is_full());
    let reporter = reporter.lock();
    assert_eq!(reporter.by_seq, vec![(95, *requested.as_uint256())]);
}

#[test]
fn shamap_sync_tree_owner_config_matches_narrow_cpp_roles() {
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
            "sync-owner-config-parity",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
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
        assert_eq!(fetcher.fetches.lock().clone(), vec![requested]);
    });
    let reporter_state = reporter.lock();
    assert_eq!(reporter_state.by_seq, vec![(205, *requested.as_uint256())]);
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

    assert!(!loaded_tree.deep_compare(&unbacked_tree, &mut |_| None, &mut |_| Some(leaf.clone()),));
}

#[test]
fn shamap_add_known_node_matches_narrow_cpp_sync_ingestion_roles() {
    struct RecordingFilter {
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
            None
        }
    }

    let child = SHAMapTreeNode::new_inner(0);
    child.set_child_hash(4, sample_hash(0x44));
    child.update_hash_deep();
    let child_wire = child
        .serialize_for_wire()
        .expect("inner wire serialization should succeed");

    let root = SHAMapTreeNode::new_inner(0);
    root.set_child_hash(3, child.get_hash());
    root.update_hash();

    let node_id = SHAMapNodeId::default()
        .get_child_node_id(3)
        .expect("child id should exist");
    let mut tree = SyncTree::from_root(root.clone(), true, 77, SyncState::Synching);
    let mut full_below = NullFullBelowCache::new(1);
    let mut filter = RecordingFilter { got: Vec::new() };
    let accepted = {
        let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);
        tree.add_known_node(
            node_id,
            &child_wire,
            &mut filter_ref,
            &mut full_below,
            &mut |_| None,
        )
    };
    assert!(accepted.is_useful());
    assert!(tree.root().get_child(3).is_some());
    assert_eq!(
        filter.got,
        vec![(false, child.get_hash(), 77, SHAMapNodeType::Inner)]
    );

    let wrong_leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x99), vec![1; 12]),
        0,
        child.get_hash(),
    );
    let wrong_wire = wrong_leaf
        .serialize_for_wire()
        .expect("leaf wire serialization should succeed");

    let wrong_root = SHAMapTreeNode::new_inner(0);
    wrong_root.set_child_hash(3, child.get_hash());
    wrong_root.update_hash();
    let mut invalid_tree = SyncTree::from_root(wrong_root, true, 0, SyncState::Synching);
    let mut no_filter: Option<&mut dyn SHAMapSyncFilter> = None;
    let invalid = invalid_tree.add_known_node(
        node_id,
        &wrong_wire,
        &mut no_filter,
        &mut full_below,
        &mut |_| None,
    );
    assert!(invalid.is_invalid());

    let idle_duplicate = tree.add_known_node(
        node_id,
        &child_wire,
        &mut no_filter,
        &mut full_below,
        &mut |_| None,
    );
    assert!(idle_duplicate.is_good());
    assert!(!idle_duplicate.is_useful());
    assert!(!idle_duplicate.is_invalid());
}

#[test]
fn shamap_sync_tree_owner_read_traversal_wrappers_match_narrow_cpp_roles() {
    #[derive(Debug, Default)]
    struct RecordingFetcher {
        expected: Vec<(SHAMapHash, SharedIntrusive<SHAMapTreeNode>)>,
        fetches: Mutex<Vec<SHAMapHash>>,
    }

    impl SHAMapNodeFetcher for RecordingFetcher {
        fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.fetches.lock().push(hash);
            self.expected
                .iter()
                .find(|(expected_hash, _)| *expected_hash == hash)
                .map(|(_, node)| node.clone())
        }
    }

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
            "sync-read-traversal-parity",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(22),
        RecordingFetcher {
            expected: vec![
                (first_leaf.get_hash(), first_leaf.clone_with_cowid(0)),
                (second_leaf.get_hash(), second_leaf.clone_with_cowid(0)),
            ],
            fetches: Mutex::new(Vec::new()),
        },
        NullMissingNodeReporter,
    );
    let tree = SyncTree::from_root(root.clone(), true, 110, SyncState::Modifying);

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
    assert_eq!(resolved.1, first_leaf.get_hash());
    assert_eq!(
        tree.find_key_with_family(second_key, &family)
            .expect("owner-backed find_key should succeed")
            .expect("stored leaf should resolve")
            .get_hash(),
        second_leaf.get_hash()
    );

    let mut stack: Vec<NodePathEntry> = Vec::new();
    let first = tree
        .peek_first_item_with_family(&mut stack, &family)
        .expect("owner-backed peek_first_item should succeed")
        .expect("tree should have a first item");
    assert_eq!(first.get_hash(), first_leaf.get_hash());
    let next = tree
        .peek_next_item_with_family(first_key, &mut stack, &family)
        .expect("owner-backed peek_next_item should succeed")
        .expect("tree should have a next item");
    assert_eq!(next.get_hash(), second_leaf.get_hash());
    assert_eq!(
        tree.upper_bound_with_family(first_key, &family)
            .expect("owner-backed upper_bound should succeed")
            .expect("upper_bound should resolve")
            .get_hash(),
        second_leaf.get_hash()
    );
    assert_eq!(
        tree.lower_bound_with_family(second_key, &family)
            .expect("owner-backed lower_bound should succeed")
            .expect("lower_bound should resolve")
            .get_hash(),
        first_leaf.get_hash()
    );

    let mut visited_hashes = Vec::new();
    tree.visit_nodes_with_family(&family, &mut |node| {
        visited_hashes.push(node.get_hash());
        true
    })
    .expect("owner-backed visit_nodes should succeed");
    let mut visited_keys = Vec::new();
    tree.visit_leaves_with_family(&family, &mut |item| visited_keys.push(item.key()))
        .expect("owner-backed visit_leaves should succeed");

    assert!(visited_hashes.contains(&root.get_hash()));
    assert!(visited_hashes.contains(&first_leaf.get_hash()));
    assert!(visited_hashes.contains(&second_leaf.get_hash()));
    assert_eq!(visited_keys, vec![first_key, second_key]);
}

#[test]
fn shamap_sync_tree_visit_differences_with_families_matches_narrow_cpp_roles() {
    #[derive(Debug, Default)]
    struct RecordingFetcher {
        expected: Vec<(SHAMapHash, SharedIntrusive<SHAMapTreeNode>)>,
    }

    impl SHAMapNodeFetcher for RecordingFetcher {
        fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.expected
                .iter()
                .find(|(expected_hash, _)| *expected_hash == hash)
                .map(|(_, node)| node.clone())
        }
    }

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
            "sync-differences-parity-self",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(23),
        RecordingFetcher {
            expected: vec![
                (shared_leaf.get_hash(), shared_leaf.clone_with_cowid(0)),
                (
                    only_self_leaf.get_hash(),
                    only_self_leaf.clone_with_cowid(0),
                ),
            ],
        },
        NullMissingNodeReporter,
    );
    let have_family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "sync-differences-parity-have",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(24),
        RecordingFetcher::default(),
        NullMissingNodeReporter,
    );
    let self_tree = SyncTree::from_root(self_root.clone(), true, 111, SyncState::Modifying);
    let have_tree = SyncTree::from_root(have_root, false, 111, SyncState::Modifying);

    let mut visited = Vec::new();
    self_tree
        .visit_differences_with_families(
            Some(&have_tree),
            &self_family,
            Some(&have_family),
            &mut |node| {
                visited.push(node.get_hash());
                true
            },
        )
        .expect("owner-backed visit_differences should succeed");

    assert_eq!(visited[0], self_root.get_hash());
    assert!(visited.contains(&only_self_leaf.get_hash()));
    assert!(!visited.contains(&shared_leaf.get_hash()));
}

#[test]
fn shamap_delta_compare_matches_narrow_cpp_roles() {
    let deleted_key =
        Uint256::from_hex("1000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let changed_key =
        Uint256::from_hex("2000000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");

    let deleted_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(deleted_key, vec![4; 12]),
        0,
    );
    let left_changed = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(changed_key, vec![7; 12]),
        0,
    );
    let right_changed = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(changed_key, vec![9; 12]),
        0,
    );

    let left = SHAMapTreeNode::new_inner(1);
    left.set_child_hash(2, left_changed.get_hash());
    left.share_child(2, &left_changed);
    left.update_hash_deep();

    let right = SHAMapTreeNode::new_inner(1);
    right.set_child_hash(1, deleted_leaf.get_hash());
    right.share_child(1, &deleted_leaf);
    right.set_child_hash(2, right_changed.get_hash());
    right.share_child(2, &right_changed);
    right.update_hash_deep();

    let mut delta = Delta::new();
    let complete = compare(
        &left,
        &right,
        false,
        &mut |_| None,
        false,
        &mut |_| None,
        &mut delta,
        100,
    )
    .expect("delta compare should succeed");

    assert!(complete);
    assert_eq!(delta.len(), 2);
    assert_eq!(
        delta.get(&deleted_key),
        Some(&(None, Some(SHAMapItem::new(deleted_key, vec![4; 12]))))
    );
    assert_eq!(
        delta.get(&changed_key),
        Some(&(
            Some(SHAMapItem::new(changed_key, vec![7; 12])),
            Some(SHAMapItem::new(changed_key, vec![9; 12])),
        ))
    );
}

#[test]
fn shamap_deep_compare_matches_narrow_cpp_roles() {
    let left_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_hex("1000000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            vec![1; 12],
        ),
        0,
    );
    let deep_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_hex("4100000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            vec![2; 12],
        ),
        0,
    );
    let right_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_hex("9000000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            vec![3; 12],
        ),
        0,
    );

    let middle_inner = SHAMapTreeNode::new_inner(1);
    middle_inner.set_child_hash(1, deep_leaf.get_hash());
    middle_inner.share_child(1, &deep_leaf);
    middle_inner.update_hash_deep();

    let left = SHAMapTreeNode::new_inner(1);
    left.set_child_hash(1, left_leaf.get_hash());
    left.share_child(1, &left_leaf);
    left.set_child_hash(4, middle_inner.get_hash());
    left.share_child(4, &middle_inner);
    left.set_child_hash(9, right_leaf.get_hash());
    left.share_child(9, &right_leaf);
    left.update_hash_deep();

    let right = SHAMapTreeNode::new_inner(1);
    right.set_child_hash(1, left_leaf.get_hash());
    right.share_child(1, &left_leaf);
    right.set_child_hash(4, middle_inner.get_hash());
    right.share_child(4, &middle_inner);
    right.set_child_hash(9, right_leaf.get_hash());
    right.share_child(9, &right_leaf);
    right.update_hash_deep();

    assert!(deep_compare(
        &left,
        &right,
        false,
        &mut |_| None,
        false,
        &mut |_| None,
    ));

    let changed_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_hex("9000000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse"),
            vec![9; 12],
        ),
        0,
    );
    right.set_child_hash(9, changed_leaf.get_hash());
    right.share_child(9, &changed_leaf);
    right.update_hash_deep();

    assert!(!deep_compare(
        &left,
        &right,
        false,
        &mut |_| None,
        false,
        &mut |_| None,
    ));
}

#[test]
fn shamap_loaded_tree_mutation_helpers_match_narrow_cpp_roles() {
    let existing_key =
        Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
            .expect("hex should parse");
    let inserted_key =
        Uint256::from_hex("1234A67890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
            .expect("hex should parse");
    let root = SHAMapTreeNode::new_inner(1);
    add_item(
        &root,
        SHAMapNodeType::AccountState,
        SHAMapItem::new(existing_key, vec![1; 12]),
    )
    .expect("first insert should succeed");

    let inserted = add_item(
        &root,
        SHAMapNodeType::AccountState,
        SHAMapItem::new(inserted_key, vec![2; 12]),
    )
    .expect("split insert should succeed");
    assert!(inserted);

    let found_existing = find_key(&root, existing_key, false, &mut |_| None)
        .expect("existing lookup should succeed")
        .expect("existing key should resolve");
    let existing_hash = found_existing.get_hash();

    let updated = update_item(
        &root,
        SHAMapNodeType::AccountState,
        SHAMapItem::new(existing_key, vec![3; 12]),
    )
    .expect("update should succeed");
    assert!(updated);

    let found_updated = find_key(&root, existing_key, false, &mut |_| None)
        .expect("updated lookup should succeed")
        .expect("updated key should resolve");
    assert_ne!(found_updated.get_hash(), existing_hash);

    let error = update_item(
        &root,
        SHAMapNodeType::TransactionMd,
        SHAMapItem::new(existing_key, vec![4; 12]),
    )
    .expect_err("cross-type update should be rejected");
    assert_eq!(
        error,
        MutationError::CrossTypeChange {
            requested: SHAMapNodeType::TransactionMd,
            existing: SHAMapNodeType::AccountState,
        }
    );

    let deleted = delete_item(&root, inserted_key).expect("delete should succeed");
    assert!(deleted);
    assert!(
        find_key(&root, inserted_key, false, &mut |_| None)
            .expect("post-delete lookup should succeed")
            .is_none()
    );
}

#[test]
fn shamap_loaded_tree_mutation_helpers_accept_minimum_payloads() {
    let key = Uint256::from_array([0x5A; 32]);
    let root = SHAMapTreeNode::new_inner(1);

    let inserted = add_item(
        &root,
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(key, vec![0x01; 12]),
    )
    .expect("minimum transaction insert should succeed");
    assert!(inserted);

    let found = find_key(&root, key, false, &mut |_| None)
        .expect("lookup should succeed")
        .expect("minimum transaction leaf should resolve");
    assert_eq!(found.get_type(), SHAMapNodeType::TransactionNm);
    assert_eq!(
        found
            .peek_item()
            .expect("minimum transaction leaf should carry an item")
            .data(),
        &[0x01; 12]
    );

    let updated = update_item(
        &root,
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(key, vec![0x02; 12]),
    )
    .expect("minimum transaction update should succeed");
    assert!(updated);

    let updated_found = find_key(&root, key, false, &mut |_| None)
        .expect("updated lookup should succeed")
        .expect("updated minimum transaction leaf should resolve");
    assert_eq!(
        updated_found
            .peek_item()
            .expect("updated minimum transaction leaf should carry an item")
            .data(),
        &[0x02; 12]
    );
}

#[test]
fn fetch_backed_delete_collapses_hash_only_sole_leaf_like_loaded_delete() {
    let target =
        Uint256::from_hex("1000000000000000000000000000000000000000000000000000000000000000")
            .expect("target key should parse");
    let survivor =
        Uint256::from_hex("1100000000000000000000000000000000000000000000000000000000000000")
            .expect("survivor key should parse");
    let other =
        Uint256::from_hex("2000000000000000000000000000000000000000000000000000000000000000")
            .expect("other key should parse");

    let build = |cowid| {
        let mut tree = MutableTree::new(cowid);
        for (key, fill) in [(target, 1), (survivor, 2), (other, 3)] {
            tree.add_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(key, vec![fill; 12]),
            )
            .expect("fixture insert should succeed");
        }
        tree
    };

    let mut loaded = build(1);
    assert!(
        loaded
            .delete_item(target)
            .expect("loaded delete should succeed")
    );
    loaded.root().update_hash_deep();
    let expected_hash = loaded.root().get_hash();

    let source = build(2);
    let source_root = source.root();
    let (target_leaf, target_path) =
        walk_towards_key_with_path(&source_root, target, false, &mut |_| None)
            .expect("target path should resolve");
    let target_leaf = target_leaf.expect("target leaf should exist");
    let shared_inner = target_path[1].node.clone();
    shared_inner.update_hash_deep();
    source_root.update_hash_deep();
    let survivor_leaf = source
        .find_key(survivor)
        .expect("survivor lookup should succeed")
        .expect("survivor leaf should exist");
    let other_leaf = source
        .find_key(other)
        .expect("other lookup should succeed")
        .expect("other leaf should exist");

    let shallow_inner = SHAMapTreeNode::new_inner(0);
    shallow_inner.set_child_hash(0, target_leaf.get_hash());
    shallow_inner.set_child_hash(1, survivor_leaf.get_hash());
    shallow_inner.update_hash_deep();
    assert_eq!(shallow_inner.get_hash(), shared_inner.get_hash());

    let shallow_root = SHAMapTreeNode::new_inner(0);
    shallow_root.set_child_hash(1, shallow_inner.get_hash());
    shallow_root.set_child_hash(2, other_leaf.get_hash());
    shallow_root.update_hash_deep();
    assert_eq!(shallow_root.get_hash(), source_root.get_hash());

    let mut stored = HashMap::new();
    stored.insert(shallow_inner.get_hash(), shallow_inner);
    stored.insert(target_leaf.get_hash(), target_leaf);
    stored.insert(survivor_leaf.get_hash(), survivor_leaf);
    stored.insert(other_leaf.get_hash(), other_leaf);
    assert!(shallow_root.get_child(1).is_none());
    let mut backed = MutableTree::from_loaded_root(shallow_root, 3);
    let mut fetches = 0usize;
    let deleted = backed
        .delete_item_with_fetch(target, &mut |hash| {
            fetches += 1;
            stored.get(&hash).cloned()
        })
        .expect("fetch-backed delete should succeed");
    assert!(deleted, "target must remain reachable through stored nodes");

    assert!(fetches >= 2, "path and sole sibling should be fetched");
    backed.root().update_hash_deep();
    assert_eq!(
        backed.root().get_hash(),
        expected_hash,
        "hash-only sole descendants must collapse to the canonical SHAMap shape"
    );
}

#[test]
fn shamap_mutable_snapshot_helpers_match_narrow_cpp_roles() {
    let key = Uint256::from_array([0xB1; 32]);
    let mut original = MutableTree::new(1);
    original
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![5; 12]),
        )
        .expect("initial insert should succeed");

    let original_root = original.root();
    let original_hash = original
        .find_key(key)
        .expect("original lookup should succeed")
        .expect("original leaf should exist")
        .get_hash();

    let mut snapshot = original.mutable_snapshot(2);
    snapshot
        .update_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![6; 12]),
        )
        .expect("snapshot update should succeed");

    let original_leaf = original
        .find_key(key)
        .expect("original lookup should still succeed")
        .expect("original leaf should still exist");
    let snapshot_leaf = snapshot
        .find_key(key)
        .expect("snapshot lookup should succeed")
        .expect("snapshot leaf should exist");

    assert_eq!(original_leaf.get_hash(), original_hash);
    assert_ne!(snapshot_leaf.get_hash(), original_hash);
    assert!(same_node(&original.root(), &original_root));
    assert!(!same_node(&original.root(), &snapshot.root()));
}

#[test]
fn shamap_loaded_unshare_helpers_match_narrow_cpp_roles() {
    let key = Uint256::from_array([0xC7; 32]);
    let mut original = MutableTree::new(1);
    original
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![7; 12]),
        )
        .expect("insert should succeed");

    let original_root = original.root();
    let mut foreign_owner = MutableTree::from_loaded_root(original_root.clone(), 2);
    let count = foreign_owner.share_loaded_subtree();

    assert_eq!(count, 2);
    assert_eq!(foreign_owner.root().cowid(), 0);
    assert_eq!(original_root.cowid(), 1);
    assert!(!same_node(&foreign_owner.root(), &original_root));
    assert!(
        foreign_owner
            .find_key(key)
            .expect("shared-tree lookup should succeed")
            .is_some()
    );
}

#[test]
fn shamap_mutable_tree_walk_subtree_matches_narrow_cpp_roles() {
    let key = Uint256::from_array([0xD7; 32]);
    let mut tree = MutableTree::new(1);
    tree.add_item(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![21; 12]),
    )
    .expect("insert should succeed");

    let original_leaf = tree
        .find_key(key)
        .expect("lookup should succeed")
        .expect("leaf should exist");
    let original_item = original_leaf
        .peek_item()
        .expect("leaf should carry an item");
    let original_hash = original_leaf.get_hash();

    let unshared = tree.unshare();
    assert_eq!(unshared, 2);
    assert_eq!(tree.root().cowid(), 0);
    let shared_leaf = tree
        .find_key(key)
        .expect("lookup should succeed")
        .expect("leaf should remain reachable");
    assert_eq!(shared_leaf.cowid(), 0);
    assert_eq!(tree.unshare(), 0);

    let mut owned_again = MutableTree::new(2);
    owned_again
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![21; 12]),
        )
        .expect("owned insert should succeed");
    let owned_leaf_before = owned_again
        .find_key(key)
        .expect("lookup should succeed")
        .expect("leaf should exist");
    let mut write_order = Vec::new();
    let flushed = owned_again.flush_dirty(&mut |node| {
        write_order.push(node.is_leaf());
        if node.is_leaf() {
            SHAMapTreeNode::new_leaf_with_hash(
                node.get_type(),
                original_item.clone(),
                0,
                original_hash,
            )
        } else {
            node
        }
    });

    assert_eq!(flushed, 2);
    assert_eq!(write_order, vec![true, false]);
    let replaced_leaf = owned_again
        .find_key(key)
        .expect("lookup should succeed")
        .expect("leaf should remain reachable");
    assert_eq!(replaced_leaf.cowid(), 0);
    assert_eq!(replaced_leaf.get_hash(), original_hash);
    assert!(!same_node(&replaced_leaf, &owned_leaf_before));
}

#[test]
fn shamap_flush_dirty_store_writer_matches_narrow_cpp_roles() {
    let key = Uint256::from_array([0xE7; 32]);
    let clock = ManualClock::new(0);
    let cache = TreeNodeCache::new("tree", 8, Duration::seconds(1), clock);
    let mut tree = MutableTree::new(1);
    tree.add_item(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![31; 12]),
    )
    .expect("insert should succeed");

    let original_leaf = tree
        .find_key(key)
        .expect("lookup should succeed")
        .expect("leaf should exist");
    let original_item = original_leaf
        .peek_item()
        .expect("leaf should carry an item");
    let canonical_leaf = SHAMapTreeNode::new_leaf_with_hash(
        SHAMapNodeType::AccountState,
        original_item,
        0,
        original_leaf.get_hash(),
    );
    let mut cached = canonical_leaf.clone();
    assert!(
        !cache.canonicalize_replace_client(canonical_leaf.get_hash().as_uint256(), &mut cached)
    );

    let mut sink = RecordingNodeStore::default();
    {
        let mut writer =
            CanonicalNodeWriter::new(&cache, NodeObjectType::AccountNode, 77, &mut sink);
        let flushed = tree.flush_dirty(&mut |node| {
            writer
                .write_node(node)
                .expect("current subtree walk should only produce prefix-serializable nodes")
        });
        assert_eq!(flushed, 2);
    }

    let leaf_after = tree
        .find_key(key)
        .expect("lookup should succeed")
        .expect("leaf should remain reachable");
    assert!(same_node(&leaf_after, &canonical_leaf));
    assert_eq!(sink.stored.len(), 2);
    assert_eq!(sink.stored[0].object_type(), NodeObjectType::AccountNode);
    assert_eq!(sink.stored[0].ledger_seq(), 77);
    assert_eq!(
        sink.stored[0].hash(),
        canonical_leaf.get_hash().as_uint256()
    );
    assert_eq!(
        sink.stored[0].data(),
        canonical_leaf
            .serialize_with_prefix()
            .expect("leaf should serialize with prefix")
    );

    let root_after = tree.root();
    assert_eq!(sink.stored[1].object_type(), NodeObjectType::AccountNode);
    assert_eq!(sink.stored[1].ledger_seq(), 77);
    assert_eq!(sink.stored[1].hash(), root_after.get_hash().as_uint256());
    assert_eq!(
        sink.stored[1].data(),
        root_after
            .serialize_with_prefix()
            .expect("inner root should serialize with prefix")
    );
}

#[test]
fn shamap_storage_tree_flush_dirty_matches_narrow_cpp_owner_roles() {
    let key = Uint256::from_array([0xF7; 32]);
    let cache = Arc::new(TreeNodeCache::new(
        "tree",
        8,
        Duration::seconds(1),
        ManualClock::new(0),
    ));

    let mut unbacked = StorageTree::new(1, false, 101, cache.clone());
    unbacked.root().set_child(
        2,
        Some(SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![41; 12]),
            1,
        )),
    );
    unbacked.root().update_hash_deep();

    let mut unbacked_sink = RecordingNodeStore::default();
    let unbacked_flushed = unbacked
        .flush_dirty(NodeObjectType::AccountNode, &mut unbacked_sink)
        .expect("unbacked flush should walk without storing");

    assert_eq!(unbacked_flushed, 2);
    assert!(unbacked_sink.stored.is_empty());
    assert_eq!(unbacked.root().cowid(), 0);

    let canonical_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, vec![41; 12]),
        0,
    );
    let mut cached = canonical_leaf.clone();
    assert!(
        !cache.canonicalize_replace_client(canonical_leaf.get_hash().as_uint256(), &mut cached)
    );

    let mut backed = StorageTree::new(2, true, 102, cache);
    backed.root().set_child(
        2,
        Some(SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            canonical_leaf
                .peek_item()
                .expect("canonical leaf should carry an item"),
            2,
            canonical_leaf.get_hash(),
        )),
    );
    backed.root().update_hash_deep();

    let mut backed_sink = RecordingNodeStore::default();
    let backed_flushed = backed
        .flush_dirty(NodeObjectType::AccountNode, &mut backed_sink)
        .expect("backed flush should store");

    assert_eq!(backed_flushed, 2);
    let leaf_after = backed
        .root()
        .get_child(2)
        .expect("flushed root should still carry the leaf");
    assert!(same_node(&leaf_after, &canonical_leaf));
    assert_eq!(backed_sink.stored.len(), 2);
    assert_eq!(backed_sink.stored[0].ledger_seq(), 102);
    assert_eq!(
        backed_sink.stored[0].object_type(),
        NodeObjectType::AccountNode
    );
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
fn shamap_storage_tree_walk_map_with_family_matches_owner_fetch_roles() {
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

    let missing_hash = sample_hash(0x97);
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
            "storage-walk-map-owner-parity",
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
    let tree = StorageTree::from_loaded_root_with_family(root.clone(), 2, true, 207, &family);
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
    assert!(root.get_child(2).is_none());
    assert!(!tree.is_full());
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
fn shamap_storage_tree_walk_map_parallel_with_family_logs_worker_failures() {
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

    let panic_hash = sample_hash(0x98);
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
            "storage-walk-map-parallel-panic-parity",
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
    let tree = StorageTree::from_loaded_root_with_family(root.clone(), 2, true, 208, &family);
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
fn shamap_storage_tree_owner_full_gate_matches_narrow_cpp_fetch_roles() {
    let key = Uint256::from_hex("2000000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let missing_hash = sample_hash(0x91);
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(2, missing_hash);
    root.update_hash();

    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "storage-tree-full-gate",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
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
fn shamap_storage_tree_owner_config_matches_narrow_cpp_roles() {
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
            "storage-tree-owner-config-parity",
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
        assert_eq!(fetcher.fetches.lock().clone(), vec![missing_hash]);
    });
    let reporter_state = reporter.lock();
    assert_eq!(
        reporter_state.by_seq,
        vec![(206, *missing_hash.as_uint256())]
    );
}

#[test]
fn shamap_storage_tree_mutation_wrappers_match_narrow_cpp_owner_roles() {
    let first_key =
        Uint256::from_hex("3100000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let second_key =
        Uint256::from_hex("3200000000000000000000000000000000000000000000000000000000000000")
            .expect("hex should parse");
    let mut tree = StorageTree::new(
        1,
        true,
        109,
        Arc::new(TreeNodeCache::new(
            "storage-tree-mutation-parity",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
    );

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
            .expect("lookup should succeed"),
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
            .expect("delete should report false for absent keys")
    );
    assert_eq!(
        tree.peek_item(second_key, &mut |_| None)
            .expect("post-delete lookup should succeed"),
        None
    );
}

#[test]
fn shamap_storage_tree_hash_matches_narrow_cpp_owner_roles() {
    let key = Uint256::from_hex("3400000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let mut tree = StorageTree::new(
        1,
        true,
        111,
        Arc::new(TreeNodeCache::new(
            "storage-tree-hash-parity",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
    );
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
fn shamap_storage_tree_mutable_snapshot_matches_narrow_cpp_owner_roles() {
    let key = Uint256::from_hex("3300000000000000000000000000000000000000000000000000000000000000")
        .expect("hex should parse");
    let mut original = StorageTree::new(
        1,
        true,
        110,
        Arc::new(TreeNodeCache::new(
            "storage-tree-snapshot-parity",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
    );
    original
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![8; 12]),
        )
        .expect("insert should succeed");
    original.set_full();

    let mut snapshot = original.mutable_snapshot(2);

    assert!(snapshot.backed());
    assert_eq!(snapshot.ledger_seq(), 110);
    assert!(original.is_full());
    assert!(!snapshot.is_full());
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
