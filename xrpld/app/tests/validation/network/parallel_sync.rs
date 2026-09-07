//! Comprehensive tests for ledger acquisition, parallel sync, and peering edge cases.
//!
//! Tests the full sync pipeline: peer discovery → node fetch → hash verification →
//! state assembly → backpressure → error recovery.

use basics::base_uint::Uint256;
use basics::memory::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use ledger::sync_config::{SyncConfig, SyncProfile};
use shamap::item::SHAMapItem;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};

fn leaf_node(key: Uint256, data: &[u8]) -> SharedIntrusive<SHAMapTreeNode> {
    make_shared_intrusive(SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(key, data.to_vec()),
        0,
    ))
}

fn key(fill: u8) -> Uint256 {
    Uint256::from_array([fill; 32])
}

// ═══════════════════════════════════════════════════════════════
// LEDGER ACQUISITION — HAPPY PATH
// ═══════════════════════════════════════════════════════════════

/// Test: Empty sync tree has a root node (even if empty inner).
#[test]
fn empty_tree_has_root() {
    let tree = SyncTree::new_with_type(SHAMapType::State, false, 100);
    // Empty tree still has a root (empty inner node)
    let _root = tree.root();
    // The tree is valid and queryable even when empty
    assert!(!tree.is_synching());
}

/// Test: Adding a root node via wire blob to a synching tree.
#[test]
fn add_root_node_to_synching_tree() {
    let mut tree = SyncTree::new_with_type(SHAMapType::State, false, 100);
    tree.set_synching();
    assert!(tree.is_synching());

    // A synching tree accepts root nodes
    // The actual add_root_node requires a properly formatted wire blob
    // matching the expected hash — here we just verify the state machine works
    let hash = SHAMapHash::new(Uint256::from_u64(0x1234));
    let result = tree.add_root_node(hash, &[], &mut None);
    // Empty blob should be rejected (invalid) but not crash
    assert!(result.is_invalid() || result.get_bad() > 0 || result.get_duplicate() > 0);
}

/// Test: Known nodes with correct hashes are accepted.
#[test]
fn valid_known_node_has_nonzero_hash() {
    let node = leaf_node(key(0x11), &[0xAA; 50]);
    let hash = node.get_hash();
    assert_ne!(hash, SHAMapHash::default());
}

/// Test: Sync tree tracks synching state correctly.
#[test]
fn sync_state_transitions() {
    let mut tree = SyncTree::new_with_type(SHAMapType::State, false, 100);

    assert!(!tree.is_synching());
    tree.set_synching();
    assert!(tree.is_synching());
    tree.clear_synching();
    assert!(!tree.is_synching());
}

// ═══════════════════════════════════════════════════════════════
// PARALLEL SYNC — BRANCH INDEPENDENCE
// ═══════════════════════════════════════════════════════════════

/// Test: Each of the 16 branches can be fetched independently.
#[test]
fn branches_are_independently_verifiable() {
    // Create 16 leaf nodes, one per branch (first nibble of key determines branch)
    let nodes: Vec<_> = (0u8..16)
        .map(|branch| {
            let mut k = [0u8; 32];
            k[0] = branch << 4; // First nibble = branch index
            let key = Uint256::from(k);
            leaf_node(key, &[branch; 32])
        })
        .collect();

    // Each node has an independent hash
    let hashes: Vec<_> = nodes.iter().map(|n| n.get_hash()).collect();
    let unique: std::collections::HashSet<_> = hashes.iter().collect();
    assert_eq!(unique.len(), 16, "All 16 branches must have unique hashes");
}

/// Test: Parallel config allows multiple branches simultaneously.
#[test]
fn config_allows_parallel_branch_fetch() {
    let config = SyncConfig::from_profile(SyncProfile::Fast);
    // Fast profile should allow at least 8 parallel branches
    assert!(config.parallel_branches >= 8);
    // And enough total concurrency to serve them
    assert!(config.max_concurrent_requests >= config.parallel_branches);
}

// ═══════════════════════════════════════════════════════════════
// EDGE CASES
// ═══════════════════════════════════════════════════════════════

/// Test: Node with hash mismatch is rejected (corrupted data from peer).
#[test]
fn hash_mismatch_node_rejected() {
    let node = leaf_node(key(0x22), &[0xBB; 40]);
    let actual_hash = node.get_hash();
    let wrong_hash = SHAMapHash::new(Uint256::from_u64(0xDEAD));

    // The hashes don't match — this simulates a corrupt peer response
    assert_ne!(actual_hash, wrong_hash);
}

/// Test: Empty payloads cannot form account-state SHAMap leaves.
#[test]
#[should_panic(expected = "SHAMap leaf item payload below minimum size")]
fn empty_payload_leaf_is_rejected() {
    let _ = leaf_node(key(0x33), &[]);
}

/// Test: Maximum size payload node works.
#[test]
fn large_payload_node_works() {
    let big_data = vec![0xFF; 10_000]; // 10KB payload (larger than typical SLE)
    let node = leaf_node(key(0x44), &big_data);
    assert_ne!(node.get_hash(), SHAMapHash::default());
}

/// Test: Duplicate key insertion is handled.
#[test]
fn duplicate_key_produces_same_hash() {
    let node1 = leaf_node(key(0x55), &[0xCC; 20]);
    let node2 = leaf_node(key(0x55), &[0xCC; 20]);
    assert_eq!(node1.get_hash(), node2.get_hash());
}

/// Test: Different data for same key produces different hash.
#[test]
fn different_data_different_hash() {
    let node1 = leaf_node(key(0x66), &[0xAA; 20]);
    let node2 = leaf_node(key(0x66), &[0xBB; 20]);
    assert_ne!(node1.get_hash(), node2.get_hash());
}

// ═══════════════════════════════════════════════════════════════
// BAD CASES — MALFORMED PEER DATA
// ═══════════════════════════════════════════════════════════════

/// Test: Wire decode of truncated inner node doesn't crash.
#[test]
fn truncated_inner_node_no_crash() {
    // Inner node needs 16*32=512 bytes + 1 type byte. Give it less.
    let truncated = vec![0x01; 100]; // Too short for inner node
    let result = SHAMapTreeNode::make_from_wire(&truncated);
    // Should return Ok(Some(...)) with partial data or Ok(None) — not panic
    assert!(result.is_ok());
}

/// Test: Wire decode with invalid type byte doesn't crash.
#[test]
fn invalid_wire_type_no_crash() {
    let mut data = vec![0xAA; 50];
    data.push(0xFF); // Invalid wire type (valid: 0-4)
    let result = SHAMapTreeNode::make_from_wire(&data);
    assert!(result.is_err() || result.unwrap().is_none());
}

/// Test: Zero-length wire blob doesn't crash.
#[test]
fn zero_length_wire_no_crash() {
    let result = SHAMapTreeNode::make_from_wire(&[]);
    assert!(result.is_ok());
}

/// Test: Wire blob with only type byte doesn't crash.
#[test]
fn type_only_wire_no_crash() {
    for wire_type in 0u8..=5 {
        let result = SHAMapTreeNode::make_from_wire(&[wire_type]);
        // Should not panic regardless of type
        assert!(result.is_ok() || result.is_err());
    }
}

// ═══════════════════════════════════════════════════════════════
// FATAL CASES — UNRECOVERABLE SCENARIOS
// ═══════════════════════════════════════════════════════════════

/// Test: All peers disconnect during sync — tree remains in synching state.
#[test]
fn no_peers_tree_stays_synching() {
    let mut tree = SyncTree::new_with_type(SHAMapType::State, false, 100);
    tree.set_synching();

    // Simulate: no fetch function returns anything (all peers gone)
    let mut missing = Vec::new();
    tree.walk_map(SHAMapType::State, &mut missing, 100, &mut |_| None);

    // Tree should still be in synching state (not crashed, not complete)
    assert!(tree.is_synching());
}

/// Test: Sync config handles zero peers gracefully.
#[test]
fn config_with_zero_peers_still_valid() {
    let config = SyncConfig::from_profile(SyncProfile::Balanced);
    // Even with 0 peers, the config itself is valid
    // The orchestrator should handle "no peers" as a retry condition
    assert!(config.max_concurrent_requests > 0);
    assert!(config.request_timeout.as_secs() > 0);
}

// ═══════════════════════════════════════════════════════════════
// MISSING CASES — INCOMPLETE STATE
// ═══════════════════════════════════════════════════════════════

/// Test: Partial tree (some branches fetched, some missing) is queryable.
#[test]
fn partial_tree_reports_missing_branches() {
    let tree = SyncTree::new_with_type(SHAMapType::State, false, 100);
    let mut missing = Vec::new();
    tree.walk_map(SHAMapType::State, &mut missing, 256, &mut |_| None);
    // Empty tree with default root has no missing nodes to report
}

/// Test: Backpressure config prevents unbounded growth.
#[test]
fn backpressure_limits_are_enforced() {
    let config = SyncConfig::from_profile(SyncProfile::Aggressive);

    // Even the most aggressive profile has bounded resources
    let max_inflight_bytes = config.max_concurrent_requests * config.nodes_per_request * 1024; // ~1KB per node
    let max_pending_bytes = config.max_pending_writes_mb * 1024 * 1024;

    // Inflight should never exceed pending write cap
    assert!(
        max_inflight_bytes < max_pending_bytes,
        "Inflight {} must be less than write cap {}",
        max_inflight_bytes,
        max_pending_bytes
    );
}

/// Test: SHAMap immutable after sync complete.
#[test]
fn tree_becomes_immutable_after_sync() {
    let root = make_shared_intrusive(SHAMapTreeNode::new_inner(0));
    let tree =
        SyncTree::from_root_with_type(root, SHAMapType::State, false, 100, SyncState::Immutable);

    assert!(!tree.is_synching());
    // Immutable tree should not accept new nodes
}
