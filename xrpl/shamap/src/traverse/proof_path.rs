//! Current the reference implementation proof-path verification role.

use crate::family::{MissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher};
use crate::node_id::{SHAMapNodeId, select_branch};
use crate::search::{walk_towards_key_with_path, walk_towards_key_with_path_and_family};
use crate::traversal::{TraversalError, descend_no_store, descend_throw};
use crate::tree_node::SHAMapTreeNode;
use basics::base_uint::Uint256;
use basics::blob::Blob;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::CacheClock;
use std::hash::BuildHasher;

pub fn verify_proof_path(root_hash: Uint256, key: Uint256, path: &[Blob]) -> bool {
    if path.is_empty() || path.len() > 65 {
        return false;
    }

    let mut hash = SHAMapHash::new(root_hash);
    for (depth, blob) in path.iter().rev().enumerate() {
        let Ok(Some(node)) = SHAMapTreeNode::make_from_wire(blob) else {
            return false;
        };

        node.update_hash();
        if node.get_hash() != hash {
            return false;
        }

        if node.is_inner() {
            let Ok(node_id) = SHAMapNodeId::create_id(depth, key) else {
                return false;
            };
            hash = node.get_child_hash(select_branch(node_id, key));
        } else {
            return depth + 1 == path.len();
        }
    }

    false
}

pub fn has_leaf_node(
    root: &SharedIntrusive<SHAMapTreeNode>,
    tag: Uint256,
    target_node_hash: SHAMapHash,
) -> bool {
    let mut node = root.clone();
    let mut node_id = SHAMapNodeId::default();

    if !node.is_inner() {
        return node.get_hash() == target_node_hash;
    }

    loop {
        let branch = select_branch(node_id, tag);
        if node.is_empty_branch(branch) {
            return false;
        }

        if node.get_child_hash(branch) == target_node_hash {
            return true;
        }

        let Some(child) = descend_no_store(&node, branch, true, &mut |_| None) else {
            return false;
        };
        node = child;

        if !node.is_inner() {
            return false;
        }

        node_id = node_id
            .get_child_node_id(branch)
            .expect("branch selection must stay within SHAMap depth bounds");
    }
}

pub fn has_leaf_node_backed<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    tag: Uint256,
    target_node_hash: SHAMapHash,
    backed: bool,
    fetch: &mut F,
) -> Result<bool, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    let mut node = root.clone();
    let mut node_id = SHAMapNodeId::default();

    if !node.is_inner() {
        return Ok(node.get_hash() == target_node_hash);
    }

    loop {
        let branch = select_branch(node_id, tag);
        if node.is_empty_branch(branch) {
            return Ok(false);
        }

        if node.get_child_hash(branch) == target_node_hash {
            return Ok(true);
        }

        node = descend_throw(&node, branch, backed, fetch)?
            .expect("non-empty branches should resolve to a child or error");
        node_id = node_id
            .get_child_node_id(branch)
            .expect("branch selection must stay within SHAMap depth bounds");

        if !node.is_inner() {
            return Ok(false);
        }
    }
}

pub fn has_leaf_node_with_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    tag: Uint256,
    target_node_hash: SHAMapHash,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<bool, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    has_leaf_node_backed(root, tag, target_node_hash, backed, &mut |hash| {
        family.fetch_cached_node_or_acquire_by_seq(hash, ledger_seq)
    })
}

pub fn has_inner_node<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    target_node_id: SHAMapNodeId,
    target_node_hash: SHAMapHash,
    backed: bool,
    fetch: &mut F,
) -> Result<bool, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    let mut node = root.clone();
    let mut node_id = SHAMapNodeId::default();

    while node.is_inner() && node_id.get_depth() < target_node_id.get_depth() {
        let branch = select_branch(node_id, target_node_id.get_node_id());
        if node.is_empty_branch(branch) {
            return Ok(false);
        }

        node = descend_throw(&node, branch, backed, fetch)?
            .expect("non-empty branches should resolve to a child or error");
        node_id = node_id
            .get_child_node_id(branch)
            .expect("branch selection must stay within SHAMap depth bounds");
    }

    Ok(node.is_inner() && node.get_hash() == target_node_hash)
}

pub fn has_inner_node_with_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    target_node_id: SHAMapNodeId,
    target_node_hash: SHAMapHash,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<bool, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    has_inner_node(
        root,
        target_node_id,
        target_node_hash,
        backed,
        &mut |hash| family.fetch_cached_node_or_acquire_by_seq(hash, ledger_seq),
    )
}

pub fn get_proof_path(root: &SharedIntrusive<SHAMapTreeNode>, key: Uint256) -> Option<Vec<Blob>> {
    get_proof_path_backed(root, key, false, &mut |_| None)
        .ok()
        .flatten()
}

pub fn get_proof_path_backed<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    key: Uint256,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<Vec<Blob>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    let (leaf, path_entries) = walk_towards_key_with_path(root, key, backed, fetch)?;
    finalize_proof_path(key, leaf, path_entries)
}

pub fn get_proof_path_with_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    key: Uint256,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<Option<Vec<Blob>>, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    let (leaf, path_entries) =
        walk_towards_key_with_path_and_family(root, key, backed, ledger_seq, family)?;
    finalize_proof_path_with_family(key, leaf, path_entries, family)
}

fn finalize_proof_path(
    key: Uint256,
    leaf: Option<SharedIntrusive<SHAMapTreeNode>>,
    mut path_entries: Vec<crate::search::NodePathEntry>,
) -> Result<Option<Vec<Blob>>, TraversalError> {
    let Some(leaf) = leaf else {
        return Ok(None);
    };
    let Some(item) = leaf.peek_item() else {
        return Ok(None);
    };
    if item.key() != key {
        return Ok(None);
    }

    let mut path = Vec::with_capacity(path_entries.len());
    while let Some(entry) = path_entries.pop() {
        let Ok(blob) = entry.node.serialize_for_wire() else {
            return Ok(None);
        };
        path.push(blob);
    }

    Ok(Some(path))
}

fn finalize_proof_path_with_family<CLOCK, S, FB, F, MR, NS>(
    key: Uint256,
    leaf: Option<SharedIntrusive<SHAMapTreeNode>>,
    mut path_entries: Vec<crate::search::NodePathEntry>,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<Option<Vec<Blob>>, TraversalError> {
    let Some(leaf) = leaf else {
        family.log_debug(&format!("no path to {key}"));
        return Ok(None);
    };
    let Some(item) = leaf.peek_item() else {
        family.log_debug(&format!("no path to {key}"));
        return Ok(None);
    };
    if item.key() != key {
        family.log_debug(&format!("no path to {key}"));
        return Ok(None);
    }

    let mut path = Vec::with_capacity(path_entries.len());
    while let Some(entry) = path_entries.pop() {
        let Ok(blob) = entry.node.serialize_for_wire() else {
            return Ok(None);
        };
        path.push(blob);
    }

    family.log_debug(&format!(
        "getPath for key {key}, path length {}",
        path.len()
    ));
    Ok(Some(path))
}

#[cfg(test)]
mod tests {
    use super::{
        get_proof_path, get_proof_path_backed, get_proof_path_with_family, has_inner_node,
        has_inner_node_with_family, has_leaf_node, has_leaf_node_backed, has_leaf_node_with_family,
        verify_proof_path,
    };
    use crate::family::{
        JournalLevel, MissingNodeReporter, NullFullBelowCache, SHAMapFamily, SHAMapJournal,
        SHAMapNodeFetcher,
    };
    use crate::item::SHAMapItem;
    use crate::node_id::SHAMapNodeId;
    use crate::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use basics::base_uint::Uint256;
    use basics::intrusive_pointer::SharedIntrusive;
    use basics::sha_map_hash::SHAMapHash;
    use basics::tagged_cache::ManualClock;
    use std::sync::{Arc, Mutex};
    use time::Duration;

    fn sample_uint256(fill: u8) -> Uint256 {
        Uint256::from_array([fill; 32])
    }

    fn sample_hash(fill: u8) -> SHAMapHash {
        SHAMapHash::new(sample_uint256(fill))
    }

    #[test]
    fn single_leaf_proof_path_matches_current_cpp_role() {
        let key = sample_uint256(0x11);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![1; 12]),
            0,
        );
        let leaf_wire = leaf
            .serialize_for_wire()
            .expect("leaf wire serialization should succeed");

        assert!(verify_proof_path(
            *leaf.get_hash().as_uint256(),
            sample_uint256(0xAA),
            std::slice::from_ref(&leaf_wire)
        ));
        assert!(!verify_proof_path(
            Uint256::zero(),
            sample_uint256(0xAA),
            &[leaf_wire]
        ));
    }

    #[test]
    fn inner_plus_leaf_proof_path_matches_current_cpp_role() {
        let key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![7; 12]),
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

        let mut wrong_root_wire = root_wire;
        wrong_root_wire[0] ^= 0xFF;
        assert!(!verify_proof_path(
            *root.get_hash().as_uint256(),
            key,
            &[leaf_wire, wrong_root_wire]
        ));
    }

    #[test]
    fn has_leaf_node_matches_current_loaded_tree_role() {
        let key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![9; 12]),
            0,
        );
        let root = SHAMapTreeNode::new_inner(0);
        root.set_child_hash(1, leaf.get_hash());

        assert!(has_leaf_node(&root, key, leaf.get_hash()));
        assert!(!has_leaf_node(&root, key, sample_hash(0x99)));
    }

    #[test]
    fn has_leaf_node_backed_matches_current_cpp_role() {
        let key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![4; 12]),
            0,
        );
        let inner = SHAMapTreeNode::new_inner(1);
        inner.set_child_hash(2, leaf.get_hash());
        inner.share_child(2, &leaf);
        inner.update_hash_deep();

        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(1, inner.get_hash());
        root.share_child(1, &inner);
        root.update_hash_deep();

        assert!(
            has_leaf_node_backed(&root, key, leaf.get_hash(), false, &mut |_| None)
                .expect("loaded lookup should succeed")
        );
        assert!(
            !has_leaf_node_backed(&root, key, sample_hash(0x99), false, &mut |_| None)
                .expect("loaded lookup should succeed")
        );
    }

    #[test]
    fn has_inner_node_matches_current_cpp_role() {
        let inner = SHAMapTreeNode::new_inner(1);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(0x23), vec![1; 12]),
            0,
        );
        inner.set_child_hash(6, leaf.get_hash());
        inner.share_child(6, &leaf);
        inner.update_hash_deep();

        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(2, inner.get_hash());
        root.share_child(2, &inner);
        root.update_hash_deep();

        let target = SHAMapNodeId::default()
            .get_child_node_id(2)
            .expect("child id should exist");

        assert!(
            has_inner_node(&root, target, inner.get_hash(), false, &mut |_| None)
                .expect("loaded lookup should succeed")
        );
        assert!(
            !has_inner_node(&root, target, sample_hash(0x99), false, &mut |_| None)
                .expect("loaded lookup should succeed")
        );
    }

    #[derive(Debug, Default)]
    struct RecordingMissingNodeReporter {
        by_seq: Arc<Mutex<Vec<(u32, Uint256)>>>,
    }

    impl MissingNodeReporter for RecordingMissingNodeReporter {
        fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
            self.by_seq
                .lock()
                .expect("shared reporter mutex must not be poisoned")
                .push((ref_num, node_hash));
        }

        fn missing_node_acquire_by_hash(&self, _ref_hash: Uint256, _ref_num: u32) {}
    }

    #[derive(Debug, Clone)]
    struct FixedFetcher(Option<SharedIntrusive<SHAMapTreeNode>>);

    impl SHAMapNodeFetcher for FixedFetcher {
        fn fetch_node(&self, _hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.0.clone()
        }
    }

    #[derive(Debug, Default)]
    struct RecordingJournal {
        entries: Arc<Mutex<Vec<(JournalLevel, String)>>>,
    }

    impl RecordingJournal {
        fn entries(&self) -> Vec<(JournalLevel, String)> {
            self.entries
                .lock()
                .expect("shared journal mutex must not be poisoned")
                .clone()
        }
    }

    impl SHAMapJournal for RecordingJournal {
        fn log(&self, level: JournalLevel, message: &str) {
            self.entries
                .lock()
                .expect("shared journal mutex must not be poisoned")
                .push((level, message.to_owned()));
        }
    }

    #[test]
    fn has_inner_node_with_family_fetches_missing_children_when_backed() {
        let inner = SHAMapTreeNode::new_inner(1);
        inner.set_child_hash(3, sample_hash(0x34));
        inner.update_hash();

        let root = SHAMapTreeNode::new_inner(0);
        root.set_child_hash(4, inner.get_hash());
        root.update_hash();

        let target = SHAMapNodeId::default()
            .get_child_node_id(4)
            .expect("child id should exist");
        let reporter = Arc::new(Mutex::new(Vec::new()));
        let family = SHAMapFamily::new(
            Arc::new(crate::tree_node_cache::TreeNodeCache::new(
                "proof-inner-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            FixedFetcher(Some(inner.clone())),
            RecordingMissingNodeReporter {
                by_seq: reporter.clone(),
            },
        );

        assert!(
            has_inner_node_with_family(&root, target, inner.get_hash(), true, 600, &family)
                .expect("backed lookup should succeed")
        );
        assert!(
            reporter
                .lock()
                .expect("shared reporter mutex must not be poisoned")
                .is_empty()
        );
    }

    #[test]
    fn has_leaf_node_with_family_fetches_missing_children_when_backed() {
        let key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
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

        let reporter = Arc::new(Mutex::new(Vec::new()));
        let family = SHAMapFamily::new(
            Arc::new(crate::tree_node_cache::TreeNodeCache::new(
                "proof-leaf-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            FixedFetcher(Some(inner.clone())),
            RecordingMissingNodeReporter {
                by_seq: reporter.clone(),
            },
        );

        assert!(
            has_leaf_node_with_family(&root, key, leaf.get_hash(), true, 601, &family)
                .expect("backed lookup should succeed")
        );
        assert!(
            reporter
                .lock()
                .expect("shared reporter mutex must not be poisoned")
                .is_empty()
        );
    }

    #[test]
    fn get_proof_path_returns_leaf_to_root_wire_blobs() {
        let key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![5; 12]),
            0,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(1, leaf.get_hash());
        root.share_child(1, &leaf);
        root.update_hash();

        let path = get_proof_path(&root, key).expect("loaded tree should produce a proof path");
        assert_eq!(path.len(), 2);
        assert_eq!(
            path[0],
            leaf.serialize_for_wire()
                .expect("leaf wire serialization should succeed")
        );
        assert_eq!(
            path[1],
            root.serialize_for_wire()
                .expect("root wire serialization should succeed")
        );

        let missing_key = sample_uint256(0xFF);
        assert!(get_proof_path(&root, missing_key).is_none());
    }

    #[test]
    fn get_proof_path_backed_fetches_missing_children_when_backed() {
        let key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![7; 12]),
            0,
        );
        let inner = SHAMapTreeNode::new_inner(1);
        inner.set_child_hash(2, leaf.get_hash());
        inner.share_child(2, &leaf);
        inner.update_hash_deep();

        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(1, inner.get_hash());
        root.update_hash();

        let path = get_proof_path_backed(&root, key, true, &mut |hash| {
            (hash == inner.get_hash()).then_some(inner.clone())
        })
        .expect("backed path lookup should succeed")
        .expect("key should produce a proof path");

        assert_eq!(path.len(), 3);
        assert_eq!(
            path[0],
            leaf.serialize_for_wire()
                .expect("leaf wire serialization should succeed")
        );
        assert_eq!(
            path[1],
            inner
                .serialize_for_wire()
                .expect("inner wire serialization should succeed")
        );
        assert_eq!(
            path[2],
            root.serialize_for_wire()
                .expect("root wire serialization should succeed")
        );
    }

    #[test]
    fn get_proof_path_with_family_fetches_missing_children_when_backed() {
        let key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
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

        let journal = Arc::new(RecordingJournal::default());
        let family = SHAMapFamily::new_with_journal(
            Arc::new(crate::tree_node_cache::TreeNodeCache::new(
                "proof-path-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            FixedFetcher(Some(inner.clone())),
            RecordingMissingNodeReporter {
                by_seq: Arc::new(Mutex::new(Vec::new())),
            },
            journal.clone(),
        );

        let path = get_proof_path_with_family(&root, key, true, 602, &family)
            .expect("backed path lookup should succeed")
            .expect("key should produce a proof path");

        assert_eq!(path.len(), 3);
        assert_eq!(
            path[0],
            leaf.serialize_for_wire()
                .expect("leaf wire serialization should succeed")
        );
        assert_eq!(
            path[1],
            inner
                .serialize_for_wire()
                .expect("inner wire serialization should succeed")
        );
        assert_eq!(
            path[2],
            root.serialize_for_wire()
                .expect("root wire serialization should succeed")
        );
        assert_eq!(journal.entries().len(), 1);
        assert_eq!(journal.entries()[0].0, JournalLevel::Debug);
        assert!(journal.entries()[0].1.contains("getPath for key"));
    }

    #[test]
    fn get_proof_path_with_family_logs_when_no_path_exists() {
        let key = sample_uint256(0xA4);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(0xB5), vec![8; 12]),
            0,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(1, leaf.get_hash());
        root.share_child(1, &leaf);
        root.update_hash();

        let journal = Arc::new(RecordingJournal::default());
        let family = SHAMapFamily::new_with_journal(
            Arc::new(crate::tree_node_cache::TreeNodeCache::new(
                "proof-path-no-path-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            FixedFetcher(None),
            RecordingMissingNodeReporter {
                by_seq: Arc::new(Mutex::new(Vec::new())),
            },
            journal.clone(),
        );

        let path = get_proof_path_with_family(&root, key, false, 603, &family)
            .expect("loaded path lookup should succeed");

        assert!(path.is_none());
        assert_eq!(journal.entries().len(), 1);
        assert_eq!(journal.entries()[0].0, JournalLevel::Debug);
        assert!(journal.entries()[0].1.contains("no path to"));
    }
}
