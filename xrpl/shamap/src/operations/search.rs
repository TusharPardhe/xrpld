//! Current `SHAMap::walkTowardsKey` and `SHAMap::findKey` read helpers.

use crate::family::{MissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher};
use crate::node_id::{SHAMapNodeId, select_branch};
use crate::traversal::{TraversalError, descend_throw, descend_throw_with_family};
use crate::tree_node::SHAMapTreeNode;
use basics::base_uint::Uint256;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::CacheClock;
use std::hash::BuildHasher;

/// Issue a memory prefetch hint for the next SHAMap tree level.
///
/// After descending to a child inner node, we already know which branch
/// we'll take next (from the key bits). Prefetching that child's memory
/// hides one level of pointer-chasing latency (~50-80 cycles on L2 miss).
#[inline(always)]
fn prefetch_next_child(node: &SHAMapTreeNode, node_id: SHAMapNodeId, key: Uint256) {
    if !node.is_inner() {
        return;
    }
    let branch = select_branch(node_id, key);
    if node.is_empty_branch(branch) {
        return;
    }
    if let Some(child) = node.get_child(branch) {
        let ptr = &*child as *const SHAMapTreeNode;
        unsafe {
            #[cfg(target_arch = "x86_64")]
            std::arch::x86_64::_mm_prefetch(ptr as *const i8, std::arch::x86_64::_MM_HINT_T0);
            #[cfg(target_arch = "x86")]
            std::arch::x86::_mm_prefetch(ptr as *const i8, std::arch::x86::_MM_HINT_T0);
            #[cfg(target_arch = "aarch64")]
            {
                // Use inline asm for stable aarch64 prefetch (PRFM PLDL1KEEP)
                std::arch::asm!("prfm pldl1keep, [{ptr}]", ptr = in(reg) ptr, options(nostack, preserves_flags));
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct NodePathEntry {
    pub node: SharedIntrusive<SHAMapTreeNode>,
    pub node_id: SHAMapNodeId,
}

pub fn walk_towards_key<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    walk_towards_key_impl(root, id, backed, fetch, |_, _| {})
}

pub fn walk_towards_key_with_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    walk_towards_key(root, id, backed, &mut |hash| {
        family.fetch_cached_node_or_acquire_by_seq(hash, ledger_seq)
    })
}

pub fn walk_towards_key_with_path<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    fetch: &mut F,
) -> Result<(Option<SharedIntrusive<SHAMapTreeNode>>, Vec<NodePathEntry>), TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    let mut path = Vec::new();
    let leaf = walk_towards_key_impl(root, id, backed, fetch, |node, node_id| {
        path.push(NodePathEntry {
            node: node.clone(),
            node_id,
        });
    })?;
    Ok((leaf, path))
}

pub fn walk_towards_key_with_path_and_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<(Option<SharedIntrusive<SHAMapTreeNode>>, Vec<NodePathEntry>), TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    let mut path = Vec::new();
    let leaf = walk_towards_key_impl_with_family(
        root,
        id,
        backed,
        ledger_seq,
        family,
        |node, node_id| {
            path.push(NodePathEntry {
                node: node.clone(),
                node_id,
            });
        },
    )?;
    Ok((leaf, path))
}

pub fn find_key<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    let Some(leaf) = walk_towards_key(root, id, backed, fetch)? else {
        return Ok(None);
    };

    if leaf.peek_item().is_some_and(|item| item.key() == id) {
        Ok(Some(leaf))
    } else {
        Ok(None)
    }
}

pub fn find_key_with_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    let Some(leaf) = walk_towards_key_with_family(root, id, backed, ledger_seq, family)? else {
        return Ok(None);
    };

    if leaf.peek_item().is_some_and(|item| item.key() == id) {
        Ok(Some(leaf))
    } else {
        Ok(None)
    }
}

fn walk_towards_key_impl<F, V>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    fetch: &mut F,
    mut visit: V,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    V: FnMut(&SharedIntrusive<SHAMapTreeNode>, SHAMapNodeId),
{
    let mut node = root.clone();
    let mut node_id = SHAMapNodeId::default();

    while node.is_inner() {
        visit(&node, node_id);
        let branch = select_branch(node_id, id);
        if node.is_empty_branch(branch) {
            return Ok(None);
        }

        let next = descend_throw(&node, branch, backed, fetch)?
            .expect("non-empty branches should resolve to a child or error");
        node_id = node_id
            .get_child_node_id(branch)
            .expect("branch selection must stay within SHAMap depth bounds");
        prefetch_next_child(&next, node_id, id);
        node = next;
    }

    visit(&node, node_id);
    Ok(Some(node))
}

fn walk_towards_key_impl_with_family<CLOCK, S, FB, F, MR, NS, V>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
    mut visit: V,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
    V: FnMut(&SharedIntrusive<SHAMapTreeNode>, SHAMapNodeId),
{
    let mut node = root.clone();
    let mut node_id = SHAMapNodeId::default();

    while node.is_inner() {
        visit(&node, node_id);
        let branch = select_branch(node_id, id);
        if node.is_empty_branch(branch) {
            return Ok(None);
        }

        let next = descend_throw_with_family(&node, branch, backed, ledger_seq, family)?
            .expect("non-empty branches should resolve to a child or error");
        node_id = node_id
            .get_child_node_id(branch)
            .expect("branch selection must stay within SHAMap depth bounds");
        prefetch_next_child(&next, node_id, id);
        node = next;
    }

    visit(&node, node_id);
    Ok(Some(node))
}

#[cfg(test)]
mod tests {
    use super::{
        find_key, find_key_with_family, walk_towards_key, walk_towards_key_with_family,
        walk_towards_key_with_path,
    };
    use crate::family::{MissingNodeReporter, NullFullBelowCache, NullNodeFetcher, SHAMapFamily};
    use crate::item::SHAMapItem;
    use crate::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use crate::tree_node_cache::TreeNodeCache;
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

    fn same_node(
        left: &SharedIntrusive<SHAMapTreeNode>,
        right: &SharedIntrusive<SHAMapTreeNode>,
    ) -> bool {
        std::ptr::eq(&**left, &**right)
    }

    #[derive(Debug, Default)]
    struct RecordingMissingNodeReporter {
        by_seq: Mutex<Vec<(u32, Uint256)>>,
    }

    impl MissingNodeReporter for RecordingMissingNodeReporter {
        fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
            self.by_seq
                .lock()
                .expect("recording reporter by-seq mutex must not be poisoned")
                .push((ref_num, node_hash));
        }

        fn missing_node_acquire_by_hash(&self, _ref_hash: Uint256, _ref_num: u32) {}
    }

    #[test]
    fn walk_towards_key_with_path_collects_root_to_leaf_entries() {
        let key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![1; 12]),
            0,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(1, leaf.get_hash());
        root.share_child(1, &leaf);

        let (resolved, path) = walk_towards_key_with_path(&root, key, false, &mut |_| None)
            .expect("loaded path walk should succeed");

        let resolved = resolved.expect("leaf should be reached");
        assert!(same_node(&resolved, &leaf));
        assert_eq!(path.len(), 2);
        assert!(path[0].node.is_inner());
        assert!(path[1].node.is_leaf());
        assert_eq!(path[0].node_id.get_depth(), 0);
        assert_eq!(path[1].node_id.get_depth(), 1);
    }

    #[test]
    fn walk_towards_key_fetches_missing_children_when_backed() {
        let key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![2; 12]),
            0,
            sample_hash(7),
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(1, sample_hash(7));

        let mut fetch_calls = 0;
        let resolved = walk_towards_key(&root, key, true, &mut |_| {
            fetch_calls += 1;
            Some(leaf.clone())
        })
        .expect("backed walk should succeed")
        .expect("fetched leaf should be reached");

        assert!(same_node(&resolved, &leaf));
        assert_eq!(fetch_calls, 1);
        assert!(root.get_child(1).is_some());
    }

    #[test]
    fn find_key_requires_exact_leaf_key_match() {
        let stored_key = sample_uint256(0x10);
        let requested_key = sample_uint256(0x1F);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(stored_key, vec![3; 12]),
            0,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(1, leaf.get_hash());
        root.share_child(1, &leaf);

        let found = find_key(&root, stored_key, false, &mut |_| None)
            .expect("exact match lookup should succeed");
        assert!(found.is_some());

        let mismatched = find_key(&root, requested_key, false, &mut |_| None)
            .expect("mismatched lookup should succeed");
        assert!(mismatched.is_none());
    }

    #[test]
    fn family_backed_key_walk_reports_missing_fetches_by_ledger_seq() {
        #[derive(Debug)]
        struct SharedReporter(Arc<Mutex<RecordingMissingNodeReporter>>);

        impl MissingNodeReporter for SharedReporter {
            fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
                self.0
                    .lock()
                    .expect("shared reporter mutex must not be poisoned")
                    .missing_node_acquire_by_seq(ref_num, node_hash);
            }

            fn missing_node_acquire_by_hash(&self, _ref_hash: Uint256, _ref_num: u32) {}
        }

        let requested_key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(1, sample_hash(0x91));

        let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "search-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            SharedReporter(reporter.clone()),
        );

        let error = walk_towards_key_with_family(&root, requested_key, true, 800, &family)
            .expect_err("missing fetched child should surface as a traversal error");
        assert_eq!(
            error,
            crate::traversal::TraversalError::MissingNode(sample_hash(0x91))
        );
        assert!(
            find_key_with_family(&root, requested_key, true, 801, &family).is_err(),
            "family-backed exact lookup should report the same traversal miss"
        );

        let reporter = reporter
            .lock()
            .expect("shared reporter mutex must not be poisoned");
        assert_eq!(
            *reporter
                .by_seq
                .lock()
                .expect("recording reporter by-seq mutex must not be poisoned"),
            vec![
                (800, *sample_hash(0x91).as_uint256()),
                (801, *sample_hash(0x91).as_uint256()),
            ]
        );
    }
}
