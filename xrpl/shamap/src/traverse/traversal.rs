//! Current fetch-backed `SHAMap` descend helpers.

use crate::family::{MissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher};
use crate::node_id::SHAMapNodeId;
use crate::tree_node::SHAMapTreeNode;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::CacheClock;
use std::hash::BuildHasher;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraversalError {
    MissingNode(SHAMapHash),
    RootNotFound,
    View,
}

pub fn descend<F>(
    parent: &SharedIntrusive<SHAMapTreeNode>,
    branch: usize,
    backed: bool,
    fetch: &mut F,
) -> Option<SharedIntrusive<SHAMapTreeNode>>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    assert!(parent.is_inner(), "descend requires an inner parent node");

    let loaded = parent.get_child(branch);
    if loaded.is_some() || !backed || parent.is_empty_branch(branch) {
        return loaded;
    }

    let fetched = fetch(parent.get_child_hash(branch))?;
    Some(parent.canonicalize_child(branch, fetched))
}

pub fn descend_with_family<CLOCK, S, FB, F, MR, NS>(
    parent: &SharedIntrusive<SHAMapTreeNode>,
    branch: usize,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Option<SharedIntrusive<SHAMapTreeNode>>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    descend(parent, branch, backed, &mut |hash| {
        family.fetch_cached_node_or_acquire_by_seq(hash, ledger_seq)
    })
}

pub fn descend_throw<F>(
    parent: &SharedIntrusive<SHAMapTreeNode>,
    branch: usize,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    let node = descend(parent, branch, backed, fetch);
    if node.is_none() && !parent.is_empty_branch(branch) {
        return Err(TraversalError::MissingNode(parent.get_child_hash(branch)));
    }

    Ok(node)
}

pub fn descend_throw_with_family<CLOCK, S, FB, F, MR, NS>(
    parent: &SharedIntrusive<SHAMapTreeNode>,
    branch: usize,
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
    descend_throw(parent, branch, backed, &mut |hash| {
        family.fetch_cached_node_or_acquire_by_seq(hash, ledger_seq)
    })
}

pub fn descend_no_store<F>(
    parent: &SharedIntrusive<SHAMapTreeNode>,
    branch: usize,
    backed: bool,
    fetch: &mut F,
) -> Option<SharedIntrusive<SHAMapTreeNode>>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    assert!(
        parent.is_inner(),
        "descend_no_store requires an inner parent node"
    );

    let loaded = parent.get_child(branch);
    if loaded.is_some() || !backed || parent.is_empty_branch(branch) {
        return loaded;
    }

    fetch(parent.get_child_hash(branch))
}

pub fn descend_no_store_with_family<CLOCK, S, FB, F, MR, NS>(
    parent: &SharedIntrusive<SHAMapTreeNode>,
    branch: usize,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Option<SharedIntrusive<SHAMapTreeNode>>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    descend_no_store(parent, branch, backed, &mut |hash| {
        family.fetch_cached_node_or_acquire_by_seq(hash, ledger_seq)
    })
}

pub fn descend_with_id<F>(
    parent: &SharedIntrusive<SHAMapTreeNode>,
    parent_id: SHAMapNodeId,
    branch: usize,
    fetch: &mut F,
) -> (Option<SharedIntrusive<SHAMapTreeNode>>, SHAMapNodeId)
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    assert!(
        parent.is_inner(),
        "descend_with_id requires an inner parent node"
    );
    assert!(
        !parent.is_empty_branch(branch),
        "descend_with_id requires a non-empty branch"
    );

    let child = if let Some(loaded) = parent.get_child(branch) {
        Some(loaded)
    } else {
        fetch(parent.get_child_hash(branch))
            .map(|fetched| parent.canonicalize_child(branch, fetched))
    };

    let child_id = parent_id
        .get_child_node_id(branch)
        .expect("branch selection must stay within SHAMap depth bounds");
    (child, child_id)
}

pub fn descend_with_id_with_family<CLOCK, S, FB, F, MR, NS>(
    parent: &SharedIntrusive<SHAMapTreeNode>,
    parent_id: SHAMapNodeId,
    branch: usize,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> (Option<SharedIntrusive<SHAMapTreeNode>>, SHAMapNodeId)
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    descend_with_id(parent, parent_id, branch, &mut |hash| {
        family.fetch_cached_node_or_acquire_by_seq(hash, ledger_seq)
    })
}

#[cfg(test)]
mod tests {
    use super::{
        TraversalError, descend, descend_no_store, descend_no_store_with_family, descend_throw,
        descend_throw_with_family, descend_with_family, descend_with_id,
    };
    use crate::family::{MissingNodeReporter, NullFullBelowCache, NullNodeFetcher, SHAMapFamily};
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
    fn descend_reuses_loaded_child_without_fetching() {
        let child = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(1), vec![7; 12]),
            0,
            sample_hash(9),
        );
        let parent = SHAMapTreeNode::new_inner(1);
        parent.set_child_hash(3, sample_hash(9));
        parent.share_child(3, &child);

        let mut fetch_calls = 0;
        let resolved = descend(&parent, 3, true, &mut |_| {
            fetch_calls += 1;
            None
        })
        .expect("loaded child should be returned");

        assert!(same_node(&resolved, &child));
        assert_eq!(fetch_calls, 0);
    }

    #[test]
    fn descend_fetches_and_canonicalizes_missing_child() {
        let child = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(2), vec![8; 12]),
            0,
            sample_hash(7),
        );
        let parent = SHAMapTreeNode::new_inner(1);
        parent.set_child_hash(4, sample_hash(7));

        let mut fetch_calls = 0;
        let first = descend(&parent, 4, true, &mut |_| {
            fetch_calls += 1;
            Some(child.clone())
        })
        .expect("fetch should provide the child");
        let second = descend(&parent, 4, true, &mut |_| {
            fetch_calls += 1;
            None
        })
        .expect("canonicalized child should now be loaded");

        assert!(same_node(&first, &child));
        assert!(same_node(&second, &child));
        assert_eq!(fetch_calls, 1);
    }

    #[test]
    fn descend_no_store_fetches_without_attaching_child() {
        let child = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(sample_uint256(3), vec![9; 12]),
            0,
            sample_hash(6),
        );
        let parent = SHAMapTreeNode::new_inner(1);
        parent.set_child_hash(5, sample_hash(6));

        let fetched = descend_no_store(&parent, 5, true, &mut |_| Some(child.clone()))
            .expect("fetch should provide the child");
        assert!(same_node(&fetched, &child));
        assert!(parent.get_child(5).is_none());
    }

    #[test]
    fn descend_throw_reports_missing_non_empty_branch() {
        let parent = SHAMapTreeNode::new_inner(1);
        parent.set_child_hash(2, sample_hash(4));

        let error = descend_throw(&parent, 2, true, &mut |_| None)
            .expect_err("missing loaded or fetched child should be reported");
        assert_eq!(error, TraversalError::MissingNode(sample_hash(4)));

        let empty = descend_throw(&parent, 3, true, &mut |_| None)
            .expect("empty branches should not error");
        assert!(empty.is_none());
    }

    #[test]
    fn family_backed_descend_helpers_report_misses_by_ledger_seq() {
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

        let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
        let family = SHAMapFamily::new(
            Arc::new(crate::tree_node_cache::TreeNodeCache::new(
                "traversal-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            SharedReporter(reporter.clone()),
        );
        let parent = SHAMapTreeNode::new_inner(1);
        parent.set_child_hash(2, sample_hash(4));

        assert!(descend_with_family(&parent, 2, true, 700, &family).is_none());
        assert!(descend_no_store_with_family(&parent, 2, true, 701, &family).is_none());
        let error = descend_throw_with_family(&parent, 2, true, 702, &family)
            .expect_err("family-backed missing branches should still error");
        assert_eq!(error, TraversalError::MissingNode(sample_hash(4)));

        let reporter = reporter
            .lock()
            .expect("shared reporter mutex must not be poisoned");
        assert_eq!(
            *reporter
                .by_seq
                .lock()
                .expect("recording reporter by-seq mutex must not be poisoned"),
            vec![
                (700, *sample_hash(4).as_uint256()),
                (701, *sample_hash(4).as_uint256()),
                (702, *sample_hash(4).as_uint256()),
            ]
        );
    }

    #[test]
    fn descend_with_id_returns_child_and_next_node_id() {
        let child = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(4), vec![1; 12]),
            0,
            sample_hash(5),
        );
        let parent = SHAMapTreeNode::new_inner(1);
        let parent_id = SHAMapNodeId::default();
        parent.set_child_hash(1, sample_hash(5));

        let (resolved, child_id) =
            descend_with_id(&parent, parent_id, 1, &mut |_| Some(child.clone()));

        let resolved = resolved.expect("fetch should provide the child");
        assert!(same_node(&resolved, &child));
        assert_eq!(child_id.get_depth(), 1);
        assert_eq!(
            parent
                .get_child(1)
                .expect("child should be canonicalized")
                .get_hash(),
            sample_hash(5)
        );
    }
}
