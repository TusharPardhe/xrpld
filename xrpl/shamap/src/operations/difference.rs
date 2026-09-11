//! Current `SHAMap::visitDifferences` caller seam.

use crate::family::{MissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher};
use crate::node_id::SHAMapNodeId;
use crate::proof_path::{
    has_inner_node, has_inner_node_with_family, has_leaf_node_backed, has_leaf_node_with_family,
};
use crate::traversal::{TraversalError, descend_throw, descend_throw_with_family};
use crate::tree_node::{BRANCH_FACTOR, SHAMapTreeNode};
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::CacheClock;
use std::hash::BuildHasher;

pub fn visit_differences<FS, FH, V>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    have: Option<&SharedIntrusive<SHAMapTreeNode>>,
    self_backed: bool,
    self_fetch: &mut FS,
    have_backed: bool,
    have_fetch: &mut FH,
    visit: &mut V,
) -> Result<(), TraversalError>
where
    FS: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    FH: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    V: FnMut(&SharedIntrusive<SHAMapTreeNode>) -> bool,
{
    if root.get_hash().is_zero() {
        return Ok(());
    }

    if have.is_some_and(|other| root.get_hash() == other.get_hash()) {
        return Ok(());
    }

    if root.is_leaf() {
        let key = root
            .peek_item()
            .expect("leaf roots should carry an item")
            .key();
        let missing_from_have = match have {
            None => true,
            Some(other) => {
                !has_leaf_node_backed(other, key, root.get_hash(), have_backed, have_fetch)?
            }
        };
        if missing_from_have && !visit(root) {
            return Ok(());
        }
        return Ok(());
    }

    let mut stack = vec![(root.clone(), SHAMapNodeId::default())];
    while let Some((node, node_id)) = stack.pop() {
        if !visit(&node) {
            return Ok(());
        }

        for branch in 0..BRANCH_FACTOR {
            if node.is_empty_branch(branch) {
                continue;
            }

            let child_hash = node.get_child_hash(branch);
            let child_id = node_id
                .get_child_node_id(branch)
                .expect("branch selection must stay within SHAMap depth bounds");
            let next = descend_throw(&node, branch, self_backed, self_fetch)?
                .expect("non-empty branches should resolve to a child or error");

            if next.is_inner() {
                let missing_from_have = match have {
                    None => true,
                    Some(other) => {
                        !has_inner_node(other, child_id, child_hash, have_backed, have_fetch)?
                    }
                };
                if missing_from_have {
                    stack.push((next, child_id));
                }
            } else {
                let key = next
                    .peek_item()
                    .expect("leaf children should carry an item")
                    .key();
                let missing_from_have = match have {
                    None => true,
                    Some(other) => {
                        !has_leaf_node_backed(other, key, child_hash, have_backed, have_fetch)?
                    }
                };
                if missing_from_have && !visit(&next) {
                    return Ok(());
                }
            }
        }
    }

    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn visit_differences_with_families<
    CLOCKS,
    SS,
    FBS,
    FS,
    MRS,
    NSS,
    CLOCKH,
    SH,
    FBH,
    FH,
    MRH,
    NSH,
    V,
>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    have: Option<&SharedIntrusive<SHAMapTreeNode>>,
    self_backed: bool,
    self_ledger_seq: u32,
    self_family: &SHAMapFamily<CLOCKS, SS, FBS, FS, MRS, NSS>,
    have_backed: bool,
    have_ledger_seq: u32,
    have_family: Option<&SHAMapFamily<CLOCKH, SH, FBH, FH, MRH, NSH>>,
    visit: &mut V,
) -> Result<(), TraversalError>
where
    CLOCKS: CacheClock,
    SS: BuildHasher + Clone,
    FS: SHAMapNodeFetcher,
    MRS: MissingNodeReporter,
    CLOCKH: CacheClock,
    SH: BuildHasher + Clone,
    FH: SHAMapNodeFetcher,
    MRH: MissingNodeReporter,
    V: FnMut(&SharedIntrusive<SHAMapTreeNode>) -> bool,
{
    if root.get_hash().is_zero() {
        return Ok(());
    }

    if have.is_some_and(|other| root.get_hash() == other.get_hash()) {
        return Ok(());
    }

    if root.is_leaf() {
        let key = root
            .peek_item()
            .expect("leaf roots should carry an item")
            .key();
        let missing_from_have = match have {
            None => true,
            Some(other) => !has_leaf_node_with_family(
                other,
                key,
                root.get_hash(),
                have_backed,
                have_ledger_seq,
                have_family.expect("have tree requires a family for membership checks"),
            )?,
        };
        if missing_from_have && !visit(root) {
            return Ok(());
        }
        return Ok(());
    }

    let mut stack = vec![(root.clone(), SHAMapNodeId::default())];
    while let Some((node, node_id)) = stack.pop() {
        if !visit(&node) {
            return Ok(());
        }

        for branch in 0..BRANCH_FACTOR {
            if node.is_empty_branch(branch) {
                continue;
            }

            let child_hash = node.get_child_hash(branch);
            let child_id = node_id
                .get_child_node_id(branch)
                .expect("branch selection must stay within SHAMap depth bounds");
            let next = descend_throw_with_family(
                &node,
                branch,
                self_backed,
                self_ledger_seq,
                self_family,
            )?
            .expect("non-empty branches should resolve to a child or error");

            if next.is_inner() {
                let missing_from_have = match have {
                    None => true,
                    Some(other) => !has_inner_node_with_family(
                        other,
                        child_id,
                        child_hash,
                        have_backed,
                        have_ledger_seq,
                        have_family.expect("have tree requires a family for membership checks"),
                    )?,
                };
                if missing_from_have {
                    stack.push((next, child_id));
                }
            } else {
                let key = next
                    .peek_item()
                    .expect("leaf children should carry an item")
                    .key();
                let missing_from_have = match have {
                    None => true,
                    Some(other) => !has_leaf_node_with_family(
                        other,
                        key,
                        child_hash,
                        have_backed,
                        have_ledger_seq,
                        have_family.expect("have tree requires a family for membership checks"),
                    )?,
                };
                if missing_from_have && !visit(&next) {
                    return Ok(());
                }
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{visit_differences, visit_differences_with_families};
    use crate::family::{
        NullFullBelowCache, NullMissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher,
    };
    use crate::item::SHAMapItem;
    use crate::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use basics::base_uint::Uint256;
    use basics::intrusive_pointer::SharedIntrusive;
    use basics::sha_map_hash::SHAMapHash;
    use basics::tagged_cache::ManualClock;
    use parking_lot::Mutex;
    use std::collections::HashMap;
    use std::sync::Arc;
    use time::Duration;

    fn key(hex: &str) -> Uint256 {
        Uint256::from_hex(hex).expect("hex should parse")
    }

    fn sample_hash(fill: u8) -> SHAMapHash {
        SHAMapHash::new(Uint256::from_array([fill; 32]))
    }

    fn build_difference_fixture() -> (
        SharedIntrusive<SHAMapTreeNode>,
        SharedIntrusive<SHAMapTreeNode>,
        Uint256,
        Uint256,
    ) {
        let shared_key = key("1000000000000000000000000000000000000000000000000000000000000000");
        let deep_key = key("4100000000000000000000000000000000000000000000000000000000000000");
        let top_leaf_key = key("9000000000000000000000000000000000000000000000000000000000000000");

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

        (root, have, deep_key, top_leaf_key)
    }

    #[test]
    fn visit_differences_reports_only_nodes_missing_from_have_in_current_order() {
        let (root, have, deep_key, top_leaf_key) = build_difference_fixture();
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
    fn visit_differences_stops_when_callback_returns_false() {
        let (root, have, _, _) = build_difference_fixture();
        let mut calls = 0;

        visit_differences(
            &root,
            Some(&have),
            false,
            &mut |_| None,
            false,
            &mut |_| None,
            &mut |_| {
                calls += 1;
                calls < 2
            },
        )
        .expect("difference walk should succeed");

        assert_eq!(calls, 2);
    }

    #[test]
    fn visit_differences_fetches_and_canonicalizes_missing_self_children() {
        let leaf_key = key("2000000000000000000000000000000000000000000000000000000000000000");
        let expected_hash = sample_hash(0x44);
        let fetched_leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(leaf_key, vec![4; 12]),
            0,
            expected_hash,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(2, expected_hash);
        root.update_hash_deep();

        let mut fetch_calls = 0;
        let mut visited = 0;
        visit_differences(
            &root,
            None,
            true,
            &mut |_| {
                fetch_calls += 1;
                Some(fetched_leaf.clone())
            },
            false,
            &mut |_| None,
            &mut |_| {
                visited += 1;
                true
            },
        )
        .expect("fetch-backed difference walk should succeed");

        assert_eq!(fetch_calls, 1);
        assert_eq!(visited, 2);
        assert!(root.get_child(2).is_some());
    }

    #[test]
    fn visit_differences_fetches_have_map_for_hash_membership_checks() {
        let key = key("3000000000000000000000000000000000000000000000000000000000000000");
        let expected_hash = sample_hash(0x66);

        let self_leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![5; 12]),
            0,
            expected_hash,
        );
        let self_root = SHAMapTreeNode::new_inner(1);
        self_root.set_child_hash(3, expected_hash);
        self_root.share_child(3, &self_leaf);
        self_root.update_hash_deep();

        let have_root = SHAMapTreeNode::new_inner(1);
        have_root.set_child_hash(3, expected_hash);
        have_root.update_hash_deep();
        let have_leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![5; 12]),
            0,
            expected_hash,
        );

        let mut have_fetch_calls = 0;
        let mut visited = 0;
        visit_differences(
            &self_root,
            Some(&have_root),
            false,
            &mut |_| None,
            true,
            &mut |_| {
                have_fetch_calls += 1;
                Some(have_leaf.clone())
            },
            &mut |_| {
                visited += 1;
                true
            },
        )
        .expect("difference walk should succeed");

        assert_eq!(have_fetch_calls, 0);
        assert_eq!(visited, 0);
    }

    #[derive(Debug, Default)]
    struct MappingFetcher {
        nodes: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
        fetches: Mutex<Vec<SHAMapHash>>,
    }

    impl SHAMapNodeFetcher for MappingFetcher {
        fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.fetches.lock().push(hash);
            self.nodes.get(&hash).cloned()
        }
    }

    #[test]
    fn visit_differences_with_families_fetches_and_canonicalizes_missing_self_children() {
        let leaf_key = key("5000000000000000000000000000000000000000000000000000000000000000");
        let expected_hash = sample_hash(0x77);
        let fetched_leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(leaf_key, vec![7; 12]),
            0,
            expected_hash,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(5, expected_hash);
        root.update_hash();

        let mut nodes = HashMap::new();
        nodes.insert(expected_hash, fetched_leaf.clone());
        let family = SHAMapFamily::new(
            Arc::new(crate::tree_node_cache::TreeNodeCache::new(
                "difference-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            MappingFetcher {
                nodes,
                fetches: Mutex::new(Vec::new()),
            },
            NullMissingNodeReporter,
        );

        let mut visited = 0;
        visit_differences_with_families(
            &root,
            None,
            true,
            920,
            &family,
            false,
            0,
            None::<
                &SHAMapFamily<
                    ManualClock,
                    std::collections::hash_map::RandomState,
                    NullFullBelowCache,
                    MappingFetcher,
                    NullMissingNodeReporter,
                    (),
                >,
            >,
            &mut |_| {
                visited += 1;
                true
            },
        )
        .expect("family-backed difference walk should succeed");

        assert_eq!(visited, 2);
        assert!(root.get_child(5).is_some());
        family.with_fetcher(|fetcher| {
            assert_eq!(fetcher.fetches.lock().clone(), vec![expected_hash])
        });
    }

    #[test]
    fn visit_differences_returns_traversal_errors_for_missing_have_leaf_membership() {
        let key = key("6000000000000000000000000000000000000000000000000000000000000000");
        let root = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![8; 12]),
            0,
        );

        let have_root = SHAMapTreeNode::new_inner(1);
        have_root.set_child_hash(6, sample_hash(0x88));
        have_root.update_hash_deep();

        let err = visit_differences(
            &root,
            Some(&have_root),
            false,
            &mut |_| None,
            true,
            &mut |_| None,
            &mut |_| true,
        )
        .expect_err("missing have-tree child should surface as a traversal error");

        assert_eq!(
            err,
            crate::traversal::TraversalError::MissingNode(sample_hash(0x88))
        );
    }

    #[test]
    fn visit_differences_with_families_returns_traversal_errors_for_missing_have_leaf_membership() {
        let key = key("7000000000000000000000000000000000000000000000000000000000000000");
        let root = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![9; 12]),
            0,
        );

        let have_root = SHAMapTreeNode::new_inner(1);
        let missing_hash = sample_hash(0x99);
        have_root.set_child_hash(7, missing_hash);
        have_root.update_hash();

        let family = SHAMapFamily::new(
            Arc::new(crate::tree_node_cache::TreeNodeCache::new(
                "difference-family-error",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            MappingFetcher {
                nodes: HashMap::new(),
                fetches: Mutex::new(Vec::new()),
            },
            NullMissingNodeReporter,
        );

        let err = visit_differences_with_families(
            &root,
            Some(&have_root),
            false,
            910,
            &family,
            true,
            910,
            Some(&family),
            &mut |_| true,
        )
        .expect_err("missing have-tree child should surface as a traversal error");

        assert_eq!(
            err,
            crate::traversal::TraversalError::MissingNode(missing_hash)
        );
    }
}
