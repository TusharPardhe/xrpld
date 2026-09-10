//! Current `SHAMap::compare` and debug-style `SHAMap::deepCompare` helpers.

use crate::family::{MissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher};
use crate::item::SHAMapItem;
use crate::traversal::{TraversalError, descend, descend_throw};
use crate::tree_node::{BRANCH_FACTOR, SHAMapTreeNode};
use basics::base_uint::Uint256;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::CacheClock;
use std::collections::BTreeMap;
use std::hash::BuildHasher;

pub type DeltaItem = (Option<SHAMapItem>, Option<SHAMapItem>);
pub type Delta = BTreeMap<Uint256, DeltaItem>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DeepCompareEvent {
    HashMismatch,
    UnableToFetchInnerNode,
}

#[allow(clippy::too_many_arguments)]
pub fn compare<FL, FR>(
    left_root: &SharedIntrusive<SHAMapTreeNode>,
    right_root: &SharedIntrusive<SHAMapTreeNode>,
    left_backed: bool,
    left_fetch: &mut FL,
    right_backed: bool,
    right_fetch: &mut FR,
    differences: &mut Delta,
    mut max_count: i32,
) -> Result<bool, TraversalError>
where
    FL: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    FR: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    ensure_loaded_hashes(left_root);
    ensure_loaded_hashes(right_root);
    if left_root.get_hash() == right_root.get_hash() {
        return Ok(true);
    }

    let mut stack = vec![(left_root.clone(), right_root.clone())];
    while let Some((left, right)) = stack.pop() {
        if left.is_leaf() && right.is_leaf() {
            let left_item = left.peek_item().expect("leaf nodes should carry an item");
            let right_item = right.peek_item().expect("leaf nodes should carry an item");

            if left_item.key() == right_item.key() {
                if left_item.data() != right_item.data()
                    && !record_difference(
                        differences,
                        left_item.key(),
                        Some(left_item),
                        Some(right_item),
                        &mut max_count,
                    )
                {
                    return Ok(false);
                }
            } else {
                if !record_difference(
                    differences,
                    left_item.key(),
                    Some(left_item),
                    None,
                    &mut max_count,
                ) {
                    return Ok(false);
                }

                if !record_difference(
                    differences,
                    right_item.key(),
                    None,
                    Some(right_item),
                    &mut max_count,
                ) {
                    return Ok(false);
                }
            }
            continue;
        }

        if left.is_inner() && right.is_leaf() {
            let right_item = right.peek_item().expect("leaf nodes should carry an item");
            if !walk_branch(
                &left,
                Some(right_item),
                true,
                differences,
                &mut max_count,
                left_backed,
                left_fetch,
            )? {
                return Ok(false);
            }
            continue;
        }

        if left.is_leaf() && right.is_inner() {
            let left_item = left.peek_item().expect("leaf nodes should carry an item");
            if !walk_branch(
                &right,
                Some(left_item),
                false,
                differences,
                &mut max_count,
                right_backed,
                right_fetch,
            )? {
                return Ok(false);
            }
            continue;
        }

        for branch in 0..BRANCH_FACTOR {
            if left.get_child_hash(branch) == right.get_child_hash(branch) {
                continue;
            }

            if right.is_empty_branch(branch) {
                let left_child = descend_throw(&left, branch, left_backed, left_fetch)?
                    .expect("non-empty branches should resolve to a child or error");
                if !walk_branch(
                    &left_child,
                    None,
                    true,
                    differences,
                    &mut max_count,
                    left_backed,
                    left_fetch,
                )? {
                    return Ok(false);
                }
            } else if left.is_empty_branch(branch) {
                let right_child = descend_throw(&right, branch, right_backed, right_fetch)?
                    .expect("non-empty branches should resolve to a child or error");
                if !walk_branch(
                    &right_child,
                    None,
                    false,
                    differences,
                    &mut max_count,
                    right_backed,
                    right_fetch,
                )? {
                    return Ok(false);
                }
            } else {
                let left_child = descend_throw(&left, branch, left_backed, left_fetch)?
                    .expect("non-empty branches should resolve to a child or error");
                let right_child = descend_throw(&right, branch, right_backed, right_fetch)?
                    .expect("non-empty branches should resolve to a child or error");
                stack.push((left_child, right_child));
            }
        }
    }

    Ok(true)
}

fn ensure_loaded_hashes(node: &SharedIntrusive<SHAMapTreeNode>) {
    if node.get_hash().is_non_zero() {
        return;
    }

    if !node.is_inner() {
        node.update_hash();
        return;
    }

    for branch in 0..BRANCH_FACTOR {
        if node.is_empty_branch(branch) {
            continue;
        }

        let Some(child) = node.get_child(branch) else {
            continue;
        };
        ensure_loaded_hashes(&child);
    }

    node.update_hash_deep();
}

fn walk_branch<F>(
    node: &SharedIntrusive<SHAMapTreeNode>,
    other_map_item: Option<SHAMapItem>,
    is_first_map: bool,
    differences: &mut Delta,
    max_count: &mut i32,
    backed: bool,
    fetch: &mut F,
) -> Result<bool, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    let mut node_stack = vec![node.clone()];
    let mut empty_branch = other_map_item.is_none();

    while let Some(node) = node_stack.pop() {
        if node.is_inner() {
            for branch in 0..BRANCH_FACTOR {
                if node.is_empty_branch(branch) {
                    continue;
                }

                let child = descend_throw(&node, branch, backed, fetch)?
                    .expect("non-empty branches should resolve to a child or error");
                node_stack.push(child);
            }
            continue;
        }

        let item = node.peek_item().expect("leaf nodes should carry an item");

        if empty_branch {
            let can_continue = if is_first_map {
                record_difference(differences, item.key(), Some(item), None, max_count)
            } else {
                record_difference(differences, item.key(), None, Some(item), max_count)
            };
            if !can_continue {
                return Ok(false);
            }
        } else {
            let other_item = other_map_item
                .as_ref()
                .expect("a non-empty comparison branch should keep its leaf");
            if item.key() != other_item.key() {
                let can_continue = if is_first_map {
                    record_difference(differences, item.key(), Some(item), None, max_count)
                } else {
                    record_difference(differences, item.key(), None, Some(item), max_count)
                };
                if !can_continue {
                    return Ok(false);
                }
            } else if item.data() != other_item.data() {
                let can_continue = if is_first_map {
                    record_difference(
                        differences,
                        item.key(),
                        Some(item),
                        Some(other_item.clone()),
                        max_count,
                    )
                } else {
                    record_difference(
                        differences,
                        item.key(),
                        Some(other_item.clone()),
                        Some(item),
                        max_count,
                    )
                };
                if !can_continue {
                    return Ok(false);
                }
                empty_branch = true;
            } else {
                empty_branch = true;
            }
        }
    }

    if !empty_branch {
        let other_item =
            other_map_item.expect("a non-empty comparison branch should keep its leaf");
        let can_continue = if is_first_map {
            record_difference(
                differences,
                other_item.key(),
                None,
                Some(other_item),
                max_count,
            )
        } else {
            record_difference(
                differences,
                other_item.key(),
                Some(other_item),
                None,
                max_count,
            )
        };
        if !can_continue {
            return Ok(false);
        }
    }

    Ok(true)
}

fn record_difference(
    differences: &mut Delta,
    key: Uint256,
    left: Option<SHAMapItem>,
    right: Option<SHAMapItem>,
    max_count: &mut i32,
) -> bool {
    differences.entry(key).or_insert((left, right));
    *max_count -= 1;
    *max_count > 0
}

pub fn deep_compare<FL, FR>(
    left_root: &SharedIntrusive<SHAMapTreeNode>,
    right_root: &SharedIntrusive<SHAMapTreeNode>,
    left_backed: bool,
    left_fetch: &mut FL,
    right_backed: bool,
    right_fetch: &mut FR,
) -> bool
where
    FL: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    FR: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    deep_compare_with_events(
        left_root,
        right_root,
        left_backed,
        left_fetch,
        right_backed,
        right_fetch,
        &mut |_| {},
    )
}

pub(crate) fn deep_compare_with_events<FL, FR, REPORT>(
    left_root: &SharedIntrusive<SHAMapTreeNode>,
    right_root: &SharedIntrusive<SHAMapTreeNode>,
    left_backed: bool,
    left_fetch: &mut FL,
    right_backed: bool,
    right_fetch: &mut FR,
    report_event: &mut REPORT,
) -> bool
where
    FL: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    FR: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    REPORT: FnMut(DeepCompareEvent),
{
    deep_compare_impl(
        left_root,
        right_root,
        left_backed,
        left_fetch,
        right_backed,
        right_fetch,
        report_event,
    )
}

fn deep_compare_impl<FL, FR, REPORT>(
    left_root: &SharedIntrusive<SHAMapTreeNode>,
    right_root: &SharedIntrusive<SHAMapTreeNode>,
    left_backed: bool,
    left_fetch: &mut FL,
    right_backed: bool,
    right_fetch: &mut FR,
    report_event: &mut REPORT,
) -> bool
where
    FL: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    FR: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    REPORT: FnMut(DeepCompareEvent),
{
    let mut stack = vec![(left_root.clone(), right_root.clone())];

    while let Some((left, right)) = stack.pop() {
        if left.get_hash() != right.get_hash() {
            report_event(DeepCompareEvent::HashMismatch);
            return false;
        }

        if left.is_leaf() {
            if !right.is_leaf() {
                return false;
            }

            let Some(left_item) = left.peek_item() else {
                return false;
            };
            let Some(right_item) = right.peek_item() else {
                return false;
            };
            if left_item != right_item {
                return false;
            }
            continue;
        }

        if !right.is_inner() {
            return false;
        }

        for branch in 0..BRANCH_FACTOR {
            if left.is_empty_branch(branch) {
                if !right.is_empty_branch(branch) {
                    return false;
                }
                continue;
            }

            if right.is_empty_branch(branch) {
                return false;
            }

            let Some(left_next) = descend(&left, branch, left_backed, left_fetch) else {
                report_event(DeepCompareEvent::UnableToFetchInnerNode);
                return false;
            };
            let Some(right_next) = descend(&right, branch, right_backed, right_fetch) else {
                report_event(DeepCompareEvent::UnableToFetchInnerNode);
                return false;
            };
            stack.push((left_next, right_next));
        }
    }

    true
}

#[allow(clippy::too_many_arguments)]
pub fn compare_with_families<CLOCKL, SL, CL, FL, MRL, NSL, CLOCKR, SR, CR, FR, MRR, NSR>(
    left_root: &SharedIntrusive<SHAMapTreeNode>,
    right_root: &SharedIntrusive<SHAMapTreeNode>,
    left_backed: bool,
    right_backed: bool,
    differences: &mut Delta,
    max_count: i32,
    left_family: &SHAMapFamily<CLOCKL, SL, CL, FL, MRL, NSL>,
    right_family: &SHAMapFamily<CLOCKR, SR, CR, FR, MRR, NSR>,
) -> Result<bool, TraversalError>
where
    CLOCKL: CacheClock,
    SL: BuildHasher + Clone,
    FL: SHAMapNodeFetcher,
    MRL: MissingNodeReporter,
    CLOCKR: CacheClock,
    SR: BuildHasher + Clone,
    FR: SHAMapNodeFetcher,
    MRR: MissingNodeReporter,
{
    compare(
        left_root,
        right_root,
        left_backed,
        &mut |hash| left_family.fetch_cached_node(hash),
        right_backed,
        &mut |hash| right_family.fetch_cached_node(hash),
        differences,
        max_count,
    )
}

pub fn deep_compare_with_families<CLOCKL, SL, CL, FL, MRL, NSL, CLOCKR, SR, CR, FR, MRR, NSR>(
    left_root: &SharedIntrusive<SHAMapTreeNode>,
    right_root: &SharedIntrusive<SHAMapTreeNode>,
    left_backed: bool,
    right_backed: bool,
    left_family: &SHAMapFamily<CLOCKL, SL, CL, FL, MRL, NSL>,
    right_family: &SHAMapFamily<CLOCKR, SR, CR, FR, MRR, NSR>,
) -> bool
where
    CLOCKL: CacheClock,
    SL: BuildHasher + Clone,
    FL: SHAMapNodeFetcher,
    MRL: MissingNodeReporter,
    CLOCKR: CacheClock,
    SR: BuildHasher + Clone,
    FR: SHAMapNodeFetcher,
    MRR: MissingNodeReporter,
{
    deep_compare_with_events(
        left_root,
        right_root,
        left_backed,
        &mut |hash| left_family.fetch_cached_node(hash),
        right_backed,
        &mut |hash| right_family.fetch_cached_node(hash),
        &mut |event| match event {
            DeepCompareEvent::HashMismatch => {
                left_family.log_warn("node hash mismatch");
            }
            DeepCompareEvent::UnableToFetchInnerNode => {
                left_family.log_warn("unable to fetch inner node");
            }
        },
    )
}

#[cfg(test)]
mod tests {
    use super::{Delta, compare, compare_with_families, deep_compare, deep_compare_with_families};
    use crate::family::{
        JournalLevel, NullFullBelowCache, NullMissingNodeReporter, SHAMapFamily, SHAMapJournal,
        SHAMapNodeFetcher,
    };
    use crate::item::SHAMapItem;
    use crate::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use crate::tree_node_cache::TreeNodeCache;
    use basics::base_uint::Uint256;
    use basics::intrusive_pointer::SharedIntrusive;
    use basics::sha_map_hash::SHAMapHash;
    use basics::tagged_cache::ManualClock;
    use parking_lot::Mutex;
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

    fn key(hex: &str) -> Uint256 {
        Uint256::from_hex(hex).expect("hex should parse")
    }

    fn sample_hash(fill: u8) -> SHAMapHash {
        SHAMapHash::new(Uint256::from_array([fill; 32]))
    }

    fn build_equal_tree() -> SharedIntrusive<SHAMapTreeNode> {
        let left_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                key("1000000000000000000000000000000000000000000000000000000000000000"),
                vec![1; 12],
            ),
            0,
        );
        let deep_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                key("4100000000000000000000000000000000000000000000000000000000000000"),
                vec![2; 12],
            ),
            0,
        );
        let right_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                key("9000000000000000000000000000000000000000000000000000000000000000"),
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
        root
    }

    fn build_empty_root() -> SharedIntrusive<SHAMapTreeNode> {
        let root = SHAMapTreeNode::new_inner(1);
        root.update_hash_deep();
        root
    }

    fn build_single_leaf_root(
        item_key: Uint256,
        payload: Vec<u8>,
    ) -> SharedIntrusive<SHAMapTreeNode> {
        SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(item_key, payload),
            0,
        )
    }

    #[test]
    fn deep_compare_returns_true_for_equal_loaded_trees() {
        let left = build_equal_tree();
        let right = build_equal_tree();

        assert!(deep_compare(
            &left,
            &right,
            false,
            &mut |_| None,
            false,
            &mut |_| None,
        ));
    }

    #[test]
    fn deep_compare_rejects_leaf_payload_mismatches() {
        let left = build_equal_tree();
        let right = build_equal_tree();
        let changed_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                key("9000000000000000000000000000000000000000000000000000000000000000"),
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
    fn deep_compare_rejects_shape_mismatches() {
        let left = build_equal_tree();
        let right = SHAMapTreeNode::new_inner(1);
        right.set_child_hash(1, left.get_child_hash(1));
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
    fn deep_compare_can_fetch_missing_children_on_both_sides() {
        let key = key("2000000000000000000000000000000000000000000000000000000000000000");
        let expected_hash = sample_hash(0xAA);
        let left_leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![4; 12]),
            0,
            expected_hash,
        );
        let right_leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![4; 12]),
            0,
            expected_hash,
        );

        let left = SHAMapTreeNode::new_inner(1);
        left.set_child_hash(2, expected_hash);
        left.update_hash_deep();

        let right = SHAMapTreeNode::new_inner(1);
        right.set_child_hash(2, expected_hash);
        right.update_hash_deep();

        let equal = deep_compare(
            &left,
            &right,
            true,
            &mut |_| Some(left_leaf.clone()),
            true,
            &mut |_| Some(right_leaf.clone()),
        );

        assert!(equal);
        assert!(left.get_child(2).is_some());
        assert!(right.get_child(2).is_some());
    }

    #[test]
    fn compare_returns_empty_delta_for_equal_trees() {
        let left = build_equal_tree();
        let right = build_equal_tree();
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
        .expect("equal compare should succeed");

        assert!(complete);
        assert!(delta.is_empty());
    }

    #[test]
    fn compare_reports_deletions_with_right_only_entries() {
        let deleted_key = key("1000000000000000000000000000000000000000000000000000000000000000");
        let left = build_empty_root();
        let right_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(deleted_key, vec![7; 12]),
            0,
        );
        let right = SHAMapTreeNode::new_inner(1);
        right.set_child_hash(1, right_leaf.get_hash());
        right.share_child(1, &right_leaf);
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
        .expect("deletion compare should succeed");

        assert!(complete);
        assert_eq!(delta.len(), 1);
        assert_eq!(
            delta.get(&deleted_key),
            Some(&(None, Some(SHAMapItem::new(deleted_key, vec![7; 12]))))
        );
    }

    #[test]
    fn compare_pairs_same_key_payload_mismatches() {
        let changed_key = key("2000000000000000000000000000000000000000000000000000000000000000");
        let left = build_single_leaf_root(changed_key, vec![1; 12]);
        let right = build_single_leaf_root(changed_key, vec![9; 12]);
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
        .expect("payload mismatch compare should succeed");

        assert!(complete);
        assert_eq!(delta.len(), 1);
        assert_eq!(
            delta.get(&changed_key),
            Some(&(
                Some(SHAMapItem::new(changed_key, vec![1; 12])),
                Some(SHAMapItem::new(changed_key, vec![9; 12])),
            ))
        );
    }

    #[test]
    fn compare_returns_false_with_partial_delta_when_max_count_is_exhausted() {
        let left = build_single_leaf_root(
            key("1000000000000000000000000000000000000000000000000000000000000000"),
            vec![1; 12],
        );
        let right = build_single_leaf_root(
            key("9000000000000000000000000000000000000000000000000000000000000000"),
            vec![2; 12],
        );
        let mut delta = Delta::new();

        let complete = compare(
            &left,
            &right,
            false,
            &mut |_| None,
            false,
            &mut |_| None,
            &mut delta,
            1,
        )
        .expect("bounded compare should succeed");

        assert!(!complete);
        assert_eq!(delta.len(), 1);
        assert_eq!(
            delta.get(&key(
                "1000000000000000000000000000000000000000000000000000000000000000"
            )),
            Some(&(
                Some(SHAMapItem::new(
                    key("1000000000000000000000000000000000000000000000000000000000000000"),
                    vec![1; 12],
                )),
                None,
            ))
        );
        assert!(!delta.contains_key(&key(
            "9000000000000000000000000000000000000000000000000000000000000000"
        )));
    }

    #[test]
    fn compare_walk_branch_pairs_matching_leaf_and_reports_other_unmatched_leaves() {
        let shared_key = key("1000000000000000000000000000000000000000000000000000000000000000");
        let extra_key = key("9000000000000000000000000000000000000000000000000000000000000000");
        let shared_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(shared_key, vec![8; 12]),
            0,
        );
        let extra_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(extra_key, vec![3; 12]),
            0,
        );
        let left = SHAMapTreeNode::new_inner(1);
        left.set_child_hash(1, shared_leaf.get_hash());
        left.share_child(1, &shared_leaf);
        left.set_child_hash(9, extra_leaf.get_hash());
        left.share_child(9, &extra_leaf);
        left.update_hash_deep();

        let right = build_single_leaf_root(shared_key, vec![1; 12]);
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
        .expect("walk-branch compare should succeed");

        assert!(complete);
        assert_eq!(
            delta.get(&shared_key),
            Some(&(
                Some(SHAMapItem::new(shared_key, vec![8; 12])),
                Some(SHAMapItem::new(shared_key, vec![1; 12])),
            ))
        );
        assert_eq!(
            delta.get(&extra_key),
            Some(&(Some(SHAMapItem::new(extra_key, vec![3; 12])), None))
        );
    }

    #[test]
    fn compare_skips_fetching_equal_child_hashes() {
        let shared_key = key("1000000000000000000000000000000000000000000000000000000000000000");
        let changed_key = key("2000000000000000000000000000000000000000000000000000000000000000");
        let shared_hash = sample_hash(0x44);
        let left_shared = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(shared_key, vec![1; 12]),
            0,
            shared_hash,
        );
        let right_shared = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(shared_key, vec![1; 12]),
            0,
            shared_hash,
        );
        let left_changed = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(changed_key, vec![2; 12]),
            0,
        );
        let right_changed = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(changed_key, vec![9; 12]),
            0,
        );

        let left = SHAMapTreeNode::new_inner(1);
        left.set_child_hash(1, shared_hash);
        left.set_child_hash(2, left_changed.get_hash());
        left.update_hash_deep();

        let right = SHAMapTreeNode::new_inner(1);
        right.set_child_hash(1, shared_hash);
        right.set_child_hash(2, right_changed.get_hash());
        right.update_hash_deep();

        let mut left_fetches = Vec::new();
        let mut right_fetches = Vec::new();
        let mut delta = Delta::new();
        let complete = compare(
            &left,
            &right,
            true,
            &mut |hash| {
                left_fetches.push(hash);
                if hash == left_changed.get_hash() {
                    Some(left_changed.clone())
                } else if hash == shared_hash {
                    Some(left_shared.clone())
                } else {
                    None
                }
            },
            true,
            &mut |hash| {
                right_fetches.push(hash);
                if hash == right_changed.get_hash() {
                    Some(right_changed.clone())
                } else if hash == shared_hash {
                    Some(right_shared.clone())
                } else {
                    None
                }
            },
            &mut delta,
            100,
        )
        .expect("backed compare should succeed");

        assert!(complete);
        assert_eq!(left_fetches, vec![left_changed.get_hash()]);
        assert_eq!(right_fetches, vec![right_changed.get_hash()]);
        assert!(left.get_child(1).is_none());
        assert!(right.get_child(1).is_none());
        assert!(left.get_child(2).is_some());
        assert!(right.get_child(2).is_some());
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
    fn compare_with_families_and_deep_compare_with_families_reuse_shared_family_fetches() {
        let key =
            Uint256::from_hex("8100000000000000000000000000000000000000000000000000000000000000")
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

        let compare_left_root = SHAMapTreeNode::new_inner(1);
        compare_left_root.set_child_hash(8, left_leaf.get_hash());
        compare_left_root.update_hash();

        let right_root = SHAMapTreeNode::new_inner(1);
        right_root.set_child_hash(8, right_leaf.get_hash());
        right_root.share_child(8, &right_leaf);
        right_root.update_hash();

        let mut compare_nodes = HashMap::new();
        compare_nodes.insert(left_leaf.get_hash(), left_leaf.clone());
        let compare_left_family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "compare-left-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            MappingFetcher {
                nodes: compare_nodes,
                fetches: Mutex::new(Vec::new()),
            },
            NullMissingNodeReporter,
        );
        let compare_right_family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "compare-right-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            MappingFetcher::default(),
            NullMissingNodeReporter,
        );

        let mut delta = Delta::new();
        let complete = compare_with_families(
            &compare_left_root,
            &right_root,
            true,
            false,
            &mut delta,
            8,
            &compare_left_family,
            &compare_right_family,
        )
        .expect("family-backed compare should succeed");

        assert!(complete);
        assert_eq!(
            compare_left_root.get_child(8).map(|node| node.get_hash()),
            Some(left_leaf.get_hash())
        );
        assert_eq!(
            delta.get(&key),
            Some(&(
                Some(SHAMapItem::new(key, vec![1; 12])),
                Some(SHAMapItem::new(key, vec![2; 12])),
            ))
        );

        let deep_left_root = SHAMapTreeNode::new_inner(1);
        deep_left_root.set_child_hash(8, left_leaf.get_hash());
        deep_left_root.update_hash();

        let equal_right_root = SHAMapTreeNode::new_inner(1);
        equal_right_root.set_child_hash(8, left_leaf.get_hash());
        equal_right_root.share_child(8, &left_leaf);
        equal_right_root.update_hash();

        let mut deep_nodes = HashMap::new();
        deep_nodes.insert(left_leaf.get_hash(), left_leaf.clone());
        let deep_left_family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "deep-left-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            MappingFetcher {
                nodes: deep_nodes,
                fetches: Mutex::new(Vec::new()),
            },
            NullMissingNodeReporter,
        );
        let deep_right_family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "deep-right-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            MappingFetcher::default(),
            NullMissingNodeReporter,
        );

        assert!(deep_compare_with_families(
            &deep_left_root,
            &equal_right_root,
            true,
            false,
            &deep_left_family,
            &deep_right_family,
        ));
        assert_eq!(
            deep_left_root.get_child(8).map(|node| node.get_hash()),
            Some(left_leaf.get_hash())
        );
    }

    #[test]
    fn deep_compare_with_families_logs_hash_mismatch_on_left_family() {
        let left_leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                key("9100000000000000000000000000000000000000000000000000000000000000"),
                vec![1; 12],
            ),
            0,
            sample_hash(0x91),
        );
        let right_leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                key("9200000000000000000000000000000000000000000000000000000000000000"),
                vec![2; 12],
            ),
            0,
            sample_hash(0x92),
        );
        let journal = Arc::new(RecordingJournal::default());
        let left_family = SHAMapFamily::new_with_journal(
            Arc::new(TreeNodeCache::new(
                "deep-compare-hash-mismatch-left",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            MappingFetcher::default(),
            NullMissingNodeReporter,
            journal.clone(),
        );
        let right_family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "deep-compare-hash-mismatch-right",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            MappingFetcher::default(),
            NullMissingNodeReporter,
        );

        assert!(!deep_compare_with_families(
            &left_leaf,
            &right_leaf,
            false,
            false,
            &left_family,
            &right_family,
        ));
        assert_eq!(
            journal.entries(),
            vec![(JournalLevel::Warn, "node hash mismatch".to_owned())]
        );
    }

    #[test]
    fn deep_compare_with_families_logs_inner_fetch_misses_on_left_family() {
        let key =
            Uint256::from_hex("9300000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse");
        let leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![3; 12]),
            0,
            sample_hash(0x93),
        );
        let left_root = SHAMapTreeNode::new_inner(1);
        left_root.set_child_hash(9, leaf.get_hash());
        left_root.update_hash();

        let right_root = SHAMapTreeNode::new_inner(1);
        right_root.set_child_hash(9, leaf.get_hash());
        right_root.share_child(9, &leaf);
        right_root.update_hash();

        let journal = Arc::new(RecordingJournal::default());
        let left_family = SHAMapFamily::new_with_journal(
            Arc::new(TreeNodeCache::new(
                "deep-compare-fetch-miss-left",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            MappingFetcher::default(),
            NullMissingNodeReporter,
            journal.clone(),
        );
        let right_family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "deep-compare-fetch-miss-right",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            MappingFetcher::default(),
            NullMissingNodeReporter,
        );

        assert!(!deep_compare_with_families(
            &left_root,
            &right_root,
            true,
            false,
            &left_family,
            &right_family,
        ));
        assert_eq!(
            journal.entries(),
            vec![(JournalLevel::Warn, "unable to fetch inner node".to_owned())]
        );
    }
}
