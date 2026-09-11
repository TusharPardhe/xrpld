//! Current `SHAMap::visitNodes` and `SHAMap::visitLeaves` helpers.

use crate::family::{MissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher};
use crate::traversal::{TraversalError, descend_no_store, descend_no_store_with_family};
use crate::tree_node::{BRANCH_FACTOR, SHAMapTreeNode};
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::CacheClock;
use std::hash::BuildHasher;

pub fn visit_nodes<F, V>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    backed: bool,
    fetch: &mut F,
    visit: &mut V,
) -> Result<(), TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    V: FnMut(&SharedIntrusive<SHAMapTreeNode>) -> bool,
{
    if !visit(root) || !root.is_inner() {
        return Ok(());
    }

    let mut stack: Vec<(usize, SharedIntrusive<SHAMapTreeNode>)> = Vec::new();
    let mut node = root.clone();
    let mut pos = 0;

    loop {
        while pos < BRANCH_FACTOR {
            if node.is_empty_branch(pos) {
                pos += 1;
                continue;
            }

            let branch = pos;
            let Some(child) = descend_no_store(&node, branch, backed, fetch) else {
                return Err(TraversalError::MissingNode(node.get_child_hash(branch)));
            };

            if !visit(&child) {
                return Ok(());
            }

            if child.is_leaf() {
                pos += 1;
                continue;
            }

            while (pos != BRANCH_FACTOR - 1) && node.is_empty_branch(pos + 1) {
                pos += 1;
            }

            if pos != BRANCH_FACTOR - 1 {
                stack.push((pos + 1, node));
            }

            node = child;
            pos = 0;
        }

        let Some((resume_pos, resume_node)) = stack.pop() else {
            break;
        };
        pos = resume_pos;
        node = resume_node;
    }

    Ok(())
}

pub fn visit_nodes_with_family<CLOCK, S, FB, F, MR, NS, V>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
    visit: &mut V,
) -> Result<(), TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
    V: FnMut(&SharedIntrusive<SHAMapTreeNode>) -> bool,
{
    if !visit(root) || !root.is_inner() {
        return Ok(());
    }

    let mut stack: Vec<(usize, SharedIntrusive<SHAMapTreeNode>)> = Vec::new();
    let mut node = root.clone();
    let mut pos = 0;

    loop {
        while pos < BRANCH_FACTOR {
            if node.is_empty_branch(pos) {
                pos += 1;
                continue;
            }

            let branch = pos;
            let Some(child) =
                descend_no_store_with_family(&node, branch, backed, ledger_seq, family)
            else {
                return Err(TraversalError::MissingNode(node.get_child_hash(branch)));
            };

            if !visit(&child) {
                return Ok(());
            }

            if child.is_leaf() {
                pos += 1;
                continue;
            }

            while (pos != BRANCH_FACTOR - 1) && node.is_empty_branch(pos + 1) {
                pos += 1;
            }

            if pos != BRANCH_FACTOR - 1 {
                stack.push((pos + 1, node));
            }

            node = child;
            pos = 0;
        }

        let Some((resume_pos, resume_node)) = stack.pop() else {
            break;
        };
        pos = resume_pos;
        node = resume_node;
    }

    Ok(())
}

pub fn visit_leaves<F, V>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    backed: bool,
    fetch: &mut F,
    visit: &mut V,
) -> Result<(), TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    V: FnMut(&crate::item::SHAMapItem),
{
    visit_nodes(root, backed, fetch, &mut |node| {
        if node.is_leaf() {
            let item = node.peek_item().expect("leaf nodes should carry an item");
            visit(&item);
        }
        true
    })
}

pub fn visit_leaves_with_family<CLOCK, S, FB, F, MR, NS, V>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
    visit: &mut V,
) -> Result<(), TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
    V: FnMut(&crate::item::SHAMapItem),
{
    visit_nodes_with_family(root, backed, ledger_seq, family, &mut |node| {
        if node.is_leaf() {
            let item = node.peek_item().expect("leaf nodes should carry an item");
            visit(&item);
        }
        true
    })
}

#[cfg(test)]
mod tests {
    use super::{visit_leaves, visit_leaves_with_family, visit_nodes, visit_nodes_with_family};
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

    fn key(hex: &str) -> Uint256 {
        Uint256::from_hex(hex).expect("hex should parse")
    }

    fn same_node(
        left: &SharedIntrusive<SHAMapTreeNode>,
        right: &SharedIntrusive<SHAMapTreeNode>,
    ) -> bool {
        std::ptr::eq(&**left, &**right)
    }

    fn sample_hash(fill: u8) -> SHAMapHash {
        SHAMapHash::new(Uint256::from_array([fill; 32]))
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

    fn build_nested_tree() -> (
        SharedIntrusive<SHAMapTreeNode>,
        SharedIntrusive<SHAMapTreeNode>,
        SharedIntrusive<SHAMapTreeNode>,
        SharedIntrusive<SHAMapTreeNode>,
    ) {
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

        (root, left_leaf, middle_inner, right_leaf)
    }

    #[test]
    fn visit_nodes_walks_current_preorder_shape() {
        let (root, left_leaf, middle_inner, right_leaf) = build_nested_tree();
        let mut visited = Vec::new();

        visit_nodes(&root, false, &mut |_| None, &mut |node| {
            visited.push(node.clone());
            true
        })
        .expect("loaded visit should succeed");

        assert_eq!(visited.len(), 5);
        assert!(same_node(&visited[0], &root));
        assert!(same_node(&visited[1], &left_leaf));
        assert!(same_node(&visited[2], &middle_inner));
        assert_eq!(
            visited[3]
                .peek_item()
                .expect("deep leaf should carry an item")
                .key(),
            key("4100000000000000000000000000000000000000000000000000000000000000")
        );
        assert!(same_node(&visited[4], &right_leaf));
    }

    #[test]
    fn visit_nodes_stops_when_callback_returns_false() {
        let (root, ..) = build_nested_tree();
        let mut count = 0;

        visit_nodes(&root, false, &mut |_| None, &mut |_| {
            count += 1;
            count < 3
        })
        .expect("early-stop visit should succeed");

        assert_eq!(count, 3);
    }

    #[test]
    fn visit_leaves_reports_leaf_items_in_branch_order() {
        let (root, ..) = build_nested_tree();
        let mut visited = Vec::new();

        visit_leaves(&root, false, &mut |_| None, &mut |item| {
            visited.push(item.key());
        })
        .expect("leaf visit should succeed");

        assert_eq!(
            visited,
            vec![
                key("1000000000000000000000000000000000000000000000000000000000000000"),
                key("4100000000000000000000000000000000000000000000000000000000000000"),
                key("9000000000000000000000000000000000000000000000000000000000000000"),
            ]
        );
    }

    #[test]
    fn visit_nodes_fetches_without_attaching_children() {
        let fetched_leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                key("2000000000000000000000000000000000000000000000000000000000000000"),
                vec![4; 12],
            ),
            0,
            sample_hash(0xCC),
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(2, sample_hash(0xCC));

        let mut visited = Vec::new();
        visit_nodes(
            &root,
            true,
            &mut |_| Some(fetched_leaf.clone()),
            &mut |node| {
                visited.push(node.clone());
                true
            },
        )
        .expect("backed visit should succeed");

        assert_eq!(visited.len(), 2);
        assert!(same_node(&visited[1], &fetched_leaf));
        assert!(root.get_child(2).is_none());
    }

    #[test]
    fn family_backed_visits_report_missing_fetches_by_ledger_seq() {
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

        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(2, sample_hash(0xCD));

        let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "visitor-family",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            SharedReporter(reporter.clone()),
        );

        let node_error = visit_nodes_with_family(&root, true, 900, &family, &mut |_| true)
            .expect_err("missing non-empty branch should still report an error");
        assert_eq!(
            node_error,
            crate::traversal::TraversalError::MissingNode(sample_hash(0xCD))
        );

        let leaf_error = visit_leaves_with_family(&root, true, 901, &family, &mut |_| {})
            .expect_err("leaf-only visit should report the same missing branch");
        assert_eq!(
            leaf_error,
            crate::traversal::TraversalError::MissingNode(sample_hash(0xCD))
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
                (900, *sample_hash(0xCD).as_uint256()),
                (901, *sample_hash(0xCD).as_uint256()),
            ]
        );
    }
}
