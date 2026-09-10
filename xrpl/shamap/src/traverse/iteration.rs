//! Current `SHAMap` ordered leaf walk helpers.

use crate::family::{MissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher};
use crate::node_id::{SHAMapNodeId, select_branch};
use crate::search::{
    NodePathEntry, walk_towards_key_with_path, walk_towards_key_with_path_and_family,
};
use crate::traversal::{TraversalError, descend_throw, descend_throw_with_family};
use crate::tree_node::{BRANCH_FACTOR, SHAMapTreeNode};
use basics::base_uint::Uint256;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::CacheClock;
use std::hash::BuildHasher;

pub fn peek_first_item<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    stack: &mut Vec<NodePathEntry>,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    stack.clear();
    let leaf = first_below(root, SHAMapNodeId::default(), stack, backed, fetch)?;
    if leaf.is_none() {
        stack.clear();
    }
    Ok(leaf)
}

pub fn peek_first_item_with_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    stack: &mut Vec<NodePathEntry>,
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
    stack.clear();
    let leaf = first_below_with_family(
        root,
        SHAMapNodeId::default(),
        stack,
        backed,
        ledger_seq,
        family,
    )?;
    if leaf.is_none() {
        stack.clear();
    }
    Ok(leaf)
}

pub fn peek_next_item<F>(
    id: Uint256,
    stack: &mut Vec<NodePathEntry>,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    assert!(
        !stack.is_empty(),
        "peek_next_item requires a non-empty stack from peek_first_item"
    );
    assert!(
        stack
            .last()
            .expect("stack was checked as non-empty")
            .node
            .is_leaf(),
        "peek_next_item expects the stack to end with a leaf"
    );

    stack.pop();
    while let Some(entry) = stack.last().cloned() {
        assert!(
            entry.node.is_inner(),
            "non-leaf stack entries must be inner"
        );
        let start_branch = select_branch(entry.node_id, id) + 1;
        for branch in start_branch..BRANCH_FACTOR {
            if entry.node.is_empty_branch(branch) {
                continue;
            }

            let child = descend_throw(&entry.node, branch, backed, fetch)?
                .expect("non-empty branches should resolve to a child or error");
            let child_id = entry
                .node_id
                .get_child_node_id(branch)
                .expect("branch selection must stay within SHAMap depth bounds");
            return first_below(&child, child_id, stack, backed, fetch);
        }
        stack.pop();
    }

    Ok(None)
}

pub fn peek_next_item_with_family<CLOCK, S, FB, F, MR, NS>(
    id: Uint256,
    stack: &mut Vec<NodePathEntry>,
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
    assert!(
        !stack.is_empty(),
        "peek_next_item requires a non-empty stack from peek_first_item"
    );
    assert!(
        stack
            .last()
            .expect("stack was checked as non-empty")
            .node
            .is_leaf(),
        "peek_next_item expects the stack to end with a leaf"
    );

    stack.pop();
    while let Some(entry) = stack.last().cloned() {
        assert!(
            entry.node.is_inner(),
            "non-leaf stack entries must be inner"
        );
        let start_branch = select_branch(entry.node_id, id) + 1;
        for branch in start_branch..BRANCH_FACTOR {
            if entry.node.is_empty_branch(branch) {
                continue;
            }

            let child = descend_throw_with_family(&entry.node, branch, backed, ledger_seq, family)?
                .expect("non-empty branches should resolve to a child or error");
            let child_id = entry
                .node_id
                .get_child_node_id(branch)
                .expect("branch selection must stay within SHAMap depth bounds");
            return first_below_with_family(&child, child_id, stack, backed, ledger_seq, family);
        }
        stack.pop();
    }

    Ok(None)
}

pub fn upper_bound<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    let (_, mut stack) = walk_towards_key_with_path(root, id, backed, fetch)?;
    while let Some(entry) = stack.last().cloned() {
        if entry.node.is_leaf() {
            if entry.node.peek_item().is_some_and(|item| item.key() > id) {
                return Ok(Some(entry.node));
            }
        } else {
            let start_branch = select_branch(entry.node_id, id) + 1;
            for branch in start_branch..BRANCH_FACTOR {
                if entry.node.is_empty_branch(branch) {
                    continue;
                }

                let child = descend_throw(&entry.node, branch, backed, fetch)?
                    .expect("non-empty branches should resolve to a child or error");
                let child_id = entry
                    .node_id
                    .get_child_node_id(branch)
                    .expect("branch selection must stay within SHAMap depth bounds");
                let mut below_stack = Vec::new();
                return first_below(&child, child_id, &mut below_stack, backed, fetch);
            }
        }
        stack.pop();
    }

    Ok(None)
}

pub fn upper_bound_with_family<CLOCK, S, FB, F, MR, NS>(
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
    let (_, mut stack) =
        walk_towards_key_with_path_and_family(root, id, backed, ledger_seq, family)?;
    while let Some(entry) = stack.last().cloned() {
        if entry.node.is_leaf() {
            if entry.node.peek_item().is_some_and(|item| item.key() > id) {
                return Ok(Some(entry.node));
            }
        } else {
            let start_branch = select_branch(entry.node_id, id) + 1;
            for branch in start_branch..BRANCH_FACTOR {
                if entry.node.is_empty_branch(branch) {
                    continue;
                }

                let child =
                    descend_throw_with_family(&entry.node, branch, backed, ledger_seq, family)?
                        .expect("non-empty branches should resolve to a child or error");
                let child_id = entry
                    .node_id
                    .get_child_node_id(branch)
                    .expect("branch selection must stay within SHAMap depth bounds");
                let mut below_stack = Vec::new();
                return first_below_with_family(
                    &child,
                    child_id,
                    &mut below_stack,
                    backed,
                    ledger_seq,
                    family,
                );
            }
        }
        stack.pop();
    }

    Ok(None)
}

/// Collect up to `limit` leaves whose keys are strictly greater than `start`,
/// returned in ascending key order.
///
/// ## Algorithm
///
/// 1. **Seek** — `walk_towards_key_with_path` descends from `root` toward
///    `start`, recording every node visited (root → … → closest leaf or dead
///    end) into a `Vec<NodePathEntry>` walk stack.
///
/// 2. **Upper-bound** — the same logic as [`upper_bound`] is applied to that
///    stack to reach the first leaf `> start`.  The critical difference from
///    [`upper_bound`] is that the **stack is kept live**: when `first_below`
///    is called it receives the shared stack, so by the time it returns the
///    stack ends with that first leaf — exactly the invariant expected by
///    `peek_next_item`.
///
/// 3. **Collect** — `peek_next_item` is called repeatedly to advance forward
///    through the tree in O(1) amortised time per step, accumulating nodes
///    until `limit` is reached or the tree is exhausted.
///
/// ## Errors
///
/// Returns [`TraversalError::MissingNode`] if a hash-addressed child is
/// referenced but cannot be resolved (only possible when `backed = true`).
pub fn iterate_from<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    start: Uint256,
    limit: usize,
    backed: bool,
    fetch: &mut F,
) -> Result<Vec<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    if limit == 0 {
        return Ok(Vec::new());
    }
    iterate_from_inner(root, start, limit, backed, fetch)
}

// Two-phase implementation: upper-bound seek (stack-preserving), then
// limit-capped forward collection via peek_next_item.
fn iterate_from_inner<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    start: Uint256,
    limit: usize,
    backed: bool,
    fetch: &mut F,
) -> Result<Vec<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    // ── Step 1: Walk toward `start`, collecting the path from root. ──────────
    let (_, mut stack) = walk_towards_key_with_path(root, start, backed, fetch)?;

    // ── Step 2: Upper-bound seek ─────────────────────────────────────────────
    //
    // We find the first leaf strictly > start using the same traversal logic
    // as `upper_bound`, but critically we pass `&mut stack` to `first_below`
    // so the stack remains valid for `peek_next_item` afterwards.
    //
    // The tricky case is the inner-node branch: once we find a child branch
    // to descend, we call `first_below` with our stack. After that call the
    // stack ends with the first leaf under that subtree, and we are done
    // seeking. We use an `Option` sentinel (`seek_done`) to break out of the
    // manual "while let" loop without needing a labelled break-with-value.
    enum SeekResult {
        Found(SharedIntrusive<SHAMapTreeNode>),
        Exhausted,
    }

    let seek_result: SeekResult = {
        let mut result = SeekResult::Exhausted;
        'seek: loop {
            let Some(entry) = stack.last().cloned() else {
                break 'seek;
            };

            if entry.node.is_leaf() {
                if entry
                    .node
                    .peek_item()
                    .is_some_and(|item| item.key() > start)
                {
                    // Stack already ends with this leaf.
                    result = SeekResult::Found(entry.node);
                    break 'seek;
                }
                stack.pop();
            } else {
                let start_branch = select_branch(entry.node_id, start) + 1;
                let mut descended = false;
                for branch in start_branch..BRANCH_FACTOR {
                    if entry.node.is_empty_branch(branch) {
                        continue;
                    }

                    let child = descend_throw(&entry.node, branch, backed, fetch)?
                        .expect("non-empty branches should resolve to a child or error");
                    let child_id = entry
                        .node_id
                        .get_child_node_id(branch)
                        .expect("branch selection must stay within SHAMap depth bounds");

                    // Descend into the first leaf under this subtree.
                    // `first_below` appends to `stack`, leaving it with the leaf on top.
                    if let Some(leaf) = first_below(&child, child_id, &mut stack, backed, fetch)? {
                        result = SeekResult::Found(leaf);
                        break 'seek;
                    }
                    descended = true;
                    break;
                }
                if !descended {
                    stack.pop();
                }
            }
        }
        result
    };

    // ── Step 3: Collect up to `limit` leaves via peek_next_item ─────────────
    let first_leaf = match seek_result {
        SeekResult::Exhausted => return Ok(Vec::new()),
        SeekResult::Found(leaf) => leaf,
    };

    let mut results = Vec::with_capacity(limit);
    results.push(first_leaf.clone());

    // The key of the leaf currently on top of the stack, used by peek_next_item
    // to figure out which sibling branch to advance past.
    let mut current_key = first_leaf
        .peek_item()
        .expect("a leaf node must always carry an item")
        .key();

    while results.len() < limit {
        match peek_next_item(current_key, &mut stack, backed, fetch)? {
            None => break,
            Some(leaf) => {
                current_key = leaf
                    .peek_item()
                    .expect("a leaf node must always carry an item")
                    .key();
                results.push(leaf);
            }
        }
    }

    Ok(results)
}

pub fn lower_bound<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    id: Uint256,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    let (_, mut stack) = walk_towards_key_with_path(root, id, backed, fetch)?;
    while let Some(entry) = stack.last().cloned() {
        if entry.node.is_leaf() {
            if entry.node.peek_item().is_some_and(|item| item.key() < id) {
                return Ok(Some(entry.node));
            }
        } else {
            let start_branch = select_branch(entry.node_id, id);
            for branch in (0..start_branch).rev() {
                if entry.node.is_empty_branch(branch) {
                    continue;
                }

                let child = descend_throw(&entry.node, branch, backed, fetch)?
                    .expect("non-empty branches should resolve to a child or error");
                let child_id = entry
                    .node_id
                    .get_child_node_id(branch)
                    .expect("branch selection must stay within SHAMap depth bounds");
                let mut below_stack = Vec::new();
                return last_below(&child, child_id, &mut below_stack, backed, fetch);
            }
        }
        stack.pop();
    }

    Ok(None)
}

pub fn lower_bound_with_family<CLOCK, S, FB, F, MR, NS>(
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
    let (_, mut stack) =
        walk_towards_key_with_path_and_family(root, id, backed, ledger_seq, family)?;
    while let Some(entry) = stack.last().cloned() {
        if entry.node.is_leaf() {
            if entry.node.peek_item().is_some_and(|item| item.key() < id) {
                return Ok(Some(entry.node));
            }
        } else {
            let start_branch = select_branch(entry.node_id, id);
            for branch in (0..start_branch).rev() {
                if entry.node.is_empty_branch(branch) {
                    continue;
                }

                let child =
                    descend_throw_with_family(&entry.node, branch, backed, ledger_seq, family)?
                        .expect("non-empty branches should resolve to a child or error");
                let child_id = entry
                    .node_id
                    .get_child_node_id(branch)
                    .expect("branch selection must stay within SHAMap depth bounds");
                let mut below_stack = Vec::new();
                return last_below_with_family(
                    &child,
                    child_id,
                    &mut below_stack,
                    backed,
                    ledger_seq,
                    family,
                );
            }
        }
        stack.pop();
    }

    Ok(None)
}

fn first_below<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    root_id: SHAMapNodeId,
    stack: &mut Vec<NodePathEntry>,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    extreme_below(root, root_id, stack, backed, fetch, true)
}

fn first_below_with_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    root_id: SHAMapNodeId,
    stack: &mut Vec<NodePathEntry>,
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
    extreme_below_with_family(root, root_id, stack, backed, ledger_seq, family, true)
}

fn last_below<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    root_id: SHAMapNodeId,
    stack: &mut Vec<NodePathEntry>,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    extreme_below(root, root_id, stack, backed, fetch, false)
}

fn last_below_with_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    root_id: SHAMapNodeId,
    stack: &mut Vec<NodePathEntry>,
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
    extreme_below_with_family(root, root_id, stack, backed, ledger_seq, family, false)
}

fn extreme_below<F>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    root_id: SHAMapNodeId,
    stack: &mut Vec<NodePathEntry>,
    backed: bool,
    fetch: &mut F,
    forward: bool,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    let mut node = root.clone();
    let mut node_id = root_id;

    loop {
        stack.push(NodePathEntry {
            node: node.clone(),
            node_id,
        });

        if node.is_leaf() {
            return Ok(Some(node));
        }

        let next = if forward {
            next_child_in_order(&node, node_id, backed, fetch)?
        } else {
            previous_child_in_order(&node, node_id, backed, fetch)?
        };
        let Some((child, child_id)) = next else {
            return Ok(None);
        };
        node = child;
        node_id = child_id;
    }
}

fn extreme_below_with_family<CLOCK, S, FB, F, MR, NS>(
    root: &SharedIntrusive<SHAMapTreeNode>,
    root_id: SHAMapNodeId,
    stack: &mut Vec<NodePathEntry>,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
    forward: bool,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    let mut node = root.clone();
    let mut node_id = root_id;

    loop {
        stack.push(NodePathEntry {
            node: node.clone(),
            node_id,
        });

        if node.is_leaf() {
            return Ok(Some(node));
        }

        let next = if forward {
            next_child_in_order_with_family(&node, node_id, backed, ledger_seq, family)?
        } else {
            previous_child_in_order_with_family(&node, node_id, backed, ledger_seq, family)?
        };
        let Some((child, child_id)) = next else {
            return Ok(None);
        };
        node = child;
        node_id = child_id;
    }
}

fn next_child_in_order<F>(
    node: &SharedIntrusive<SHAMapTreeNode>,
    node_id: SHAMapNodeId,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<(SharedIntrusive<SHAMapTreeNode>, SHAMapNodeId)>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    for branch in 0..BRANCH_FACTOR {
        if node.is_empty_branch(branch) {
            continue;
        }

        let child = descend_throw(node, branch, backed, fetch)?
            .expect("non-empty branches should resolve to a child or error");
        let child_id = node_id
            .get_child_node_id(branch)
            .expect("branch selection must stay within SHAMap depth bounds");
        return Ok(Some((child, child_id)));
    }

    Ok(None)
}

fn next_child_in_order_with_family<CLOCK, S, FB, F, MR, NS>(
    node: &SharedIntrusive<SHAMapTreeNode>,
    node_id: SHAMapNodeId,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<Option<(SharedIntrusive<SHAMapTreeNode>, SHAMapNodeId)>, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    for branch in 0..BRANCH_FACTOR {
        if node.is_empty_branch(branch) {
            continue;
        }

        let child = descend_throw_with_family(node, branch, backed, ledger_seq, family)?
            .expect("non-empty branches should resolve to a child or error");
        let child_id = node_id
            .get_child_node_id(branch)
            .expect("branch selection must stay within SHAMap depth bounds");
        return Ok(Some((child, child_id)));
    }

    Ok(None)
}

fn previous_child_in_order<F>(
    node: &SharedIntrusive<SHAMapTreeNode>,
    node_id: SHAMapNodeId,
    backed: bool,
    fetch: &mut F,
) -> Result<Option<(SharedIntrusive<SHAMapTreeNode>, SHAMapNodeId)>, TraversalError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    for branch in (0..BRANCH_FACTOR).rev() {
        if node.is_empty_branch(branch) {
            continue;
        }

        let child = descend_throw(node, branch, backed, fetch)?
            .expect("non-empty branches should resolve to a child or error");
        let child_id = node_id
            .get_child_node_id(branch)
            .expect("branch selection must stay within SHAMap depth bounds");
        return Ok(Some((child, child_id)));
    }

    Ok(None)
}

fn previous_child_in_order_with_family<CLOCK, S, FB, F, MR, NS>(
    node: &SharedIntrusive<SHAMapTreeNode>,
    node_id: SHAMapNodeId,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<Option<(SharedIntrusive<SHAMapTreeNode>, SHAMapNodeId)>, TraversalError>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    for branch in (0..BRANCH_FACTOR).rev() {
        if node.is_empty_branch(branch) {
            continue;
        }

        let child = descend_throw_with_family(node, branch, backed, ledger_seq, family)?
            .expect("non-empty branches should resolve to a child or error");
        let child_id = node_id
            .get_child_node_id(branch)
            .expect("branch selection must stay within SHAMap depth bounds");
        return Ok(Some((child, child_id)));
    }

    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::{iterate_from, lower_bound, peek_first_item, peek_next_item, upper_bound};
    use crate::item::SHAMapItem;
    use crate::search::NodePathEntry;
    use crate::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use basics::base_uint::Uint256;
    use basics::intrusive_pointer::SharedIntrusive;
    use basics::sha_map_hash::SHAMapHash;

    fn key(hex: &str) -> Uint256 {
        Uint256::from_hex(hex).expect("hex should parse")
    }

    fn sample_hash(fill: u8) -> SHAMapHash {
        SHAMapHash::new(Uint256::from_array([fill; 32]))
    }

    fn same_node(
        left: &SharedIntrusive<SHAMapTreeNode>,
        right: &SharedIntrusive<SHAMapTreeNode>,
    ) -> bool {
        std::ptr::eq(&**left, &**right)
    }

    type ThreeLeafRoot = (
        SharedIntrusive<SHAMapTreeNode>,
        SharedIntrusive<SHAMapTreeNode>,
        SharedIntrusive<SHAMapTreeNode>,
        SharedIntrusive<SHAMapTreeNode>,
        Uint256,
        Uint256,
        Uint256,
    );

    fn build_three_leaf_root() -> ThreeLeafRoot {
        let low_key = key("1000000000000000000000000000000000000000000000000000000000000000");
        let mid_key = key("4000000000000000000000000000000000000000000000000000000000000000");
        let high_key = key("9000000000000000000000000000000000000000000000000000000000000000");

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

        (
            root, low_leaf, mid_leaf, high_leaf, low_key, mid_key, high_key,
        )
    }

    #[test]
    fn peek_first_and_next_item_walk_loaded_leaves_in_order() {
        let (root, low_leaf, mid_leaf, high_leaf, low_key, mid_key, _) = build_three_leaf_root();
        let mut stack: Vec<NodePathEntry> = Vec::new();

        let first = peek_first_item(&root, &mut stack, false, &mut |_| None)
            .expect("first loaded leaf lookup should succeed")
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

        let end = peek_next_item(
            third
                .peek_item()
                .expect("third leaf should have an item")
                .key(),
            &mut stack,
            false,
            &mut |_| None,
        )
        .expect("iteration end should not error");
        assert!(end.is_none());
    }

    #[test]
    fn upper_and_lower_bound_match_current_cpp_roles() {
        let (root, _low_leaf, mid_leaf, high_leaf, low_key, _mid_key, high_key) =
            build_three_leaf_root();
        let between_mid_and_high =
            key("7000000000000000000000000000000000000000000000000000000000000000");

        let upper = upper_bound(&root, between_mid_and_high, false, &mut |_| None)
            .expect("upper bound should succeed")
            .expect("higher leaf should exist");
        assert!(same_node(&upper, &high_leaf));

        let lower = lower_bound(&root, between_mid_and_high, false, &mut |_| None)
            .expect("lower bound should succeed")
            .expect("lower leaf should exist");
        assert!(same_node(&lower, &mid_leaf));

        let exact_upper = upper_bound(&root, low_key, false, &mut |_| None)
            .expect("exact upper bound should succeed")
            .expect("next leaf should exist");
        assert!(same_node(&exact_upper, &mid_leaf));

        let exact_lower = lower_bound(&root, high_key, false, &mut |_| None)
            .expect("exact lower bound should succeed")
            .expect("previous leaf should exist");
        assert!(same_node(&exact_lower, &mid_leaf));

        let no_lower = lower_bound(&root, low_key, false, &mut |_| None)
            .expect("empty predecessor search should succeed");
        assert!(no_lower.is_none());
    }

    #[test]
    fn peek_first_item_fetches_missing_children_when_backed() {
        let key = key("2000000000000000000000000000000000000000000000000000000000000000");
        let leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![9; 12]),
            0,
            sample_hash(0xAB),
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child_hash(2, sample_hash(0xAB));

        let mut stack = Vec::new();
        let mut fetch_calls = 0;
        let first = peek_first_item(&root, &mut stack, true, &mut |_| {
            fetch_calls += 1;
            Some(leaf.clone())
        })
        .expect("backed first lookup should succeed")
        .expect("fetched first leaf should exist");

        assert!(same_node(&first, &leaf));
        assert_eq!(fetch_calls, 1);
        assert!(root.get_child(2).is_some());
    }

    // ── iterate_from tests ────────────────────────────────────────────────────

    #[test]
    fn iterate_from_returns_all_leaves_after_key_below_all() {
        // start key is below all leaves → should return all three in order
        let (root, low_leaf, mid_leaf, high_leaf, _, _, _) = build_three_leaf_root();
        let below_all = key("0000000000000000000000000000000000000000000000000000000000000001");

        let results = iterate_from(&root, below_all, 10, false, &mut |_| None)
            .expect("iterate_from below all leaves should succeed");

        assert_eq!(results.len(), 3);
        assert!(same_node(&results[0], &low_leaf));
        assert!(same_node(&results[1], &mid_leaf));
        assert!(same_node(&results[2], &high_leaf));
    }

    #[test]
    fn iterate_from_respects_limit() {
        let (root, low_leaf, mid_leaf, _, _, _, _) = build_three_leaf_root();
        let below_all = key("0000000000000000000000000000000000000000000000000000000000000001");

        let results = iterate_from(&root, below_all, 2, false, &mut |_| None)
            .expect("iterate_from with limit 2 should succeed");

        assert_eq!(results.len(), 2);
        assert!(same_node(&results[0], &low_leaf));
        assert!(same_node(&results[1], &mid_leaf));
    }

    #[test]
    fn iterate_from_skips_exact_start_key() {
        // start == low_key: low_leaf must NOT be included (strictly greater)
        let (root, _low_leaf, mid_leaf, high_leaf, low_key, _, _) = build_three_leaf_root();

        let results = iterate_from(&root, low_key, 10, false, &mut |_| None)
            .expect("iterate_from from exact low_key should succeed");

        assert_eq!(results.len(), 2);
        assert!(same_node(&results[0], &mid_leaf));
        assert!(same_node(&results[1], &high_leaf));
    }

    #[test]
    fn iterate_from_between_keys_finds_upper_bound_first() {
        // start between mid_key and high_key → only high_leaf is returned
        let (root, _, _, high_leaf, _, _, _) = build_three_leaf_root();
        let between_mid_and_high =
            key("7000000000000000000000000000000000000000000000000000000000000000");

        let results = iterate_from(&root, between_mid_and_high, 10, false, &mut |_| None)
            .expect("iterate_from between mid and high should succeed");

        assert_eq!(results.len(), 1);
        assert!(same_node(&results[0], &high_leaf));
    }

    #[test]
    fn iterate_from_at_or_past_last_key_returns_empty() {
        let (root, _, _, _, _, _, high_key) = build_three_leaf_root();

        // start == high_key (exact last): nothing strictly greater
        let at_last = iterate_from(&root, high_key, 10, false, &mut |_| None)
            .expect("iterate_from at last key should succeed");
        assert!(at_last.is_empty(), "no leaves are strictly > high_key");

        // start past everything
        let beyond_all = key("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
        let past_all = iterate_from(&root, beyond_all, 10, false, &mut |_| None)
            .expect("iterate_from past all leaves should succeed");
        assert!(past_all.is_empty(), "no leaves exist past max key");
    }

    #[test]
    fn iterate_from_limit_zero_returns_empty_without_traversal() {
        let (root, _, _, _, _, _, _) = build_three_leaf_root();
        let below_all = key("0000000000000000000000000000000000000000000000000000000000000001");

        let results = iterate_from(&root, below_all, 0, false, &mut |_| None)
            .expect("iterate_from with limit 0 should succeed");
        assert!(results.is_empty(), "limit=0 must return an empty vec");
    }

    #[test]
    fn iterate_from_limit_one_returns_single_leaf() {
        let (root, low_leaf, _, _, _, _, _) = build_three_leaf_root();
        let below_all = key("0000000000000000000000000000000000000000000000000000000000000001");

        let results = iterate_from(&root, below_all, 1, false, &mut |_| None)
            .expect("iterate_from with limit 1 should succeed");
        assert_eq!(results.len(), 1);
        assert!(same_node(&results[0], &low_leaf));
    }
}
