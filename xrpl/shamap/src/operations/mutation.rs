//! Current `SHAMap::addGiveItem` and `SHAMap::updateGiveItem` mutation roles.

use crate::item::SHAMapItem;
use crate::node_id::{SHAMapNodeId, select_branch};
use crate::search::{NodePathEntry, find_key, walk_towards_key_with_path};
use crate::traversal::TraversalError;
use crate::tree_node::{BRANCH_FACTOR, SHAMapNodeType, SHAMapTreeNode};
use basics::base_uint::Uint256;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;

type WriteNodeCallback<'a> =
    dyn FnMut(SharedIntrusive<SHAMapTreeNode>) -> SharedIntrusive<SHAMapTreeNode> + 'a;
type TryWriteNodeCallback<'a, E> =
    dyn FnMut(SharedIntrusive<SHAMapTreeNode>) -> Result<SharedIntrusive<SHAMapTreeNode>, E> + 'a;

#[derive(Debug, Clone)]
pub struct MutableTree {
    root: SharedIntrusive<SHAMapTreeNode>,
    cowid: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MutationError {
    Traversal(TraversalError),
    RootMustBeInner,
    InnerNodeMustBeOwned(SHAMapNodeId),
    LeafNodeMustBeOwned(SHAMapNodeId),
    DuplicateExactLeaf(Uint256),
    MissingExactLeaf(Uint256),
    CrossTypeChange {
        requested: SHAMapNodeType,
        existing: SHAMapNodeType,
    },
}

impl From<TraversalError> for MutationError {
    fn from(error: TraversalError) -> Self {
        Self::Traversal(error)
    }
}

impl MutableTree {
    pub fn new(cowid: u32) -> Self {
        assert!(cowid != 0, "mutable trees require a non-zero cowid");
        Self {
            root: SHAMapTreeNode::new_inner(cowid),
            cowid,
        }
    }

    pub fn from_loaded_root(root: SharedIntrusive<SHAMapTreeNode>, cowid: u32) -> Self {
        assert!(cowid != 0, "mutable trees require a non-zero cowid");
        assert!(
            root.cowid() <= cowid,
            "loaded roots must not belong to a newer owner than the mutable tree"
        );
        Self { root, cowid }
    }

    pub fn root(&self) -> SharedIntrusive<SHAMapTreeNode> {
        self.root.clone()
    }

    pub fn cowid(&self) -> u32 {
        self.cowid
    }

    pub fn mutable_snapshot(&self, next_cowid: u32) -> Self {
        assert!(
            next_cowid > self.cowid,
            "mutable snapshots must advance cowid"
        );
        Self {
            root: clone_loaded_subtree_as_shareable(&self.root, next_cowid),
            cowid: next_cowid,
        }
    }

    pub fn share_loaded_subtree(&mut self) -> usize {
        self.unshare()
    }

    pub fn unshare(&mut self) -> usize {
        let (root, count) = walk_subtree_impl(self.root.clone(), self.cowid, None);
        self.root = root;
        count
    }

    pub fn flush_dirty<F>(&mut self, writer: &mut F) -> usize
    where
        F: FnMut(SharedIntrusive<SHAMapTreeNode>) -> SharedIntrusive<SHAMapTreeNode>,
    {
        let mut writer: &mut WriteNodeCallback<'_> = writer;
        let (root, count) = walk_subtree_impl(self.root.clone(), self.cowid, Some(&mut writer));
        self.root = root;
        count
    }

    pub fn try_flush_dirty<F, E>(&mut self, writer: &mut F) -> Result<usize, E>
    where
        F: FnMut(SharedIntrusive<SHAMapTreeNode>) -> Result<SharedIntrusive<SHAMapTreeNode>, E>,
    {
        let mut writer: &mut TryWriteNodeCallback<'_, E> = writer;
        let (root, count) =
            try_walk_subtree_impl(self.root.clone(), self.cowid, Some(&mut writer))?;
        self.root = root;
        Ok(count)
    }

    /// Build a flushed, shareable view of only this tree's dirty paths while
    /// leaving the original dirty ownership untouched. Clean subtrees remain
    /// shared. This supports checked persistence: callers can serialize a
    /// complete postorder batch, commit it, and only then flush/canonicalize
    /// the original tree.
    pub fn try_flush_dirty_detached<F, E>(&self, writer: &mut F) -> Result<(Self, usize), E>
    where
        F: FnMut(SharedIntrusive<SHAMapTreeNode>) -> Result<SharedIntrusive<SHAMapTreeNode>, E>,
    {
        let mut writer: &mut TryWriteNodeCallback<'_, E> = writer;
        let (root, count) =
            try_walk_subtree_detached_impl(self.root.clone(), self.cowid, Some(&mut writer))?;
        Ok((
            Self {
                root,
                cowid: self.cowid,
            },
            count,
        ))
    }

    pub fn walk_subtree<F>(&mut self, writer: Option<&mut F>) -> usize
    where
        F: FnMut(SharedIntrusive<SHAMapTreeNode>) -> SharedIntrusive<SHAMapTreeNode>,
    {
        let writer = writer.map(|writer| writer as &mut WriteNodeCallback<'_>);
        let (root, count) = walk_subtree_impl(self.root.clone(), self.cowid, writer);
        self.root = root;
        count
    }

    pub fn find_key(
        &self,
        key: Uint256,
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError> {
        find_key(&self.root, key, false, &mut |_| None)
    }

    pub fn add_item(
        &mut self,
        node_type: SHAMapNodeType,
        item: SHAMapItem,
    ) -> Result<bool, MutationError> {
        assert_ne!(
            node_type,
            SHAMapNodeType::Inner,
            "inner nodes are not valid SHAMap add targets"
        );

        let target = item.key();
        let (terminal, path) = walk_towards_key_with_path(&self.root, target, false, &mut |_| None)
            .map_err(MutationError::from)?;

        match terminal {
            None => self.add_into_empty_branch(&path, target, node_type, item),
            Some(leaf) => self.add_with_leaf_split(&path, &leaf, node_type, item),
        }
    }

    pub fn add_give_item(
        &mut self,
        item: SHAMapItem,
        node_type: SHAMapNodeType,
    ) -> Result<bool, MutationError> {
        self.add_item(node_type, item)
    }

    pub fn update_item(
        &mut self,
        node_type: SHAMapNodeType,
        item: SHAMapItem,
    ) -> Result<bool, MutationError> {
        assert_ne!(
            node_type,
            SHAMapNodeType::Inner,
            "inner nodes are not valid SHAMap update targets"
        );

        let target = item.key();
        let (leaf, path) = walk_towards_key_with_path(&self.root, target, false, &mut |_| None)
            .map_err(MutationError::from)?;
        let Some(leaf) = leaf else {
            return Err(MutationError::MissingExactLeaf(target));
        };
        let Some(leaf_entry) = path.last() else {
            return Err(MutationError::MissingExactLeaf(target));
        };
        let Some(existing_item) = leaf.peek_item() else {
            return Err(MutationError::MissingExactLeaf(target));
        };
        if existing_item.key() != target {
            return Err(MutationError::MissingExactLeaf(target));
        }

        let existing_type = leaf.get_type();
        if existing_type != node_type {
            return Err(MutationError::CrossTypeChange {
                requested: node_type,
                existing: existing_type,
            });
        }

        let leaf = self.unshare_node(leaf, leaf_entry.node_id)?;
        if leaf.set_item(item) {
            self.root = self.dirty_up(&path[..path.len() - 1], target, leaf)?;
        }

        Ok(true)
    }

    pub fn update_give_item(
        &mut self,
        item: SHAMapItem,
        node_type: SHAMapNodeType,
    ) -> Result<bool, MutationError> {
        self.update_item(node_type, item)
    }

    pub fn has_item(&self, key: Uint256) -> bool {
        self.find_key(key).map(|opt| opt.is_some()).unwrap_or(false)
    }

    pub fn delete_item(&mut self, target: Uint256) -> Result<bool, MutationError> {
        let (leaf, path) = walk_towards_key_with_path(&self.root, target, false, &mut |_| None)
            .map_err(MutationError::from)?;
        let Some(leaf) = leaf else {
            return Ok(false);
        };
        let Some(existing_item) = leaf.peek_item() else {
            return Ok(false);
        };
        if existing_item.key() != target {
            return Ok(false);
        }

        let mut prev_node = None;
        for entry in path[..path.len() - 1].iter().rev() {
            let node = self.unshare_node(entry.node.clone(), entry.node_id)?;
            let branch = select_branch(entry.node_id, target);
            node.set_child(branch, prev_node.take());

            if entry.node_id.is_root() {
                self.root = node;
                continue;
            }

            match node.branch_count() {
                0 => {}
                1 => {
                    let Some(sole_leaf) = only_below_loaded_leaf(&node)? else {
                        prev_node = Some(node);
                        continue;
                    };

                    let sole_branch = select_only_branch(&node)
                        .expect("single-branch inner nodes must expose one branch index");
                    let sole_item = sole_leaf
                        .peek_item()
                        .expect("collapsed sole leaf should carry an item");
                    let sole_type = sole_leaf.get_type();
                    node.set_child(sole_branch, None);
                    prev_node = Some(SHAMapTreeNode::new_leaf(sole_type, sole_item, self.cowid));
                }
                _ => {
                    prev_node = Some(node);
                }
            }
        }

        Ok(true)
    }

    /// Like add_item but uses a fetch callback for tree traversal.
    pub fn add_item_with_fetch<F>(
        &mut self,
        node_type: SHAMapNodeType,
        item: SHAMapItem,
        fetch: &mut F,
    ) -> Result<bool, MutationError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        assert_ne!(node_type, SHAMapNodeType::Inner);
        let target = item.key();
        let (terminal, path) = walk_towards_key_with_path(&self.root, target, true, fetch)
            .map_err(MutationError::from)?;
        match terminal {
            None => self.add_into_empty_branch(&path, target, node_type, item),
            Some(leaf) => self.add_with_leaf_split(&path, &leaf, node_type, item),
        }
    }

    /// Like update_item but uses a fetch callback for tree traversal.
    pub fn update_item_with_fetch<F>(
        &mut self,
        node_type: SHAMapNodeType,
        item: SHAMapItem,
        fetch: &mut F,
    ) -> Result<bool, MutationError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        assert_ne!(node_type, SHAMapNodeType::Inner);
        let target = item.key();
        let (leaf, path) = walk_towards_key_with_path(&self.root, target, true, fetch)
            .map_err(MutationError::from)?;
        let Some(leaf) = leaf else {
            return Err(MutationError::MissingExactLeaf(target));
        };
        let Some(leaf_entry) = path.last() else {
            return Err(MutationError::MissingExactLeaf(target));
        };
        let Some(existing_item) = leaf.peek_item() else {
            return Err(MutationError::MissingExactLeaf(target));
        };
        if existing_item.key() != target {
            return Err(MutationError::MissingExactLeaf(target));
        }
        let existing_type = leaf.get_type();
        if existing_type != node_type {
            return Err(MutationError::CrossTypeChange {
                requested: node_type,
                existing: existing_type,
            });
        }
        let leaf = self.unshare_node(leaf, leaf_entry.node_id)?;
        if leaf.set_item(item) {
            self.root = self.dirty_up(&path[..path.len() - 1], target, leaf)?;
        }
        Ok(true)
    }

    /// Like delete_item but uses a fetch callback for tree traversal.
    pub fn delete_item_with_fetch<F>(
        &mut self,
        target: Uint256,
        fetch: &mut F,
    ) -> Result<bool, MutationError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        let (leaf, path) = walk_towards_key_with_path(&self.root, target, true, fetch)
            .map_err(MutationError::from)?;
        let Some(leaf) = leaf else {
            return Ok(false);
        };
        let Some(existing_item) = leaf.peek_item() else {
            return Ok(false);
        };
        if existing_item.key() != target {
            return Ok(false);
        }

        let mut prev_node = None;
        for entry in path[..path.len() - 1].iter().rev() {
            let node = self.unshare_node(entry.node.clone(), entry.node_id)?;
            let branch = select_branch(entry.node_id, target);
            node.set_child(branch, prev_node.take());

            if entry.node_id.is_root() {
                // reference: root is the end of the chain, no updateHashDeep
                self.root = node;
                continue;
            }

            match node.branch_count() {
                0 => {
                    // no children below this branch
                }
                1 => {
                    let Some(sole_leaf) = only_below_leaf_with_fetch(&node, fetch)? else {
                        prev_node = Some(node);
                        continue;
                    };
                    let sole_item = sole_leaf.peek_item().expect("leaf must have item");
                    let sole_type = sole_leaf.get_type();
                    prev_node = Some(SHAMapTreeNode::new_leaf(sole_type, sole_item, self.cowid));
                }
                _ => {
                    // reference: prevNode = std::move(node) — no updateHashDeep
                    prev_node = Some(node);
                }
            }
        }

        Ok(true)
    }

    fn add_into_empty_branch(
        &mut self,
        path: &[NodePathEntry],
        target: Uint256,
        node_type: SHAMapNodeType,
        item: SHAMapItem,
    ) -> Result<bool, MutationError> {
        let Some(parent_entry) = path.last() else {
            return Err(MutationError::RootMustBeInner);
        };
        let branch = select_branch(parent_entry.node_id, target);
        let parent = self.unshare_node(parent_entry.node.clone(), parent_entry.node_id)?;
        debug_assert!(parent.is_inner());
        debug_assert!(parent.is_empty_branch(branch));

        let leaf = SHAMapTreeNode::new_leaf(node_type, item, self.cowid);
        parent.set_child(branch, Some(leaf));
        self.root = self.dirty_up(&path[..path.len() - 1], target, parent)?;
        Ok(true)
    }

    fn add_with_leaf_split(
        &mut self,
        path: &[NodePathEntry],
        leaf: &SharedIntrusive<SHAMapTreeNode>,
        node_type: SHAMapNodeType,
        item: SHAMapItem,
    ) -> Result<bool, MutationError> {
        let target = item.key();
        let Some(leaf_entry) = path.last() else {
            return Err(MutationError::RootMustBeInner);
        };
        let Some(existing_item) = leaf.peek_item() else {
            return Err(MutationError::MissingExactLeaf(target));
        };
        if existing_item.key() == target {
            return Ok(false);
        }

        let existing_type = leaf.get_type();
        if existing_type != node_type {
            return Err(MutationError::CrossTypeChange {
                requested: node_type,
                existing: existing_type,
            });
        }

        let mut graft_stack = path[..path.len() - 1].to_vec();
        let mut node_id = leaf_entry.node_id;
        let mut split_node = SHAMapTreeNode::new_inner(self.cowid);

        loop {
            let new_branch = select_branch(node_id, target);
            let old_branch = select_branch(node_id, existing_item.key());
            if new_branch != old_branch {
                split_node.set_child(
                    new_branch,
                    Some(SHAMapTreeNode::new_leaf(node_type, item, self.cowid)),
                );
                split_node.set_child(
                    old_branch,
                    Some(SHAMapTreeNode::new_leaf(
                        node_type,
                        existing_item,
                        self.cowid,
                    )),
                );
                self.root = self.dirty_up(&graft_stack, target, split_node)?;
                return Ok(true);
            }

            graft_stack.push(NodePathEntry {
                node: split_node.clone(),
                node_id,
            });
            node_id = node_id
                .get_child_node_id(new_branch)
                .expect("split branches must remain within SHAMap depth bounds");
            split_node = SHAMapTreeNode::new_inner(self.cowid);
        }
    }

    fn dirty_up(
        &mut self,
        path: &[NodePathEntry],
        target: Uint256,
        mut child: SharedIntrusive<SHAMapTreeNode>,
    ) -> Result<SharedIntrusive<SHAMapTreeNode>, MutationError> {
        // It just sets children and leaves hashes dirty (zero).
        // Hashes are recomputed lazily when needed (getHash/flushDirty).
        for entry in path.iter().rev() {
            let branch = select_branch(entry.node_id, target);
            let node = self.unshare_node(entry.node.clone(), entry.node_id)?;
            node.set_child(branch, Some(child));
            child = node;
        }
        Ok(child)
    }

    fn unshare_node(
        &mut self,
        node: SharedIntrusive<SHAMapTreeNode>,
        node_id: SHAMapNodeId,
    ) -> Result<SharedIntrusive<SHAMapTreeNode>, MutationError> {
        assert!(node.cowid() <= self.cowid, "node valid for cowid");
        if node.cowid() == self.cowid {
            return Ok(node);
        }

        let cloned = node.clone_with_cowid(self.cowid);
        if node_id.is_root() {
            self.root = cloned.clone();
        }
        Ok(cloned)
    }
}

pub fn add_item(
    root: &SharedIntrusive<SHAMapTreeNode>,
    node_type: SHAMapNodeType,
    item: SHAMapItem,
) -> Result<bool, MutationError> {
    assert_ne!(
        node_type,
        SHAMapNodeType::Inner,
        "inner nodes are not valid SHAMap add targets"
    );
    if !root.is_inner() {
        return Err(MutationError::RootMustBeInner);
    }

    let owner = require_owned_inner(root, SHAMapNodeId::default())?;
    let target = item.key();
    let (terminal, path) = walk_towards_key_with_path(root, target, false, &mut |_| None)
        .map_err(MutationError::from)?;

    match terminal {
        None => add_into_empty_branch(&path, target, node_type, item, owner),
        Some(leaf) => add_with_leaf_split(&path, &leaf, node_type, item, owner),
    }
}

pub fn update_item(
    root: &SharedIntrusive<SHAMapTreeNode>,
    node_type: SHAMapNodeType,
    item: SHAMapItem,
) -> Result<bool, MutationError> {
    assert_ne!(
        node_type,
        SHAMapNodeType::Inner,
        "inner nodes are not valid SHAMap update targets"
    );
    if !root.is_inner() {
        return Err(MutationError::RootMustBeInner);
    }

    let target = item.key();
    let (leaf, path) = walk_towards_key_with_path(root, target, false, &mut |_| None)
        .map_err(MutationError::from)?;
    let Some(leaf) = leaf else {
        return Err(MutationError::MissingExactLeaf(target));
    };
    let Some(leaf_entry) = path.last() else {
        return Err(MutationError::MissingExactLeaf(target));
    };
    let Some(existing_item) = leaf.peek_item() else {
        return Err(MutationError::MissingExactLeaf(target));
    };
    if existing_item.key() != target {
        return Err(MutationError::MissingExactLeaf(target));
    }

    let existing_type = leaf.get_type();
    if existing_type != node_type {
        return Err(MutationError::CrossTypeChange {
            requested: node_type,
            existing: existing_type,
        });
    }

    require_owned_leaf(&leaf, leaf_entry.node_id)?;
    if leaf.set_item(item) {
        dirty_up(&path[..path.len() - 1], target, leaf);
    }

    Ok(true)
}

pub fn delete_item(
    root: &SharedIntrusive<SHAMapTreeNode>,
    target: Uint256,
) -> Result<bool, MutationError> {
    if !root.is_inner() {
        return Err(MutationError::RootMustBeInner);
    }

    require_owned_inner(root, SHAMapNodeId::default())?;
    let (leaf, path) = walk_towards_key_with_path(root, target, false, &mut |_| None)
        .map_err(MutationError::from)?;
    let Some(leaf) = leaf else {
        return Ok(false);
    };
    let Some(existing_item) = leaf.peek_item() else {
        return Ok(false);
    };
    if existing_item.key() != target {
        return Ok(false);
    }

    let mut prev_node = None;
    for entry in path[..path.len() - 1].iter().rev() {
        require_owned_inner(&entry.node, entry.node_id)?;
        let branch = select_branch(entry.node_id, target);
        entry.node.set_child(branch, prev_node.take());

        if entry.node_id.is_root() {
            continue;
        }

        match entry.node.branch_count() {
            0 => {}
            1 => {
                let Some(sole_leaf) = only_below_loaded_leaf(&entry.node)? else {
                    prev_node = Some(entry.node.clone());
                    continue;
                };

                let sole_branch = select_only_branch(&entry.node)
                    .expect("single-branch inner nodes must expose one branch index");
                let sole_item = sole_leaf
                    .peek_item()
                    .expect("collapsed sole leaf should carry an item");
                let sole_type = sole_leaf.get_type();
                entry.node.set_child(sole_branch, None);
                prev_node = Some(SHAMapTreeNode::new_leaf(
                    sole_type,
                    sole_item,
                    entry.node.cowid(),
                ));
            }
            _ => {
                prev_node = Some(entry.node.clone());
            }
        }
    }

    Ok(true)
}

fn add_into_empty_branch(
    path: &[NodePathEntry],
    target: Uint256,
    node_type: SHAMapNodeType,
    item: SHAMapItem,
    owner: u32,
) -> Result<bool, MutationError> {
    let Some(parent_entry) = path.last() else {
        return Err(MutationError::RootMustBeInner);
    };
    let branch = select_branch(parent_entry.node_id, target);
    require_owned_inner(&parent_entry.node, parent_entry.node_id)?;
    debug_assert!(parent_entry.node.is_inner());
    debug_assert!(parent_entry.node.is_empty_branch(branch));

    let leaf = SHAMapTreeNode::new_leaf(node_type, item, owner);
    parent_entry.node.set_child(branch, Some(leaf));
    parent_entry.node.update_hash_deep();
    dirty_up(&path[..path.len() - 1], target, parent_entry.node.clone());
    Ok(true)
}

fn add_with_leaf_split(
    path: &[NodePathEntry],
    leaf: &SharedIntrusive<SHAMapTreeNode>,
    node_type: SHAMapNodeType,
    item: SHAMapItem,
    owner: u32,
) -> Result<bool, MutationError> {
    let target = item.key();
    let Some(leaf_entry) = path.last() else {
        return Err(MutationError::RootMustBeInner);
    };
    let Some(existing_item) = leaf.peek_item() else {
        return Err(MutationError::MissingExactLeaf(target));
    };
    if existing_item.key() == target {
        return Ok(false);
    }

    let existing_type = leaf.get_type();
    if existing_type != node_type {
        return Err(MutationError::CrossTypeChange {
            requested: node_type,
            existing: existing_type,
        });
    }

    let mut graft_stack = path[..path.len() - 1].to_vec();
    let mut node_id = leaf_entry.node_id;
    let mut split_node = SHAMapTreeNode::new_inner(owner);

    loop {
        let new_branch = select_branch(node_id, target);
        let old_branch = select_branch(node_id, existing_item.key());
        if new_branch != old_branch {
            split_node.set_child(
                new_branch,
                Some(SHAMapTreeNode::new_leaf(node_type, item, owner)),
            );
            split_node.set_child(
                old_branch,
                Some(SHAMapTreeNode::new_leaf(node_type, existing_item, owner)),
            );
            dirty_up(&graft_stack, target, split_node);
            return Ok(true);
        }

        graft_stack.push(NodePathEntry {
            node: split_node.clone(),
            node_id,
        });
        node_id = node_id
            .get_child_node_id(new_branch)
            .expect("split branches must remain within SHAMap depth bounds");
        split_node = SHAMapTreeNode::new_inner(owner);
    }
}

fn dirty_up(path: &[NodePathEntry], target: Uint256, mut child: SharedIntrusive<SHAMapTreeNode>) {
    // It just sets children and leaves hashes dirty (zero).
    for entry in path.iter().rev() {
        let branch = select_branch(entry.node_id, target);
        entry.node.set_child(branch, Some(child));
        child = entry.node.clone();
    }
}

fn only_below_loaded_leaf(
    node: &SharedIntrusive<SHAMapTreeNode>,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, MutationError> {
    let mut node = node.clone();
    while node.is_inner() {
        let mut next = None;
        for branch in 0..BRANCH_FACTOR {
            if node.is_empty_branch(branch) {
                continue;
            }

            let Some(child) = node.get_child(branch) else {
                return Ok(None);
            };
            if next.is_some() {
                return Ok(None);
            }
            next = Some(child);
        }

        let Some(child) = next else {
            return Ok(None);
        };
        node = child;
    }

    Ok(Some(node))
}

/// Resolve the sole descendant of a backed single-branch subtree.
///
/// rippled's `SHAMap::onlyBelow` descends through hash-only children while
/// deciding whether a one-branch inner node can collapse to a leaf. Leaving
/// such a subtree uncollapsed preserves its logical items but changes the
/// SHAMap root, which is consensus-visible.
fn only_below_leaf_with_fetch<F>(
    node: &SharedIntrusive<SHAMapTreeNode>,
    fetch: &mut F,
) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, MutationError>
where
    F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
{
    let mut node = node.clone();
    while node.is_inner() {
        let Some(branch) = select_only_branch(&node) else {
            return Ok(None);
        };
        if node.branch_count() != 1 {
            return Ok(None);
        }

        if let Some(child) = node.get_child(branch) {
            node = child;
            continue;
        }

        let hash = node.get_child_hash(branch);
        let Some(child) = fetch(hash) else {
            return Err(MutationError::Traversal(TraversalError::MissingNode(hash)));
        };
        node = child;
    }

    Ok(Some(node))
}

fn select_only_branch(node: &SharedIntrusive<SHAMapTreeNode>) -> Option<usize> {
    (0..BRANCH_FACTOR).find(|&branch| !node.is_empty_branch(branch))
}

fn clone_loaded_subtree_as_shareable(
    node: &SharedIntrusive<SHAMapTreeNode>,
    cowid: u32,
) -> SharedIntrusive<SHAMapTreeNode> {
    let cloned = node.clone_with_cowid(cowid);

    if cloned.is_inner() {
        for branch in 0..BRANCH_FACTOR {
            if cloned.is_empty_branch(branch) {
                continue;
            }

            let Some(child) = node.get_child(branch) else {
                continue;
            };
            let cloned_child = clone_loaded_subtree_as_shareable(&child, cowid);
            cloned.set_child(branch, Some(cloned_child));
        }
        cloned.update_hash_deep();
    } else {
        cloned.update_hash();
    }

    cloned.unshare();
    cloned
}

fn pre_flush_node(
    node: SharedIntrusive<SHAMapTreeNode>,
    owner_cowid: u32,
) -> SharedIntrusive<SHAMapTreeNode> {
    if node.cowid() == owner_cowid {
        node
    } else {
        node.clone_with_cowid(owner_cowid)
    }
}

fn maybe_write_node(
    node: SharedIntrusive<SHAMapTreeNode>,
    writer: &mut Option<&mut WriteNodeCallback<'_>>,
) -> SharedIntrusive<SHAMapTreeNode> {
    if let Some(write) = writer.as_deref_mut() {
        write(node)
    } else {
        node
    }
}

fn try_maybe_write_node<E>(
    node: SharedIntrusive<SHAMapTreeNode>,
    writer: &mut Option<&mut TryWriteNodeCallback<'_, E>>,
) -> Result<SharedIntrusive<SHAMapTreeNode>, E> {
    if let Some(write) = writer.as_deref_mut() {
        write(node)
    } else {
        Ok(node)
    }
}

fn walk_subtree_impl(
    mut root: SharedIntrusive<SHAMapTreeNode>,
    owner_cowid: u32,
    mut writer: Option<&mut WriteNodeCallback<'_>>,
) -> (SharedIntrusive<SHAMapTreeNode>, usize) {
    debug_assert_ne!(
        owner_cowid, 0,
        "walk_subtree requires a non-zero owner cowid"
    );

    let mut flushed = 0;
    if root.cowid() == 0 {
        return (root, flushed);
    }

    if root.is_leaf() {
        root = pre_flush_node(root, owner_cowid);
        root.update_hash();
        root.unshare();
        root = maybe_write_node(root, &mut writer);
        return (root, 1);
    }

    if root.is_inner() && root.is_empty() {
        return (SHAMapTreeNode::new_inner(0), 1);
    }

    let mut node = pre_flush_node(root, owner_cowid);
    let mut stack = Vec::new();
    let mut pos = 0;

    loop {
        while pos < BRANCH_FACTOR {
            if node.is_empty_branch(pos) {
                pos += 1;
                continue;
            }

            let branch = pos;
            pos += 1;
            let Some(mut child) = node.get_child(branch) else {
                continue;
            };
            if child.cowid() == 0 {
                continue;
            }

            child = pre_flush_node(child, owner_cowid);
            if child.is_inner() {
                stack.push((node, branch));
                node = child;
                pos = 0;
                continue;
            }

            flushed += 1;
            child.update_hash();
            child.unshare();
            child = maybe_write_node(child, &mut writer);
            node.share_child(branch, &child);
        }

        node.update_hash_deep();
        node.unshare();
        node = maybe_write_node(node, &mut writer);
        flushed += 1;

        let Some((parent, branch)) = stack.pop() else {
            break;
        };
        parent.share_child(branch, &node);
        node = parent;
        pos = branch + 1;
    }

    (node, flushed)
}

fn try_walk_subtree_impl<E>(
    mut root: SharedIntrusive<SHAMapTreeNode>,
    owner_cowid: u32,
    mut writer: Option<&mut TryWriteNodeCallback<'_, E>>,
) -> Result<(SharedIntrusive<SHAMapTreeNode>, usize), E> {
    debug_assert_ne!(
        owner_cowid, 0,
        "walk_subtree requires a non-zero owner cowid"
    );

    let mut flushed = 0;
    if root.cowid() == 0 {
        return Ok((root, flushed));
    }

    if root.is_leaf() {
        root = pre_flush_node(root, owner_cowid);
        root.update_hash();
        root.unshare();
        root = try_maybe_write_node(root, &mut writer)?;
        return Ok((root, 1));
    }

    if root.is_inner() && root.is_empty() {
        return Ok((SHAMapTreeNode::new_inner(0), 1));
    }

    let mut node = pre_flush_node(root, owner_cowid);
    let mut stack = Vec::new();
    let mut pos = 0;

    loop {
        while pos < BRANCH_FACTOR {
            if node.is_empty_branch(pos) {
                pos += 1;
                continue;
            }

            let branch = pos;
            pos += 1;
            let Some(mut child) = node.get_child(branch) else {
                continue;
            };
            if child.cowid() == 0 {
                continue;
            }

            child = pre_flush_node(child, owner_cowid);
            if child.is_inner() {
                stack.push((node, branch));
                node = child;
                pos = 0;
                continue;
            }

            flushed += 1;
            child.update_hash();
            child.unshare();
            child = try_maybe_write_node(child, &mut writer)?;
            node.share_child(branch, &child);
        }

        node.update_hash_deep();
        node.unshare();
        node = try_maybe_write_node(node, &mut writer)?;
        flushed += 1;

        let Some((parent, branch)) = stack.pop() else {
            break;
        };
        parent.share_child(branch, &node);
        node = parent;
        pos = branch + 1;
    }

    Ok((node, flushed))
}

fn try_walk_subtree_detached_impl<E>(
    root: SharedIntrusive<SHAMapTreeNode>,
    owner_cowid: u32,
    mut writer: Option<&mut TryWriteNodeCallback<'_, E>>,
) -> Result<(SharedIntrusive<SHAMapTreeNode>, usize), E> {
    debug_assert_ne!(owner_cowid, 0);
    if root.cowid() == 0 {
        return Ok((root, 0));
    }

    let mut root = root.clone_with_cowid(owner_cowid);
    if root.is_leaf() {
        root.update_hash();
        root.unshare();
        root = try_maybe_write_node(root, &mut writer)?;
        return Ok((root, 1));
    }
    if root.is_inner() && root.is_empty() {
        return Ok((SHAMapTreeNode::new_inner(0), 1));
    }

    let mut flushed = 0;
    let mut node = root;
    let mut stack = Vec::new();
    let mut pos = 0;
    loop {
        while pos < BRANCH_FACTOR {
            if node.is_empty_branch(pos) {
                pos += 1;
                continue;
            }
            let branch = pos;
            pos += 1;
            let Some(child) = node.get_child(branch) else {
                continue;
            };
            if child.cowid() == 0 {
                continue;
            }
            let mut child = child.clone_with_cowid(owner_cowid);
            if child.is_inner() {
                stack.push((node, branch));
                node = child;
                pos = 0;
                continue;
            }
            flushed += 1;
            child.update_hash();
            child.unshare();
            child = try_maybe_write_node(child, &mut writer)?;
            node.share_child(branch, &child);
        }

        node.update_hash_deep();
        node.unshare();
        node = try_maybe_write_node(node, &mut writer)?;
        flushed += 1;
        let Some((parent, branch)) = stack.pop() else {
            break;
        };
        parent.share_child(branch, &node);
        node = parent;
        pos = branch + 1;
    }
    Ok((node, flushed))
}

fn require_owned_inner(
    node: &SharedIntrusive<SHAMapTreeNode>,
    node_id: SHAMapNodeId,
) -> Result<u32, MutationError> {
    let owner = node.cowid();
    if owner == 0 {
        return Err(MutationError::InnerNodeMustBeOwned(node_id));
    }
    Ok(owner)
}

fn require_owned_leaf(
    node: &SharedIntrusive<SHAMapTreeNode>,
    node_id: SHAMapNodeId,
) -> Result<u32, MutationError> {
    let owner = node.cowid();
    if owner == 0 {
        return Err(MutationError::LeafNodeMustBeOwned(node_id));
    }
    Ok(owner)
}

#[cfg(test)]
mod tests {
    use super::{MutableTree, MutationError, add_item, delete_item, update_item};
    use crate::item::SHAMapItem;
    use crate::search::find_key;
    use crate::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use basics::base_uint::Uint256;
    use basics::intrusive_pointer::SharedIntrusive;

    fn same_node(
        left: &SharedIntrusive<SHAMapTreeNode>,
        right: &SharedIntrusive<SHAMapTreeNode>,
    ) -> bool {
        std::ptr::eq(&**left, &**right)
    }

    #[test]
    fn add_item_attaches_a_new_leaf_to_an_empty_branch() {
        let key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let root = SHAMapTreeNode::new_inner(1);

        let inserted = add_item(
            &root,
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![1; 12]),
        )
        .expect("insert into empty branch should succeed");

        assert!(inserted);
        let found = find_key(&root, key, false, &mut |_| None)
            .expect("lookup should succeed")
            .expect("inserted key should resolve");
        assert_eq!(found.get_type(), SHAMapNodeType::AccountState);
        assert!(root.get_hash().is_non_zero());
    }

    #[test]
    fn add_item_splits_a_leaf_when_keys_diverge_below_the_current_path() {
        let existing_key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let inserted_key =
            Uint256::from_hex("1234A67890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let existing_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(existing_key, vec![2; 12]),
            1,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child(1, Some(existing_leaf.clone()));
        root.update_hash_deep();

        let inserted = add_item(
            &root,
            SHAMapNodeType::AccountState,
            SHAMapItem::new(inserted_key, vec![3; 12]),
        )
        .expect("split insert should succeed");

        assert!(inserted);
        let branch = root
            .get_child(1)
            .expect("shared prefix branch should exist");
        assert!(branch.is_inner());
        let found_existing = find_key(&root, existing_key, false, &mut |_| None)
            .expect("existing lookup should succeed")
            .expect("existing key should still resolve");
        let found_inserted = find_key(&root, inserted_key, false, &mut |_| None)
            .expect("inserted lookup should succeed")
            .expect("inserted key should resolve");
        assert!(!same_node(&found_existing, &existing_leaf));
        assert_eq!(
            found_existing
                .peek_item()
                .expect("existing leaf should carry an item")
                .key(),
            existing_key
        );
        assert_eq!(
            found_inserted
                .peek_item()
                .expect("inserted leaf should carry an item")
                .key(),
            inserted_key
        );
    }

    #[test]
    fn add_into_empty_branch_keeps_ancestors_dirty_when_a_sibling_split_is_dirty() {
        let first =
            Uint256::from_hex("1000000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse");
        let colliding =
            Uint256::from_hex("1100000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse");
        let unrelated =
            Uint256::from_hex("2000000000000000000000000000000000000000000000000000000000000000")
                .expect("hex should parse");
        let mut tree = MutableTree::new(1);

        for key in [first, colliding, unrelated] {
            assert!(
                tree.add_item(
                    SHAMapNodeType::AccountState,
                    SHAMapItem::new(key, vec![0xA5; 12]),
                )
                .expect("insert should succeed")
            );
        }

        assert!(
            tree.root().get_hash().is_zero(),
            "an ancestor cannot be considered hashed while its split child remains dirty"
        );
        tree.unshare();
        assert!(tree.root().get_hash().is_non_zero());
    }

    #[test]
    fn add_item_returns_false_for_duplicate_keys() {
        let key = Uint256::from_array([0x11; 32]);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![4; 12]),
            1,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child(1, Some(leaf));
        root.update_hash_deep();

        let inserted = add_item(
            &root,
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![9; 12]),
        )
        .expect("duplicate insert should not error");

        assert!(!inserted);
    }

    #[test]
    fn add_item_splits_a_loaded_leaf_root_into_a_new_inner_root() {
        let existing_key = Uint256::from_array([0x10; 32]);
        let inserted_key = Uint256::from_array([0x90; 32]);
        let existing_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(existing_key, vec![4; 12]),
            1,
        );
        let mut tree = MutableTree::from_loaded_root(existing_leaf.clone(), 1);

        let inserted = tree
            .add_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(inserted_key, vec![9; 12]),
            )
            .expect("leaf-root split insert should succeed");

        assert!(inserted);
        let root = tree.root();
        assert!(root.is_inner());
        assert!(
            find_key(&root, existing_key, false, &mut |_| None)
                .expect("existing lookup should succeed")
                .is_some()
        );
        assert!(
            find_key(&root, inserted_key, false, &mut |_| None)
                .expect("inserted lookup should succeed")
                .is_some()
        );
        assert!(root.get_child(1).is_some());
        assert!(root.get_child(9).is_some());
        assert_ne!(root.get_hash(), existing_leaf.get_hash());
    }

    #[test]
    fn update_item_recomputes_leaf_and_parent_hashes() {
        let key = Uint256::from_array([0x22; 32]);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![5; 12]),
            1,
        );
        let root = SHAMapTreeNode::new_inner(2);
        root.set_child(2, Some(leaf.clone()));
        root.update_hash_deep();

        let old_leaf_hash = leaf.get_hash();
        let old_root_hash = root.get_hash();
        let updated = update_item(
            &root,
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![6; 12]),
        )
        .expect("owned update should succeed");

        assert!(updated);
        assert_ne!(leaf.get_hash(), old_leaf_hash);
        assert_ne!(root.get_hash(), old_root_hash);
    }

    #[test]
    fn update_item_rejects_cross_type_changes() {
        let key = Uint256::from_array([0x33; 32]);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![7; 12]),
            1,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child(3, Some(leaf));
        root.update_hash_deep();

        let error = update_item(
            &root,
            SHAMapNodeType::TransactionMd,
            SHAMapItem::new(key, vec![8; 12]),
        )
        .expect_err("cross-type update should be rejected");

        assert_eq!(
            error,
            MutationError::CrossTypeChange {
                requested: SHAMapNodeType::TransactionMd,
                existing: SHAMapNodeType::AccountState,
            }
        );
    }

    #[test]
    fn delete_item_returns_false_when_the_exact_key_is_missing() {
        let stored_key = Uint256::from_array([0x41; 32]);
        let requested_key = Uint256::from_array([0x4F; 32]);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(stored_key, vec![9; 12]),
            1,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child(4, Some(leaf));
        root.update_hash_deep();

        let deleted = delete_item(&root, requested_key).expect("missing delete should not error");
        assert!(!deleted);
    }

    #[test]
    fn delete_item_removes_the_last_root_child_without_collapsing_root() {
        let key = Uint256::from_array([0x51; 32]);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![10; 12]),
            1,
        );
        let root = SHAMapTreeNode::new_inner(1);
        root.set_child(5, Some(leaf));
        root.update_hash_deep();

        let deleted = delete_item(&root, key).expect("root delete should succeed");
        assert!(deleted);
        assert!(
            find_key(&root, key, false, &mut |_| None)
                .expect("lookup should succeed")
                .is_none()
        );
        assert!(root.is_inner());
        assert!(root.is_empty());
        assert!(root.get_hash().is_zero());
    }

    #[test]
    fn delete_item_collapses_non_root_single_item_subtrees() {
        let keep_key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let delete_key =
            Uint256::from_hex("1234A67890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let root = SHAMapTreeNode::new_inner(1);
        add_item(
            &root,
            SHAMapNodeType::AccountState,
            SHAMapItem::new(keep_key, vec![11; 12]),
        )
        .expect("first insert should succeed");
        add_item(
            &root,
            SHAMapNodeType::AccountState,
            SHAMapItem::new(delete_key, vec![12; 12]),
        )
        .expect("second insert should succeed");

        let deleted = delete_item(&root, delete_key).expect("delete should succeed");
        assert!(deleted);

        let branch = root
            .get_child(1)
            .expect("surviving root branch should remain");
        assert!(branch.is_leaf());
        let found = find_key(&root, keep_key, false, &mut |_| None)
            .expect("lookup should succeed")
            .expect("surviving key should resolve");
        assert_eq!(
            found.peek_item().expect("leaf should carry an item").key(),
            keep_key
        );
    }

    #[test]
    fn delete_item_keeps_an_unloaded_single_child_subtree_without_error() {
        let keep_key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let delete_key =
            Uint256::from_hex("19FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF")
                .expect("hex should parse");

        let loaded_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(keep_key, vec![13; 12]),
            1,
        );
        let shared_prefix = SHAMapTreeNode::new_inner(1);
        shared_prefix.set_child_hash(3, loaded_leaf.get_hash());
        shared_prefix.update_hash();

        let parent = SHAMapTreeNode::new_inner(1);
        parent.set_child(2, Some(shared_prefix));

        let deleted_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(delete_key, vec![14; 12]),
            1,
        );
        parent.set_child(9, Some(deleted_leaf));
        parent.update_hash_deep();

        let root = SHAMapTreeNode::new_inner(1);
        root.set_child(1, Some(parent));
        root.update_hash_deep();

        // Deleting the sole loaded sibling must not force loading the
        // hash-only descendant: the surviving single-child subtree is valid as
        // an inner node, so the delete completes without a MissingNode error.
        let deleted = delete_item(&root, delete_key)
            .expect("unloaded descendants must not block a valid delete");
        assert!(deleted);
        assert!(
            root.get_child(1)
                .expect("surviving root branch should remain")
                .is_inner(),
            "the surviving single-child subtree is retained as an inner node"
        );
    }

    #[test]
    fn mutable_snapshot_clones_the_written_path_only_when_needed() {
        let key = Uint256::from_array([0xA1; 32]);
        let mut original = MutableTree::new(1);
        original
            .add_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(key, vec![15; 12]),
            )
            .expect("initial insert should succeed");

        let original_root_before = original.root();
        let original_leaf_before = original
            .find_key(key)
            .expect("lookup should succeed")
            .expect("leaf should exist");
        let original_leaf_hash = original_leaf_before.get_hash();

        let mut snapshot = original.mutable_snapshot(2);
        assert_eq!(original.root().cowid(), 1);
        assert_eq!(snapshot.root().cowid(), 0);
        assert!(!same_node(&original.root(), &snapshot.root()));

        snapshot
            .update_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(key, vec![16; 12]),
            )
            .expect("snapshot update should succeed");

        let original_leaf_after = original
            .find_key(key)
            .expect("original lookup should succeed")
            .expect("original leaf should still exist");
        let snapshot_leaf_after = snapshot
            .find_key(key)
            .expect("snapshot lookup should succeed")
            .expect("snapshot leaf should still exist");

        assert_eq!(original_leaf_after.get_hash(), original_leaf_hash);
        assert_ne!(snapshot_leaf_after.get_hash(), original_leaf_hash);
        assert!(same_node(&original.root(), &original_root_before));
        assert!(!same_node(&original.root(), &snapshot.root()));
        assert!(!same_node(&original_leaf_after, &snapshot_leaf_after));
        assert_eq!(snapshot.root().cowid(), 2);
        assert_eq!(original.root().cowid(), 1);
    }

    #[test]
    fn mutable_snapshot_delete_leaves_original_tree_unchanged() {
        let keep_key =
            Uint256::from_hex("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let delete_key =
            Uint256::from_hex("1234A67890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF")
                .expect("hex should parse");
        let mut original = MutableTree::new(1);
        original
            .add_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(keep_key, vec![17; 12]),
            )
            .expect("first insert should succeed");
        original
            .add_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(delete_key, vec![18; 12]),
            )
            .expect("second insert should succeed");

        let mut snapshot = original.mutable_snapshot(2);
        snapshot
            .delete_item(delete_key)
            .expect("snapshot delete should succeed");

        assert!(
            original
                .find_key(delete_key)
                .expect("original lookup should succeed")
                .is_some()
        );
        assert!(
            snapshot
                .find_key(delete_key)
                .expect("snapshot lookup should succeed")
                .is_none()
        );
        assert!(
            original
                .find_key(keep_key)
                .expect("original keep lookup should succeed")
                .is_some()
        );
        assert!(
            snapshot
                .find_key(keep_key)
                .expect("snapshot keep lookup should succeed")
                .is_some()
        );
    }

    #[test]
    #[should_panic(
        expected = "loaded roots must not belong to a newer owner than the mutable tree"
    )]
    fn from_loaded_root_rejects_nodes_from_newer_owners() {
        let key = Uint256::from_array([0xD3; 32]);
        let foreign_leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![18; 12]),
            2,
        );
        let _ = MutableTree::from_loaded_root(foreign_leaf, 1);
    }

    #[test]
    fn share_loaded_subtree_marks_loaded_nodes_shareable() {
        let key = Uint256::from_array([0xC1; 32]);
        let mut tree = MutableTree::new(1);
        tree.add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![19; 12]),
        )
        .expect("insert should succeed");

        let count = tree.share_loaded_subtree();
        assert_eq!(count, 2);
        assert_eq!(tree.root().cowid(), 0);
        let leaf = tree
            .find_key(key)
            .expect("lookup should succeed")
            .expect("leaf should remain reachable");
        assert_eq!(leaf.cowid(), 0);
    }

    #[test]
    fn flush_dirty_writes_leaves_before_inners_and_can_replace_pointers() {
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
        let original_leaf_hash = original_leaf.get_hash();
        let original_item = original_leaf
            .peek_item()
            .expect("leaf should carry an item");

        let mut writes = Vec::new();
        let flushed = tree.flush_dirty(&mut |node| {
            writes.push((node.is_leaf(), node.get_hash()));
            if node.is_leaf() {
                SHAMapTreeNode::new_leaf_with_hash(
                    node.get_type(),
                    original_item.clone(),
                    0,
                    original_leaf_hash,
                )
            } else {
                node
            }
        });

        assert_eq!(flushed, 2);
        assert_eq!(
            writes,
            vec![(true, original_leaf_hash), (false, tree.root().get_hash())]
        );

        let replaced_leaf = tree
            .find_key(key)
            .expect("lookup should succeed")
            .expect("leaf should remain reachable");
        assert_eq!(replaced_leaf.cowid(), 0);
        assert_eq!(replaced_leaf.get_hash(), original_leaf_hash);
        assert!(!same_node(&original_leaf, &replaced_leaf));
    }

    #[test]
    fn detached_flush_preserves_dirty_owner_until_canonical_commit() {
        let key = Uint256::from_array([0xD8; 32]);
        let mut tree = MutableTree::new(9);
        tree.add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![22; 12]),
        )
        .expect("insert should succeed");
        let original_root = tree.root();
        let original_leaf = tree.find_key(key).expect("lookup").expect("dirty leaf");
        let mut order = Vec::new();
        let (detached, count) = tree
            .try_flush_dirty_detached(&mut |node| {
                order.push(node.is_leaf());
                Ok::<_, ()>(node)
            })
            .expect("detached flush plan");

        assert_eq!(count, 2);
        assert_eq!(order, vec![true, false]);
        assert!(same_node(&tree.root(), &original_root));
        assert!(same_node(
            &tree.find_key(key).expect("lookup").expect("dirty leaf"),
            &original_leaf
        ));
        assert_eq!(
            tree.root().cowid(),
            9,
            "dry run must retain dirty ownership"
        );

        let canonical_root = detached.root();
        let canonical_leaf = detached
            .find_key(key)
            .expect("lookup")
            .expect("canonical leaf");
        tree.flush_dirty(&mut |node| {
            if node.is_leaf() {
                canonical_leaf.clone()
            } else {
                canonical_root.clone()
            }
        });
        assert!(same_node(&tree.root(), &canonical_root));
        assert!(same_node(
            &tree.find_key(key).expect("lookup").expect("canonical leaf"),
            &canonical_leaf
        ));
    }

    #[test]
    fn share_loaded_subtree_clones_foreign_loaded_roots_before_sharing() {
        let key = Uint256::from_array([0xD1; 32]);
        let mut original = MutableTree::new(1);
        original
            .add_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(key, vec![20; 12]),
            )
            .expect("insert should succeed");

        let original_root = original.root();
        let mut foreign_owner = MutableTree::from_loaded_root(original_root.clone(), 2);
        let count = foreign_owner.share_loaded_subtree();

        assert_eq!(count, 2);
        assert!(!same_node(&foreign_owner.root(), &original_root));
        assert_eq!(foreign_owner.root().cowid(), 0);
        assert_eq!(original_root.cowid(), 1);
    }

    #[test]
    fn unshare_returns_zero_for_already_shareable_roots() {
        let key = Uint256::from_array([0xE1; 32]);
        let mut tree = MutableTree::new(1);
        tree.add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![22; 12]),
        )
        .expect("insert should succeed");
        assert_eq!(tree.unshare(), 2);

        let second = tree.unshare();
        assert_eq!(second, 0);
        assert_eq!(tree.root().cowid(), 0);
    }

    #[test]
    fn share_loaded_subtree_replaces_empty_mutable_roots_with_shareable_empty_roots() {
        let mut tree = MutableTree::new(7);
        let count = tree.share_loaded_subtree();
        assert_eq!(count, 1);
        assert!(tree.root().is_inner());
        assert!(tree.root().is_empty());
        assert_eq!(tree.root().cowid(), 0);
    }
}
