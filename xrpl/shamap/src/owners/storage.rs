//! `SHAMap::writeNode` storage-facing role.
//!
//! This captures the current `writeNode` contract:
//! - canonicalize the node by hash through the tree-node cache,
//! - serialize the canonical node with prefix bytes,
//! - emit a stored object record carrying type, bytes, hash, and ledger
//!   sequence,
//! - return the canonical node pointer so callers can adopt it.
//!
//! The current Rust migration keeps both:
//! - a standalone sink seam for unit testing and incremental ports,
//! - a family-backed flush path that better matches the reference owner boundary,
//! - owner-backed direct-read wrappers so the mutable owner can reuse the
//!   shared family cache/fetch policy instead of staying write-only.
//!
//! The Rust node store below this seam supports both RocksDB and NuDB backends;
//! SHAMap maintains a backend-agnostic contract here.

use crate::compare::{
    DeepCompareEvent, Delta, compare as compare_impl, deep_compare as deep_compare_impl,
    deep_compare_with_events as deep_compare_with_events_impl,
};
use crate::difference::visit_differences as visit_differences_impl;
use crate::family::{
    CachedFetchResult, FullBelowCache, MissingNodeReporter, OwnerBackedFetchState, SHAMapFamily,
    SHAMapNodeFetcher,
};
use crate::item::SHAMapItem;
use crate::iteration::{
    lower_bound as lower_bound_impl, peek_first_item as peek_first_item_impl,
    peek_next_item as peek_next_item_impl, upper_bound as upper_bound_impl,
};
use crate::mutation::{MutableTree, MutationError};
use crate::node_id::SHAMapNodeId;
use crate::proof_path::{
    get_proof_path_backed as get_proof_path_impl, has_inner_node as has_inner_node_impl,
    has_leaf_node_backed as has_leaf_node_backed_impl,
};
use crate::read::{
    has_item as has_item_impl, peek_item as peek_item_impl,
    peek_item_with_hash as peek_item_with_hash_impl,
};
use crate::search::{NodePathEntry, find_key as find_key_impl};
use crate::sync::{
    ParallelWalkResult, SHAMapMissingNode, SHAMapType, walk_map as walk_map_impl,
    walk_map_parallel as walk_map_parallel_impl, walk_map_parallel_with_observer,
};
use crate::traversal::TraversalError;
use crate::tree_node::{SHAMapCodecError, SHAMapTreeNode};
use crate::tree_node_cache::TreeNodeCache;
use crate::visitor::{visit_leaves as visit_leaves_impl, visit_nodes as visit_nodes_impl};
use basics::base_uint::Uint256;
use basics::blob::Blob;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::CacheClock;
use std::hash::BuildHasher;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum NodeObjectType {
    Unknown = 0,
    Ledger = 1,
    AccountNode = 3,
    TransactionNode = 4,
    Dummy = 512,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoredNode {
    object_type: NodeObjectType,
    data: Blob,
    hash: Uint256,
    ledger_seq: u32,
}

impl StoredNode {
    pub fn new(object_type: NodeObjectType, data: Blob, hash: Uint256, ledger_seq: u32) -> Self {
        Self {
            object_type,
            data,
            hash,
            ledger_seq,
        }
    }

    pub fn object_type(&self) -> NodeObjectType {
        self.object_type
    }

    pub fn data(&self) -> &[u8] {
        &self.data
    }

    pub fn hash(&self) -> &Uint256 {
        &self.hash
    }

    pub fn ledger_seq(&self) -> u32 {
        self.ledger_seq
    }
}

pub trait NodeStoreSink {
    fn store(&mut self, node: StoredNode);
}

#[derive(Debug, Clone)]
pub struct StorageTree<C, S> {
    tree: MutableTree,
    cache: Arc<TreeNodeCache<C, S>>,
    backed: bool,
    ledger_seq: u32,
    owner_fetch_state: OwnerBackedFetchState,
}

impl<C, S> StorageTree<C, S>
where
    C: CacheClock,
    S: BuildHasher + Clone,
{
    pub fn new(cowid: u32, backed: bool, ledger_seq: u32, cache: Arc<TreeNodeCache<C, S>>) -> Self {
        Self {
            tree: MutableTree::new(cowid),
            cache,
            backed,
            ledger_seq,
            owner_fetch_state: OwnerBackedFetchState::default(),
        }
    }

    pub fn from_loaded_root(
        root: SharedIntrusive<SHAMapTreeNode>,
        cowid: u32,
        backed: bool,
        ledger_seq: u32,
        cache: Arc<TreeNodeCache<C, S>>,
    ) -> Self {
        Self {
            tree: MutableTree::from_loaded_root(root, cowid),
            cache,
            backed,
            ledger_seq,
            owner_fetch_state: OwnerBackedFetchState::default(),
        }
    }

    pub fn new_with_family<FB, F, MR, NS>(
        cowid: u32,
        backed: bool,
        ledger_seq: u32,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Self
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        Self::new(cowid, backed, ledger_seq, family.tree_node_cache())
    }

    pub fn from_loaded_root_with_family<FB, F, MR, NS>(
        root: SharedIntrusive<SHAMapTreeNode>,
        cowid: u32,
        backed: bool,
        ledger_seq: u32,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Self
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        Self::from_loaded_root(root, cowid, backed, ledger_seq, family.tree_node_cache())
    }

    pub fn root(&self) -> SharedIntrusive<SHAMapTreeNode> {
        self.tree.root()
    }

    pub fn hash(&mut self) -> SHAMapHash {
        let mut hash = self.root().get_hash();
        if hash.is_zero() {
            self.unshare();
            hash = self.root().get_hash();
        }
        hash
    }

    pub fn mutable_snapshot(&self, next_cowid: u32) -> Self {
        Self {
            tree: self.tree.mutable_snapshot(next_cowid),
            cache: self.cache.clone(),
            backed: self.backed,
            ledger_seq: self.ledger_seq,
            owner_fetch_state: OwnerBackedFetchState::default(),
        }
    }

    pub fn backed(&self) -> bool {
        self.backed
    }

    pub fn ledger_seq(&self) -> u32 {
        self.ledger_seq
    }

    pub fn set_ledger_seq(&mut self, ledger_seq: u32) {
        self.ledger_seq = ledger_seq;
    }

    pub fn set_unbacked(&mut self) {
        self.backed = false;
    }

    pub fn is_full(&self) -> bool {
        self.owner_fetch_state.is_full()
    }

    pub fn set_full(&self) {
        self.owner_fetch_state.set_full();
    }

    fn fetch_node_with_family<FB, F, MR, NS>(
        &self,
        hash: SHAMapHash,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Option<SharedIntrusive<SHAMapTreeNode>>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        match family.fetch_cached_node_result_with_ledger_seq(hash, self.ledger_seq) {
            CachedFetchResult::Found(node) => Some(node),
            CachedFetchResult::Missing => {
                self.owner_fetch_state
                    .report_missing_node_once(self.ledger_seq, hash, family);
                None
            }
            CachedFetchResult::InvalidBlob => None,
        }
    }

    pub fn has_item<F>(&self, id: Uint256, fetch: &mut F) -> Result<bool, TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        has_item_impl(&self.root(), id, self.backed, fetch)
    }

    pub fn add_item(
        &mut self,
        node_type: crate::tree_node::SHAMapNodeType,
        item: SHAMapItem,
    ) -> Result<bool, MutationError> {
        self.tree.add_item(node_type, item)
    }

    pub fn update_item(
        &mut self,
        node_type: crate::tree_node::SHAMapNodeType,
        item: SHAMapItem,
    ) -> Result<bool, MutationError> {
        self.tree.update_item(node_type, item)
    }

    pub fn delete_item(&mut self, target: Uint256) -> Result<bool, MutationError> {
        self.tree.delete_item(target)
    }

    pub fn walk_map<F>(
        &self,
        map_type: SHAMapType,
        missing_nodes: &mut Vec<SHAMapMissingNode>,
        max_missing: i32,
        fetch: &mut F,
    ) where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        walk_map_impl(
            &self.root(),
            map_type,
            missing_nodes,
            max_missing,
            self.backed,
            fetch,
        );
    }

    pub fn walk_map_with_family<FB, F, MR, NS>(
        &self,
        map_type: SHAMapType,
        missing_nodes: &mut Vec<SHAMapMissingNode>,
        max_missing: i32,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        self.walk_map(map_type, missing_nodes, max_missing, &mut |hash| {
            self.fetch_node_with_family(hash, family)
        });
    }

    pub fn walk_map_parallel<F>(
        &self,
        map_type: SHAMapType,
        missing_nodes: &mut Vec<SHAMapMissingNode>,
        max_missing: i32,
        fetch: &F,
    ) -> bool
    where
        F: Fn(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> + Sync,
    {
        walk_map_parallel_impl(
            &self.root(),
            map_type,
            missing_nodes,
            max_missing,
            self.backed,
            fetch,
        )
    }

    pub fn walk_map_parallel_with_family<FB, F, MR, NS>(
        &self,
        map_type: SHAMapType,
        missing_nodes: &mut Vec<SHAMapMissingNode>,
        max_missing: i32,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> bool
    where
        FB: FullBelowCache + Send,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
        S: Send + Sync,
        NS: Send,
    {
        let result = walk_map_parallel_with_observer(
            &self.root(),
            map_type,
            missing_nodes,
            max_missing,
            self.backed,
            &|hash| self.fetch_node_with_family(hash, family),
            &mut |root_child_index| {
                family.log_debug(&format!("starting worker {root_child_index}"))
            },
        );
        if let ParallelWalkResult::WorkerPanics(panics) = &result {
            let mut message = String::from("Exception(s) in ledger load: ");
            for panic in panics {
                message.push_str(panic);
                message.push_str(", ");
            }
            family.log_error(&message);
        }
        result.completed()
    }

    pub fn has_item_with_family<FB, F, MR, NS>(
        &self,
        id: Uint256,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<bool, TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        has_item_impl(&self.root(), id, self.backed, &mut |hash| {
            self.fetch_node_with_family(hash, family)
        })
    }

    pub fn peek_item<F>(
        &self,
        id: Uint256,
        fetch: &mut F,
    ) -> Result<Option<SHAMapItem>, TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        peek_item_impl(&self.root(), id, self.backed, fetch)
    }

    pub fn peek_item_with_family<FB, F, MR, NS>(
        &self,
        id: Uint256,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<Option<SHAMapItem>, TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        peek_item_impl(&self.root(), id, self.backed, &mut |hash| {
            self.fetch_node_with_family(hash, family)
        })
    }

    pub fn peek_item_with_hash<F>(
        &self,
        id: Uint256,
        fetch: &mut F,
    ) -> Result<Option<(SHAMapItem, SHAMapHash)>, TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        peek_item_with_hash_impl(&self.root(), id, self.backed, fetch)
    }

    pub fn peek_item_with_hash_and_family<FB, F, MR, NS>(
        &self,
        id: Uint256,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<Option<(SHAMapItem, SHAMapHash)>, TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        peek_item_with_hash_impl(&self.root(), id, self.backed, &mut |hash| {
            self.fetch_node_with_family(hash, family)
        })
    }

    pub fn has_leaf_node<F>(
        &self,
        tag: Uint256,
        target_node_hash: SHAMapHash,
        fetch: &mut F,
    ) -> Result<bool, TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        has_leaf_node_backed_impl(&self.root(), tag, target_node_hash, self.backed, fetch)
    }

    pub fn has_leaf_node_with_family<FB, F, MR, NS>(
        &self,
        tag: Uint256,
        target_node_hash: SHAMapHash,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<bool, TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        has_leaf_node_backed_impl(
            &self.root(),
            tag,
            target_node_hash,
            self.backed,
            &mut |hash| self.fetch_node_with_family(hash, family),
        )
    }

    pub fn has_inner_node<F>(
        &self,
        target_node_id: SHAMapNodeId,
        target_node_hash: SHAMapHash,
        fetch: &mut F,
    ) -> Result<bool, TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        has_inner_node_impl(
            &self.root(),
            target_node_id,
            target_node_hash,
            self.backed,
            fetch,
        )
    }

    pub fn has_inner_node_with_family<FB, F, MR, NS>(
        &self,
        target_node_id: SHAMapNodeId,
        target_node_hash: SHAMapHash,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<bool, TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        has_inner_node_impl(
            &self.root(),
            target_node_id,
            target_node_hash,
            self.backed,
            &mut |hash| self.fetch_node_with_family(hash, family),
        )
    }

    pub fn get_proof_path<F>(
        &self,
        key: Uint256,
        fetch: &mut F,
    ) -> Result<Option<Vec<Blob>>, TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        get_proof_path_impl(&self.root(), key, self.backed, fetch)
    }

    pub fn get_proof_path_with_family<FB, F, MR, NS>(
        &self,
        key: Uint256,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<Option<Vec<Blob>>, TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        get_proof_path_impl(&self.root(), key, self.backed, &mut |hash| {
            self.fetch_node_with_family(hash, family)
        })
    }

    pub fn find_key<F>(
        &self,
        key: Uint256,
        fetch: &mut F,
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        find_key_impl(&self.root(), key, self.backed, fetch)
    }

    pub fn find_key_with_family<FB, F, MR, NS>(
        &self,
        key: Uint256,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        find_key_impl(&self.root(), key, self.backed, &mut |hash| {
            self.fetch_node_with_family(hash, family)
        })
    }

    pub fn peek_first_item<F>(
        &self,
        stack: &mut Vec<NodePathEntry>,
        fetch: &mut F,
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        peek_first_item_impl(&self.root(), stack, self.backed, fetch)
    }

    pub fn peek_first_item_with_family<FB, F, MR, NS>(
        &self,
        stack: &mut Vec<NodePathEntry>,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        peek_first_item_impl(&self.root(), stack, self.backed, &mut |hash| {
            self.fetch_node_with_family(hash, family)
        })
    }

    pub fn peek_next_item<F>(
        &self,
        id: Uint256,
        stack: &mut Vec<NodePathEntry>,
        fetch: &mut F,
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        peek_next_item_impl(id, stack, self.backed, fetch)
    }

    pub fn peek_next_item_with_family<FB, F, MR, NS>(
        &self,
        id: Uint256,
        stack: &mut Vec<NodePathEntry>,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        peek_next_item_impl(id, stack, self.backed, &mut |hash| {
            self.fetch_node_with_family(hash, family)
        })
    }

    pub fn upper_bound<F>(
        &self,
        id: Uint256,
        fetch: &mut F,
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        upper_bound_impl(&self.root(), id, self.backed, fetch)
    }

    pub fn upper_bound_with_family<FB, F, MR, NS>(
        &self,
        id: Uint256,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        upper_bound_impl(&self.root(), id, self.backed, &mut |hash| {
            self.fetch_node_with_family(hash, family)
        })
    }

    pub fn lower_bound<F>(
        &self,
        id: Uint256,
        fetch: &mut F,
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        lower_bound_impl(&self.root(), id, self.backed, fetch)
    }

    pub fn lower_bound_with_family<FB, F, MR, NS>(
        &self,
        id: Uint256,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        lower_bound_impl(&self.root(), id, self.backed, &mut |hash| {
            self.fetch_node_with_family(hash, family)
        })
    }

    pub fn visit_nodes<F, V>(&self, fetch: &mut F, visit: &mut V) -> Result<(), TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
        V: FnMut(&SharedIntrusive<SHAMapTreeNode>) -> bool,
    {
        visit_nodes_impl(&self.root(), self.backed, fetch, visit)
    }

    pub fn visit_nodes_with_family<FB, F, MR, NS, V>(
        &self,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
        visit: &mut V,
    ) -> Result<(), TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
        V: FnMut(&SharedIntrusive<SHAMapTreeNode>) -> bool,
    {
        visit_nodes_impl(
            &self.root(),
            self.backed,
            &mut |hash| self.fetch_node_with_family(hash, family),
            visit,
        )
    }

    pub fn visit_leaves<F, V>(&self, fetch: &mut F, visit: &mut V) -> Result<(), TraversalError>
    where
        F: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
        V: FnMut(&SHAMapItem),
    {
        visit_leaves_impl(&self.root(), self.backed, fetch, visit)
    }

    pub fn visit_leaves_with_family<FB, F, MR, NS, V>(
        &self,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
        visit: &mut V,
    ) -> Result<(), TraversalError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
        V: FnMut(&SHAMapItem),
    {
        visit_leaves_impl(
            &self.root(),
            self.backed,
            &mut |hash| self.fetch_node_with_family(hash, family),
            visit,
        )
    }

    pub fn compare<FL, FR>(
        &self,
        other: &StorageTree<C, S>,
        differences: &mut Delta,
        max_count: i32,
        left_fetch: &mut FL,
        right_fetch: &mut FR,
    ) -> Result<bool, TraversalError>
    where
        FL: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
        FR: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        compare_impl(
            &self.root(),
            &other.root(),
            self.backed,
            left_fetch,
            other.backed,
            right_fetch,
            differences,
            max_count,
        )
    }

    pub fn compare_with_families<FBL, FL, MRL, NSL, FBR, FR, MRR, NSR>(
        &self,
        other: &StorageTree<C, S>,
        differences: &mut Delta,
        max_count: i32,
        left_family: &SHAMapFamily<C, S, FBL, FL, MRL, NSL>,
        right_family: &SHAMapFamily<C, S, FBR, FR, MRR, NSR>,
    ) -> Result<bool, TraversalError>
    where
        FBL: FullBelowCache,
        FL: SHAMapNodeFetcher,
        MRL: MissingNodeReporter,
        FBR: FullBelowCache,
        FR: SHAMapNodeFetcher,
        MRR: MissingNodeReporter,
    {
        compare_impl(
            &self.root(),
            &other.root(),
            self.backed,
            &mut |hash| self.fetch_node_with_family(hash, left_family),
            other.backed,
            &mut |hash| other.fetch_node_with_family(hash, right_family),
            differences,
            max_count,
        )
    }

    pub fn deep_compare<FL, FR>(
        &self,
        other: &StorageTree<C, S>,
        left_fetch: &mut FL,
        right_fetch: &mut FR,
    ) -> bool
    where
        FL: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
        FR: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
    {
        deep_compare_impl(
            &self.root(),
            &other.root(),
            self.backed,
            left_fetch,
            other.backed,
            right_fetch,
        )
    }

    pub fn deep_compare_with_families<FBL, FL, MRL, NSL, FBR, FR, MRR, NSR>(
        &self,
        other: &StorageTree<C, S>,
        left_family: &SHAMapFamily<C, S, FBL, FL, MRL, NSL>,
        right_family: &SHAMapFamily<C, S, FBR, FR, MRR, NSR>,
    ) -> bool
    where
        FBL: FullBelowCache,
        FL: SHAMapNodeFetcher,
        MRL: MissingNodeReporter,
        FBR: FullBelowCache,
        FR: SHAMapNodeFetcher,
        MRR: MissingNodeReporter,
    {
        deep_compare_with_events_impl(
            &self.root(),
            &other.root(),
            self.backed,
            &mut |hash| self.fetch_node_with_family(hash, left_family),
            other.backed,
            &mut |hash| other.fetch_node_with_family(hash, right_family),
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

    pub fn visit_differences<SF, HF, V>(
        &self,
        have: Option<&StorageTree<C, S>>,
        self_fetch: &mut SF,
        have_fetch: &mut HF,
        visit: &mut V,
    ) -> Result<(), TraversalError>
    where
        SF: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
        HF: FnMut(SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>,
        V: FnMut(&SharedIntrusive<SHAMapTreeNode>) -> bool,
    {
        let have_root = have.map(|tree| tree.root());
        let have_ref = have_root.as_ref();
        let have_backed = have.map(|tree| tree.backed()).unwrap_or(false);

        visit_differences_impl(
            &self.root(),
            have_ref,
            self.backed,
            self_fetch,
            have_backed,
            have_fetch,
            visit,
        )
    }

    pub fn visit_differences_with_families<FBS, FS, MRS, NSS, FBH, FH, MRH, NSH, V>(
        &self,
        have: Option<&StorageTree<C, S>>,
        self_family: &SHAMapFamily<C, S, FBS, FS, MRS, NSS>,
        have_family: Option<&SHAMapFamily<C, S, FBH, FH, MRH, NSH>>,
        visit: &mut V,
    ) -> Result<(), TraversalError>
    where
        FBS: FullBelowCache,
        FS: SHAMapNodeFetcher,
        MRS: MissingNodeReporter,
        FBH: FullBelowCache,
        FH: SHAMapNodeFetcher,
        MRH: MissingNodeReporter,
        V: FnMut(&SharedIntrusive<SHAMapTreeNode>) -> bool,
    {
        let have_root = have.map(|tree| tree.root());
        let have_ref = have_root.as_ref();
        let have_backed = have.map(|tree| tree.backed()).unwrap_or(false);

        visit_differences_impl(
            &self.root(),
            have_ref,
            self.backed,
            &mut |hash| self.fetch_node_with_family(hash, self_family),
            have_backed,
            &mut |hash| {
                have.and_then(|tree| {
                    have_family.and_then(|family| tree.fetch_node_with_family(hash, family))
                })
            },
            visit,
        )
    }

    pub fn flush_dirty<W>(
        &mut self,
        object_type: NodeObjectType,
        sink: &mut W,
    ) -> Result<usize, SHAMapCodecError>
    where
        W: NodeStoreSink,
    {
        if !self.backed {
            return Ok(self.tree.unshare());
        }

        let mut writer =
            CanonicalNodeWriter::new(self.cache.as_ref(), object_type, self.ledger_seq, sink);
        self.tree
            .try_flush_dirty(&mut |node| writer.write_node(node))
    }

    pub fn flush_dirty_with_family<FB, F, MR, NS>(
        &mut self,
        object_type: NodeObjectType,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) -> Result<usize, SHAMapCodecError>
    where
        FB: FullBelowCache,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
        NS: NodeStoreSink,
    {
        if !self.backed {
            return Ok(self.tree.unshare());
        }

        let family_cache = family.tree_node_cache();
        assert!(
            Arc::ptr_eq(&self.cache, &family_cache),
            "family-backed flush requires StorageTree and SHAMapFamily to share the same tree cache"
        );

        self.tree
            .try_flush_dirty(&mut |node| family.write_node(object_type, self.ledger_seq, node))
    }

    pub fn unshare(&mut self) -> usize {
        self.tree.unshare()
    }
}

pub struct CanonicalNodeWriter<'a, C, S, W> {
    cache: &'a TreeNodeCache<C, S>,
    object_type: NodeObjectType,
    ledger_seq: u32,
    sink: &'a mut W,
}

impl<'a, C, S, W> CanonicalNodeWriter<'a, C, S, W>
where
    C: CacheClock,
    S: BuildHasher + Clone,
    W: NodeStoreSink,
{
    pub fn new(
        cache: &'a TreeNodeCache<C, S>,
        object_type: NodeObjectType,
        ledger_seq: u32,
        sink: &'a mut W,
    ) -> Self {
        Self {
            cache,
            object_type,
            ledger_seq,
            sink,
        }
    }

    pub fn write_node(
        &mut self,
        mut node: SharedIntrusive<SHAMapTreeNode>,
    ) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
        assert_eq!(
            node.cowid(),
            0,
            "write_node requires a shareable node produced by walk_subtree"
        );

        let key = *node.get_hash().as_uint256();
        self.cache.canonicalize_replace_client(&key, &mut node);

        let data = node.serialize_with_prefix()?;
        self.sink.store(StoredNode::new(
            self.object_type,
            data,
            key,
            self.ledger_seq,
        ));
        Ok(node)
    }
}

#[cfg(test)]
mod tests {
    use super::{CanonicalNodeWriter, NodeObjectType, NodeStoreSink, StorageTree, StoredNode};
    use crate::family::{
        NullFullBelowCache, NullMissingNodeReporter, NullNodeFetcher, SHAMapFamily,
    };
    use crate::item::SHAMapItem;
    use crate::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use crate::tree_node_cache::TreeNodeCache;
    use basics::base_uint::Uint256;
    use basics::tagged_cache::ManualClock;
    use std::sync::Arc;
    use time::Duration;

    #[derive(Default)]
    struct RecordingNodeStore {
        stored: Vec<StoredNode>,
    }

    impl NodeStoreSink for RecordingNodeStore {
        fn store(&mut self, node: StoredNode) {
            self.stored.push(node);
        }
    }

    fn same_node(left: &SHAMapTreeNode, right: &SHAMapTreeNode) -> bool {
        std::ptr::eq(left, right)
    }

    #[test]
    fn write_node_canonicalizes_and_records_stored_object() {
        let cache = TreeNodeCache::new("tree", 8, Duration::seconds(1), ManualClock::new(0));
        let key = Uint256::from_array([0xA1; 32]);
        let item = SHAMapItem::new(key, vec![7; 12]);
        let canonical = SHAMapTreeNode::new_leaf(SHAMapNodeType::AccountState, item.clone(), 0);
        let mut cached = canonical.clone();
        assert!(!cache.canonicalize_replace_client(canonical.get_hash().as_uint256(), &mut cached));

        let duplicate = SHAMapTreeNode::new_leaf(SHAMapNodeType::AccountState, item, 0);
        let expected_bytes = canonical
            .serialize_with_prefix()
            .expect("leaf should serialize with a prefix");

        let mut sink = RecordingNodeStore::default();
        let mut writer =
            CanonicalNodeWriter::new(&cache, NodeObjectType::AccountNode, 55, &mut sink);
        let resolved = writer
            .write_node(duplicate)
            .expect("writer should accept prefix-serializable nodes");

        assert!(same_node(&resolved, &canonical));
        assert_eq!(
            sink.stored,
            vec![StoredNode::new(
                NodeObjectType::AccountNode,
                expected_bytes,
                *canonical.get_hash().as_uint256(),
                55,
            )]
        );
    }

    #[test]
    fn storage_tree_flush_dirty_skips_store_when_unbacked() {
        let cache = Arc::new(TreeNodeCache::new(
            "tree",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let key = Uint256::from_array([0xB1; 32]);
        let mut tree = StorageTree::new(1, false, 91, cache);
        tree.root().set_child(
            3,
            Some(SHAMapTreeNode::new_leaf(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(key, vec![5; 12]),
                1,
            )),
        );
        tree.root().update_hash_deep();

        let mut sink = RecordingNodeStore::default();
        let flushed = tree
            .flush_dirty(NodeObjectType::AccountNode, &mut sink)
            .expect("unbacked flush should not reach serialization");

        assert_eq!(flushed, 2);
        assert!(sink.stored.is_empty());
        assert_eq!(tree.root().cowid(), 0);
    }

    #[test]
    fn storage_tree_flush_dirty_stores_when_backed() {
        let cache = Arc::new(TreeNodeCache::new(
            "tree",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let key = Uint256::from_array([0xC1; 32]);
        let canonical = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![6; 12]),
            0,
        );
        let mut cached = canonical.clone();
        assert!(!cache.canonicalize_replace_client(canonical.get_hash().as_uint256(), &mut cached));

        let mut tree = StorageTree::new(2, true, 92, cache);
        tree.root().set_child(
            4,
            Some(SHAMapTreeNode::new_leaf_with_hash(
                SHAMapNodeType::AccountState,
                canonical
                    .peek_item()
                    .expect("canonical leaf should carry an item"),
                2,
                canonical.get_hash(),
            )),
        );
        tree.root().update_hash_deep();

        let mut sink = RecordingNodeStore::default();
        let flushed = tree
            .flush_dirty(NodeObjectType::AccountNode, &mut sink)
            .expect("backed flush should serialize and store");

        assert_eq!(flushed, 2);
        let leaf_after = tree
            .root()
            .get_child(4)
            .expect("root should still carry the flushed leaf");
        assert!(same_node(&leaf_after, &canonical));
        assert_eq!(sink.stored.len(), 2);
        assert_eq!(sink.stored[0].ledger_seq(), 92);
        assert_eq!(sink.stored[0].object_type(), NodeObjectType::AccountNode);
        assert_eq!(sink.stored[0].hash(), canonical.get_hash().as_uint256());
    }

    #[test]
    fn storage_tree_flush_dirty_with_family_uses_family_owned_node_store() {
        let cache = Arc::new(TreeNodeCache::new(
            "family-tree",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let key = Uint256::from_array([0xD1; 32]);
        let canonical = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![8; 12]),
            0,
        );
        let mut cached = canonical.clone();
        assert!(!cache.canonicalize_replace_client(canonical.get_hash().as_uint256(), &mut cached));

        let family = SHAMapFamily::new_with_node_store(
            cache.clone(),
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            NullMissingNodeReporter,
            RecordingNodeStore::default(),
        );
        let mut tree = StorageTree::new_with_family(2, true, 93, &family);
        tree.root().set_child(
            5,
            Some(SHAMapTreeNode::new_leaf_with_hash(
                SHAMapNodeType::AccountState,
                canonical
                    .peek_item()
                    .expect("canonical leaf should carry an item"),
                2,
                canonical.get_hash(),
            )),
        );
        tree.root().update_hash_deep();

        let flushed = tree
            .flush_dirty_with_family(NodeObjectType::AccountNode, &family)
            .expect("family-backed flush should serialize and store");

        assert_eq!(flushed, 2);
        let leaf_after = tree
            .root()
            .get_child(5)
            .expect("root should still carry the flushed leaf");
        assert!(same_node(&leaf_after, &canonical));
        family.with_node_store(|node_store| {
            assert_eq!(node_store.stored.len(), 2);
            assert_eq!(node_store.stored[0].ledger_seq(), 93);
            assert_eq!(
                node_store.stored[0].hash(),
                canonical.get_hash().as_uint256()
            );
        });
    }
}
