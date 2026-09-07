#![allow(clippy::type_complexity)]
//! `xrpl/shamap/SHAMapTreeNode.h`, `SHAMapInnerNode.h`, and
//! `SHAMapLeafNode.h` compatibility surface.
//!
//! This chooses a concrete owner plus enum layout instead of reference base-class
//! polymorphism so we can preserve intrusive lifetimes without requiring
//! trait-object intrusive pointers in the first SHAMap slice.

use crate::item::SHAMapItem;
use basics::base_uint::Uint256;
use basics::intrusive_pointer::{
    CompactIntrusiveOwner, IntrusiveObject, SharedIntrusive, make_shared_intrusive,
};
use basics::intrusive_ref_counts::IntrusiveRefCounts;
use basics::sha_map_hash::SHAMapHash;
use parking_lot::RwLock;
use sha2::{Digest, Sha512};
use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use std::fmt;
use std::marker::PhantomData;
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicU16, AtomicU32, Ordering};

pub const BRANCH_FACTOR: usize = 16;
const HASH_PREFIX_TRANSACTION_ID: u32 = 0x54584E00;
const HASH_PREFIX_TX_NODE: u32 = 0x534E4400;
const HASH_PREFIX_LEAF_NODE: u32 = 0x4D4C4E00;
const HASH_PREFIX_INNER_NODE: u32 = 0x4D494E00;
pub const WIRE_TYPE_TRANSACTION: u8 = 0;
pub const WIRE_TYPE_ACCOUNT_STATE: u8 = 1;
pub const WIRE_TYPE_INNER: u8 = 2;
pub const WIRE_TYPE_COMPRESSED_INNER: u8 = 3;
pub const WIRE_TYPE_TRANSACTION_WITH_META: u8 = 4;
const MIN_SHAMAP_ITEM_BYTES: usize = 12;
const TAGGED_POINTER_BOUNDARIES: [usize; 4] = [2, 4, 6, BRANCH_FACTOR];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SHAMapNodeType {
    Inner = 1,
    TransactionNm = 2,
    TransactionMd = 3,
    AccountState = 4,
}

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone)]
pub enum SHAMapTreeNodeKind {
    Inner(SHAMapInnerNodeData),
    Leaf(SHAMapLeafNodeData),
}

#[derive(Debug, Clone)]
pub struct SHAMapInnerNodeData {
    is_branch: u16,
    full_below_gen: u32,
}

#[derive(Debug, Clone)]
pub struct SHAMapLeafNodeData {
    node_type: SHAMapNodeType,
    item: SHAMapItem,
}

/// reference-shape `TaggedPointer`: low two bits are the capacity tag, and the
/// pointer bits address one contiguous allocation of hashes followed by children.
struct TaggedPointer {
    tagged: usize,
    _marker: PhantomData<SHAMapTreeNode>,
}

impl fmt::Debug for TaggedPointer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TaggedPointer")
            .field("tag", &self.tag())
            .field("capacity", &self.capacity())
            .finish_non_exhaustive()
    }
}

impl TaggedPointer {
    fn new(num_children: usize) -> Self {
        let tag = boundary_index(num_children);
        let capacity = TAGGED_POINTER_BOUNDARIES[tag];
        let (ptr, layout) = allocate_tagged_arrays(capacity);
        let hashes = ptr.as_ptr().cast::<SHAMapHash>();
        let children = children_ptr(ptr, capacity);
        unsafe {
            for index in 0..capacity {
                ptr::write(hashes.add(index), SHAMapHash::default());
                ptr::write(children.add(index), SharedIntrusive::new());
            }
        }
        let raw = ptr.as_ptr() as usize;
        debug_assert_eq!(raw & 0b11, 0);
        debug_assert_eq!(layout.align() & 0b11, 0);
        Self {
            tagged: raw | tag,
            _marker: PhantomData,
        }
    }

    fn tag(&self) -> usize {
        self.tagged & 0b11
    }

    fn ptr(&self) -> NonNull<u8> {
        NonNull::new((self.tagged & !0b11) as *mut u8)
            .expect("tagged pointer allocation must be non-null")
    }

    fn capacity(&self) -> usize {
        TAGGED_POINTER_BOUNDARIES[self.tag()]
    }

    fn is_dense(&self) -> bool {
        self.capacity() == BRANCH_FACTOR
    }

    fn hashes(&self) -> *mut SHAMapHash {
        self.ptr().as_ptr().cast::<SHAMapHash>()
    }

    fn children(&self) -> *mut SharedIntrusive<SHAMapTreeNode> {
        children_ptr(self.ptr(), self.capacity())
    }

    fn child_index(&self, is_branch: u16, branch: usize) -> Option<usize> {
        validate_branch(branch);
        if self.is_dense() {
            return Some(branch);
        }
        if (is_branch & (1 << branch)) == 0 {
            return None;
        }
        let mask = (1u16 << branch) - 1;
        Some((is_branch & mask).count_ones() as usize)
    }

    fn get_hash(&self, is_branch: u16, branch: usize) -> SHAMapHash {
        let Some(index) = self.child_index(is_branch, branch) else {
            return SHAMapHash::default();
        };
        unsafe { *self.hashes().add(index) }
    }

    fn set_hash_at_index(&self, index: usize, hash: SHAMapHash) {
        debug_assert!(index < self.capacity());
        unsafe {
            *self.hashes().add(index) = hash;
        }
    }

    fn get_child_at_index(&self, index: usize) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        debug_assert!(index < self.capacity());
        let child = unsafe { &*self.children().add(index) };
        (!child.is_null()).then(|| child.clone())
    }

    unsafe fn get_child_ptr_at_index(&self, index: usize) -> Option<*const SHAMapTreeNode> {
        debug_assert!(index < self.capacity());
        unsafe {
            let child = &*self.children().add(index);
            (!child.is_null()).then(|| &**child as *const SHAMapTreeNode)
        }
    }

    fn has_child_at_index(&self, index: usize) -> bool {
        debug_assert!(index < self.capacity());
        unsafe { !(&*self.children().add(index)).is_null() }
    }

    fn set_child_at_index(&self, index: usize, child: Option<SharedIntrusive<SHAMapTreeNode>>) {
        debug_assert!(index < self.capacity());
        unsafe {
            *self.children().add(index) = child.unwrap_or_default();
        }
    }

    fn iter_children<F>(&self, is_branch: u16, mut f: F)
    where
        F: FnMut(usize, SHAMapHash),
    {
        if self.is_dense() {
            for branch in 0..BRANCH_FACTOR {
                let hash = unsafe { *self.hashes().add(branch) };
                f(branch, hash);
            }
        } else {
            let mut compact_index = 0;
            for branch in 0..BRANCH_FACTOR {
                if (is_branch & (1 << branch)) != 0 {
                    let hash = unsafe { *self.hashes().add(compact_index) };
                    compact_index += 1;
                    f(branch, hash);
                } else {
                    f(branch, SHAMapHash::default());
                }
            }
        }
    }

    fn iter_non_empty_child_indexes<F>(&self, is_branch: u16, mut f: F)
    where
        F: FnMut(usize, usize),
    {
        if self.is_dense() {
            for branch in 0..BRANCH_FACTOR {
                if (is_branch & (1 << branch)) != 0 {
                    f(branch, branch);
                }
            }
        } else {
            let mut compact_index = 0;
            for branch in 0..BRANCH_FACTOR {
                if (is_branch & (1 << branch)) != 0 {
                    f(branch, compact_index);
                    compact_index += 1;
                }
            }
        }
    }

    fn resize(&mut self, is_branch: u16, to_allocate: usize) {
        self.rebuild(is_branch, is_branch, to_allocate);
    }

    fn rebuild(&mut self, src_branches: u16, dst_branches: u16, to_allocate: usize) {
        let new_capacity = capacity_for_children(to_allocate);
        if new_capacity == self.capacity() && src_branches == dst_branches {
            return;
        }

        let next = TaggedPointer::new(to_allocate);
        let src_dense = self.is_dense();
        let dst_dense = next.is_dense();

        for branch in 0..BRANCH_FACTOR {
            if (dst_branches & (1 << branch)) == 0 {
                continue;
            }
            let Some(dst_index) = next.child_index(dst_branches, branch) else {
                continue;
            };

            if (src_branches & (1 << branch)) == 0 {
                continue;
            }

            let src_index = if src_dense {
                branch
            } else {
                ((src_branches & ((1u16 << branch) - 1)).count_ones()) as usize
            };
            let hash = unsafe { *self.hashes().add(src_index) };
            let child = unsafe {
                let child = std::mem::take(&mut *self.children().add(src_index));
                (!child.is_null()).then_some(child)
            };
            let effective_dst_index = if dst_dense { branch } else { dst_index };
            next.set_hash_at_index(effective_dst_index, hash);
            next.set_child_at_index(effective_dst_index, child);
        }

        *self = next;
    }
}

impl Drop for TaggedPointer {
    fn drop(&mut self) {
        if self.tagged == 0 {
            return;
        }
        let capacity = self.capacity();
        let ptr = self.ptr();
        let hashes = self.hashes();
        let children = self.children();
        unsafe {
            for index in 0..capacity {
                ptr::drop_in_place(hashes.add(index));
                ptr::drop_in_place(children.add(index));
            }
            dealloc(ptr.as_ptr(), tagged_arrays_layout(capacity));
        }
        self.tagged = 0;
    }
}

/// Inner-node-specific arrays. Only allocated for inner nodes.
#[derive(Debug)]
pub struct InnerNodeArrays {
    hashes_and_children: std::cell::UnsafeCell<TaggedPointer>,
    /// Packed spinlock for children — one bit per branch, matching reference
    /// `std::atomic<uint16_t> lock_` with `packed_spinlock`.
    /// fetch_or to acquire, fetch_and to release. No RwLock overhead.
    children_lock: AtomicU16,
}

impl InnerNodeArrays {
    fn new(num_allocated_children: usize) -> Self {
        Self {
            hashes_and_children: std::cell::UnsafeCell::new(TaggedPointer::new(
                num_allocated_children,
            )),
            children_lock: AtomicU16::new(0),
        }
    }

    pub fn children_lock(&self) -> &AtomicU16 {
        &self.children_lock
    }

    fn tagged(&self) -> &TaggedPointer {
        unsafe { &*self.hashes_and_children.get() }
    }

    #[allow(clippy::mut_from_ref)]
    fn tagged_mut(&self) -> &mut TaggedPointer {
        unsafe { &mut *self.hashes_and_children.get() }
    }
}

unsafe impl Sync for InnerNodeArrays {}
unsafe impl Send for InnerNodeArrays {}

#[derive(Debug)]
/// SHAMap tree node — matches reference SHAMapInnerNode / SHAMapLeafNode layout.
///
///   isBranch_      → plain u16, read without lock
///   fullBelowGen_  → plain u32, read without lock
///   getChildHash   → array read without lock
///   getChild       → packed_spinlock (1 bit per child)
///
/// We mirror this with atomic fields outside the RwLock for hot-path reads.
/// The RwLock only protects the children pointer array and leaf data.
///
pub struct SHAMapTreeNode {
    ref_counts: IntrusiveRefCounts,
    hash: std::cell::UnsafeCell<SHAMapHash>,
    cowid: AtomicU32,
    /// Lock-free branch occupancy bitfield (reference isBranch_).
    /// Updated atomically when branches change.
    is_branch: AtomicU16,
    /// Lock-free full-below generation (reference fullBelowGen_).
    full_below_gen: AtomicU32,
    /// Inner-node arrays (child hashes + child pointers + spinlock).
    /// None for leaf nodes — saves ~640 bytes per leaf (~9 GB for mainnet).
    inner_arrays: Option<Box<InnerNodeArrays>>,
    /// Leaf data + inner metadata behind RwLock.
    kind: RwLock<SHAMapTreeNodeKind>,
}

// Safety: child_hashes uses UnsafeCell for lock-free reads. Writes only happen
// under the kind write lock. The SHAMap is accessed from a single thread during
// sync scans. All other fields are already Sync (RwLock, Atomic).
unsafe impl Sync for SHAMapTreeNode {}
unsafe impl Send for SHAMapTreeNode {}

// SHAMap ownership is concrete: every handle points to the same enum-backed
// allocation type. Keep the hot pointer representations to one machine word,
// matching rippled's intrusive SHAMap pointers.
const _: () = {
    assert!(std::mem::size_of::<SharedIntrusive<SHAMapTreeNode>>() == std::mem::size_of::<usize>());
    assert!(
        std::mem::size_of::<basics::intrusive_pointer::WeakIntrusive<SHAMapTreeNode>>()
            == std::mem::size_of::<usize>()
    );
    assert!(
        std::mem::size_of::<basics::intrusive_pointer::SharedWeakUnion<SHAMapTreeNode>>()
            == std::mem::size_of::<usize>()
    );
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SHAMapCodecError {
    ShortPrefixNode,
    UnknownPrefixType(u32),
    UnknownWireType(u8),
    InvalidFullInnerSize(usize),
    InvalidCompressedInnerSize(usize),
    InvalidCompressedInnerBranch(u8),
    ShortLeafNode {
        node_type: SHAMapNodeType,
        len: usize,
    },
    ShortTransactionWithMetaNode(usize),
    ShortAccountStateNode(usize),
    InvalidAccountStateNode,
    EmptyInnerNodeSerialization,
}

impl SHAMapInnerNodeData {
    fn new() -> Self {
        Self {
            is_branch: 0,
            full_below_gen: 0,
        }
    }

    fn is_empty(&self) -> bool {
        self.is_branch == 0
    }

    fn is_empty_branch(&self, branch: usize) -> bool {
        (self.is_branch & (1 << branch)) == 0
    }

    fn branch_count(&self) -> usize {
        self.is_branch.count_ones() as usize
    }

    fn iter_non_empty_child_indexes<F>(&self, arrays: &InnerNodeArrays, f: F)
    where
        F: FnMut(usize, usize),
    {
        arrays
            .tagged()
            .iter_non_empty_child_indexes(self.is_branch, f);
    }
}

impl SHAMapTreeNode {
    pub fn new_inner(cowid: u32) -> Self {
        Self::new_inner_with_capacity(cowid, 0)
    }

    fn new_inner_with_capacity(cowid: u32, num_allocated_children: usize) -> Self {
        Self {
            ref_counts: IntrusiveRefCounts::new(),
            hash: std::cell::UnsafeCell::new(SHAMapHash::default()),
            cowid: AtomicU32::new(cowid),
            is_branch: AtomicU16::new(0),
            full_below_gen: AtomicU32::new(0),
            inner_arrays: Some(Box::new(InnerNodeArrays::new(num_allocated_children))),
            kind: RwLock::new(SHAMapTreeNodeKind::Inner(SHAMapInnerNodeData::new())),
        }
    }

    pub fn new_leaf(node_type: SHAMapNodeType, item: SHAMapItem, cowid: u32) -> Self {
        assert!(
            item.size() >= MIN_SHAMAP_ITEM_BYTES,
            "SHAMap leaf item payload below minimum size"
        );
        let hash = compute_leaf_hash(node_type, &item);
        Self::new_leaf_with_hash(node_type, item, cowid, hash)
    }

    pub fn new_leaf_with_hash(
        node_type: SHAMapNodeType,
        item: SHAMapItem,
        cowid: u32,
        hash: SHAMapHash,
    ) -> Self {
        assert!(
            item.size() >= MIN_SHAMAP_ITEM_BYTES,
            "SHAMap leaf item payload below minimum size"
        );
        Self {
            ref_counts: IntrusiveRefCounts::new(),
            hash: std::cell::UnsafeCell::new(hash),
            cowid: AtomicU32::new(cowid),
            is_branch: AtomicU16::new(0),
            full_below_gen: AtomicU32::new(0),
            inner_arrays: None,
            kind: RwLock::new(SHAMapTreeNodeKind::Leaf(SHAMapLeafNodeData {
                node_type,
                item,
            })),
        }
    }

    /// Access inner-node arrays. Panics if called on a leaf node.
    #[inline]
    fn arrays(&self) -> &InnerNodeArrays {
        self.inner_arrays
            .as_ref()
            .expect("inner_arrays accessed on a leaf node")
    }

    pub fn cowid(&self) -> u32 {
        self.cowid.load(Ordering::Acquire)
    }

    pub fn unshare(&self) {
        self.cowid.store(0, Ordering::Release);
    }

    pub fn get_hash(&self) -> SHAMapHash {
        unsafe { *self.hash.get() }
    }

    pub fn set_hash(&self, hash: SHAMapHash) {
        unsafe {
            *self.hash.get() = hash;
        }
    }

    pub fn zero_hash(&self) {
        self.set_hash(SHAMapHash::default());
    }

    pub fn get_type(&self) -> SHAMapNodeType {
        // OPTIMIZATION: the Inner arm never needs the lock — inner_arrays
        // is Some for every inner node and None for every leaf, set once at
        // construction and never mutated thereafter.  Only leaf nodes must enter
        // the lock to read the concrete SHAMapNodeType variant.
        // Not present in rippled which uses a virtual dispatch / type tag instead.
        if self.inner_arrays.is_some() {
            return SHAMapNodeType::Inner;
        }
        let kind = self.kind.read();
        match &*kind {
            SHAMapTreeNodeKind::Leaf(leaf) => leaf.node_type,
            // inner_arrays.is_some() already handled above; this branch is
            // unreachable in practice but keeps the match exhaustive.
            SHAMapTreeNodeKind::Inner(_) => SHAMapNodeType::Inner,
        }
    }

    /// Returns `true` if this node is a leaf node.
    ///
    /// # Lock-free
    /// `inner_arrays` is `None` for every leaf and `Some` for every inner node.
    /// It is set once at construction (`new_leaf` / `new_inner_with_capacity`)
    /// and never changed afterward, so no lock is required.
    #[inline]
    pub fn is_leaf(&self) -> bool {
        self.inner_arrays.is_none()
    }

    /// Returns `true` if this node is an inner node.
    ///
    /// # Lock-free
    /// `inner_arrays` is `Some` for every inner node and `None` for every leaf.
    /// It is set once at construction (`new_inner_with_capacity`) and never
    /// changed afterward, so no lock is required.
    ///
    /// # Note: `peek_item_unchecked` not added
    /// A zero-copy `peek_item_unchecked()` that bypasses the `kind` RwLock
    /// entirely would require a raw `UnsafeCell<SHAMapLeafNodeData>` field,
    /// because `parking_lot::RwLock` does not expose a `data_ptr()` accessor.
    /// Restructuring the layout to enable that is left for a future phase.
    #[inline]
    pub fn is_inner(&self) -> bool {
        self.inner_arrays.is_some()
    }

    pub fn clone_with_cowid(&self, cowid: u32) -> SharedIntrusive<Self> {
        let hash = self.get_hash();
        let cloned = {
            let kind = self.kind.read();
            match &*kind {
                SHAMapTreeNodeKind::Inner(inner) => {
                    let cloned =
                        SHAMapTreeNode::new_inner_with_capacity(cowid, inner.branch_count());
                    cloned.set_hash(hash);
                    // Copy lock-free fields
                    cloned.is_branch.store(inner.is_branch, Ordering::Relaxed);
                    cloned.full_below_gen.store(
                        self.full_below_gen.load(Ordering::Relaxed),
                        Ordering::Relaxed,
                    );
                    cloned
                        .arrays()
                        .tagged_mut()
                        .resize(inner.is_branch, inner.branch_count());
                    inner.iter_non_empty_child_indexes(self.arrays(), |branch, index| {
                        let hash = self.arrays().tagged().get_hash(inner.is_branch, branch);
                        cloned.arrays().tagged().set_hash_at_index(index, hash);
                    });
                    {
                        let mut cloned_kind = cloned.kind.write();
                        if let SHAMapTreeNodeKind::Inner(cloned_inner) = &mut *cloned_kind {
                            cloned_inner.is_branch = inner.is_branch;
                            cloned_inner.full_below_gen = inner.full_below_gen;
                        }
                    }
                    inner.iter_non_empty_child_indexes(self.arrays(), |branch, index| {
                        if let Some(child) = self.get_child(branch) {
                            cloned
                                .arrays()
                                .tagged()
                                .set_child_at_index(index, Some(child));
                        }
                    });
                    cloned
                }
                SHAMapTreeNodeKind::Leaf(leaf) => SHAMapTreeNode::new_leaf_with_hash(
                    leaf.node_type,
                    leaf.item.clone(),
                    cowid,
                    hash,
                ),
            }
        };

        make_shared_intrusive(cloned)
    }

    pub fn is_empty(&self) -> bool {
        let kind = self.kind.read();
        match &*kind {
            SHAMapTreeNodeKind::Inner(inner) => inner.is_empty(),
            SHAMapTreeNodeKind::Leaf(_) => false,
        }
    }

    /// Lock-free branch check — matches reference isEmptyBranch (plain bitfield read).
    pub fn is_empty_branch(&self, branch: usize) -> bool {
        validate_branch(branch);
        (self.is_branch.load(Ordering::Relaxed) & (1 << branch)) == 0
    }

    /// Lock-free branch count — matches reference getBranchCount.
    pub fn branch_count(&self) -> usize {
        self.is_branch.load(Ordering::Relaxed).count_ones() as usize
    }

    /// Lock-free child hash read — matches reference getChildHash (no lock).
    #[inline(always)]
    pub fn get_child_hash(&self, branch: usize) -> SHAMapHash {
        validate_branch(branch);
        let is_branch = self.is_branch.load(Ordering::Relaxed);
        self.arrays().tagged().get_hash(is_branch, branch)
    }

    pub fn set_child_hash(&self, branch: usize, hash: SHAMapHash) {
        validate_branch(branch);
        let arrays = self.inner_arrays.as_ref().unwrap();
        let mut kind = self.kind.write();
        if let SHAMapTreeNodeKind::Inner(inner) = &mut *kind {
            let src_branches = inner.is_branch;
            let dst_branches = if hash.is_non_zero() {
                src_branches | (1 << branch)
            } else {
                src_branches & !(1 << branch)
            };
            arrays.tagged_mut().rebuild(
                src_branches,
                dst_branches,
                dst_branches.count_ones() as usize,
            );
            inner.is_branch = dst_branches;
            self.is_branch.store(dst_branches, Ordering::Relaxed);
            if hash.is_non_zero() {
                let index = arrays
                    .tagged()
                    .child_index(inner.is_branch, branch)
                    .expect("non-zero hash branch must be allocated");
                arrays.tagged().set_hash_at_index(index, hash);
            }
        }
    }

    pub fn set_child(&self, branch: usize, child: Option<SharedIntrusive<SHAMapTreeNode>>) {
        validate_branch(branch);
        assert!(
            self.cowid() != 0,
            "owned inner nodes must have a non-zero cowid"
        );
        let arrays = self.inner_arrays.as_ref().unwrap();
        let mut kind = self.kind.write();
        let SHAMapTreeNodeKind::Inner(inner) = &mut *kind else {
            return;
        };

        let src_branches = inner.is_branch;
        if let Some(ref child) = child {
            let dst_branches = src_branches | (1 << branch);
            arrays.tagged_mut().rebuild(
                src_branches,
                dst_branches,
                dst_branches.count_ones() as usize,
            );
            inner.is_branch = dst_branches;
            self.is_branch.store(dst_branches, Ordering::Relaxed);
            let index = arrays
                .tagged()
                .child_index(inner.is_branch, branch)
                .expect("child branch must be allocated");
            arrays
                .tagged()
                .set_hash_at_index(index, SHAMapHash::default());
            arrays
                .tagged()
                .set_child_at_index(index, Some(child.clone()));
        } else {
            let dst_branches = src_branches & !(1 << branch);
            arrays.tagged_mut().rebuild(
                src_branches,
                dst_branches,
                dst_branches.count_ones() as usize,
            );
            inner.is_branch = dst_branches;
            self.is_branch.store(dst_branches, Ordering::Relaxed);
        }

        drop(kind);
        self.zero_hash();
    }

    pub fn share_child(&self, branch: usize, child: &SharedIntrusive<SHAMapTreeNode>) {
        validate_branch(branch);
        assert!(
            self.cowid() != 0,
            "owned inner nodes must have a non-zero cowid"
        );
        assert!(!self.is_empty_branch(branch), "branch must already exist");
        let is_branch = self.is_branch.load(Ordering::Relaxed);
        let index = self
            .arrays()
            .tagged()
            .child_index(is_branch, branch)
            .expect("non-empty branch must have a child index");
        self.arrays()
            .tagged()
            .set_child_at_index(index, Some(child.clone()));
    }

    /// Per-branch child read — matches reference getChild (packed_spinlock per child).
    pub fn get_child(&self, branch: usize) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        validate_branch(branch);
        let is_branch = self.is_branch.load(Ordering::Relaxed);
        let index = self.arrays().tagged().child_index(is_branch, branch)?;
        let mask = 1u16 << index;
        // Acquire spinlock for this branch
        loop {
            if self
                .arrays()
                .children_lock()
                .fetch_or(mask, Ordering::Acquire)
                & mask
                == 0
            {
                break;
            }
            while self.arrays().children_lock().load(Ordering::Relaxed) & mask != 0 {
                std::hint::spin_loop();
            }
        }
        let result = self.arrays().tagged().get_child_at_index(index);
        self.arrays()
            .children_lock()
            .fetch_and(!mask, Ordering::Release);
        result
    }

    /// Evict all loaded children from this inner node, freeing their memory.
    ///
    /// The branch bitmap (`is_branch`) and branch hashes are preserved — only
    /// the loaded child pointers are set to `None`. After this call:
    /// - `is_empty_branch(b)` returns the same value as before (topology intact)
    /// - `get_child_hash(b)` returns the same hash as before (identity intact)
    /// - `get_child(b)` returns `None` for all branches (data evicted)
    ///
    /// This enables the backed-fetch path (`descend()` in SHAMap traversal) to
    /// re-load individual nodes from NuDB on demand — the standard lazy-load
    /// mechanism that already handles `None` children on backed trees.
    ///
    /// Thread-safety: uses the existing per-branch spinlock (`children_lock`)
    /// identically to `get_child` / `canonicalize_child`. Concurrent readers
    /// will either see the child (before eviction of that slot) or None (after),
    /// both of which are valid states for a backed tree.
    ///
    /// Does NOT require `cowid != 0` — this is a memory-management operation,
    /// not a tree mutation. The tree's logical content is unchanged.
    pub fn release_loaded_children(&self) {
        let Some(arrays) = self.inner_arrays.as_ref() else {
            return; // Leaf node — nothing to release.
        };

        let is_branch = self.is_branch.load(Ordering::Relaxed);
        if is_branch == 0 {
            return; // No branches — nothing loaded.
        }

        let tagged = arrays.tagged();
        let num_children = is_branch.count_ones() as usize;

        // Iterate over all compact indices that correspond to non-empty branches.
        // Each index is locked independently via the per-branch spinlock.
        for index in 0..num_children {
            let mask = 1u16 << index;

            // Acquire spinlock for this slot
            loop {
                if arrays.children_lock().fetch_or(mask, Ordering::Acquire) & mask == 0 {
                    break;
                }
                while arrays.children_lock().load(Ordering::Relaxed) & mask != 0 {
                    std::hint::spin_loop();
                }
            }

            // Drop the child pointer (the hash at this index is untouched)
            tagged.set_child_at_index(index, None);

            // Release spinlock
            arrays.children_lock().fetch_and(!mask, Ordering::Release);
        }
    }

    /// Raw pointer child access — no ref counting, no clone.
    /// Safety: caller must ensure the parent outlives the returned pointer.
    #[inline(always)]
    /// # Safety
    /// Caller must ensure the returned pointer is not dereferenced after the node is dropped.
    pub unsafe fn get_child_ptr(&self, branch: usize) -> Option<*const SHAMapTreeNode> {
        let is_branch = self.is_branch.load(Ordering::Relaxed);
        let index = self.arrays().tagged().child_index(is_branch, branch)?;
        let mask = 1u16 << index;
        loop {
            if self
                .arrays()
                .children_lock()
                .fetch_or(mask, Ordering::Acquire)
                & mask
                == 0
            {
                break;
            }
            while self.arrays().children_lock().load(Ordering::Relaxed) & mask != 0 {
                std::hint::spin_loop();
            }
        }
        let result = unsafe { self.arrays().tagged().get_child_ptr_at_index(index) };
        self.arrays()
            .children_lock()
            .fetch_and(!mask, Ordering::Release);
        result
    }

    /// Check if a child is loaded without cloning.
    #[inline(always)]
    pub fn has_child(&self, branch: usize) -> bool {
        validate_branch(branch);
        let is_branch = self.is_branch.load(Ordering::Relaxed);
        let Some(index) = self.arrays().tagged().child_index(is_branch, branch) else {
            return false;
        };
        let mask = 1u16 << index;
        loop {
            if self
                .arrays()
                .children_lock()
                .fetch_or(mask, Ordering::Acquire)
                & mask
                == 0
            {
                break;
            }
            while self.arrays().children_lock().load(Ordering::Relaxed) & mask != 0 {
                std::hint::spin_loop();
            }
        }
        let result = self.arrays().tagged().has_child_at_index(index);
        self.arrays()
            .children_lock()
            .fetch_and(!mask, Ordering::Release);
        result
    }

    /// Returns true if any non-empty branch has a loaded child pointer.
    /// Used to avoid unnecessary release_loaded_children calls on nodes
    /// that already have all children released.
    pub fn has_any_loaded_child(&self) -> bool {
        let Some(arrays) = self.inner_arrays.as_ref() else {
            return false;
        };
        let is_branch = self.is_branch.load(Ordering::Relaxed);
        if is_branch == 0 {
            return false;
        }
        let tagged = arrays.tagged();
        let num_children = is_branch.count_ones() as usize;
        for index in 0..num_children {
            if tagged.has_child_at_index(index) {
                return true;
            }
        }
        false
    }

    pub fn canonicalize_child(
        &self,
        branch: usize,
        node: SharedIntrusive<SHAMapTreeNode>,
    ) -> SharedIntrusive<SHAMapTreeNode> {
        validate_branch(branch);
        let node_hash = node.get_hash();
        let stored_hash = self.get_child_hash(branch);
        assert!(!self.is_empty_branch(branch), "branch must already exist");
        assert_eq!(
            node_hash, stored_hash,
            "canonicalized node hash must match the stored branch hash"
        );

        let is_branch = self.is_branch.load(Ordering::Relaxed);
        let index = self
            .arrays()
            .tagged()
            .child_index(is_branch, branch)
            .expect("non-empty branch must have a child index");
        let mask = 1u16 << index;
        loop {
            if self
                .arrays()
                .children_lock()
                .fetch_or(mask, Ordering::Acquire)
                & mask
                == 0
            {
                break;
            }
            while self.arrays().children_lock().load(Ordering::Relaxed) & mask != 0 {
                std::hint::spin_loop();
            }
        }
        let existing = self.arrays().tagged().get_child_at_index(index);
        let result = if let Some(existing) = existing {
            existing.clone()
        } else {
            self.arrays()
                .tagged()
                .set_child_at_index(index, Some(node.clone()));
            // Also update inner data for serialization paths
            node
        };
        self.arrays()
            .children_lock()
            .fetch_and(!mask, Ordering::Release);
        result
    }

    /// Lock-free full-below check — matches reference isFullBelow (plain field read).
    pub fn is_full_below(&self, generation: u32) -> bool {
        self.full_below_gen.load(Ordering::Relaxed) == generation
    }

    /// Lock-free full-below set — matches reference setFullBelowGen.
    pub fn set_full_below_gen(&self, generation: u32) {
        self.full_below_gen.store(generation, Ordering::Relaxed);
    }

    pub fn peek_item(&self) -> Option<SHAMapItem> {
        let kind = self.kind.read();
        match &*kind {
            SHAMapTreeNodeKind::Leaf(leaf) => Some(leaf.item.clone()),
            SHAMapTreeNodeKind::Inner(_) => None,
        }
    }

    pub fn set_item(&self, item: SHAMapItem) -> bool {
        assert!(
            self.cowid() != 0,
            "owned leaf nodes must have a non-zero cowid"
        );

        let old_hash = self.get_hash();
        let new_hash = {
            let mut kind = self.kind.write();
            let SHAMapTreeNodeKind::Leaf(leaf) = &mut *kind else {
                panic!("set_item is only valid for leaf nodes");
            };
            leaf.item = item;
            compute_leaf_hash(leaf.node_type, &leaf.item)
        };

        self.set_hash(new_hash);
        old_hash != new_hash
    }

    pub fn update_hash(&self) {
        let next_hash = {
            let kind = self.kind.read();
            match &*kind {
                SHAMapTreeNodeKind::Inner(inner) => compute_inner_hash(inner, self.arrays()),
                SHAMapTreeNodeKind::Leaf(leaf) => compute_leaf_hash(leaf.node_type, &leaf.item),
            }
        };

        self.set_hash(next_hash);
    }

    pub fn update_hash_deep(&self) {
        let next_hash = {
            let mut kind = self.kind.write();
            let SHAMapTreeNodeKind::Inner(inner) = &mut *kind else {
                panic!("update_hash_deep is only valid for inner nodes");
            };

            for branch in 0..BRANCH_FACTOR {
                if inner.is_empty_branch(branch) {
                    continue;
                }

                let index = self
                    .arrays()
                    .tagged()
                    .child_index(inner.is_branch, branch)
                    .expect("non-empty branch must have a child index");
                if let Some(child) = self.arrays().tagged().get_child_at_index(index) {
                    let h = child.get_hash();
                    self.arrays().tagged().set_hash_at_index(index, h);
                }
            }

            compute_inner_hash(inner, self.arrays())
        };

        self.set_hash(next_hash);
    }

    pub fn serialize_for_wire(&self) -> Result<Vec<u8>, SHAMapCodecError> {
        let kind = self.kind.read();
        match &*kind {
            SHAMapTreeNodeKind::Leaf(leaf) => Ok(serialize_leaf_for_wire(leaf)),
            SHAMapTreeNodeKind::Inner(inner) => serialize_inner_for_wire(inner, self.arrays()),
        }
    }

    pub fn serialize_with_prefix(&self) -> Result<Vec<u8>, SHAMapCodecError> {
        let kind = self.kind.read();
        match &*kind {
            SHAMapTreeNodeKind::Leaf(leaf) => Ok(serialize_leaf_with_prefix(leaf)),
            SHAMapTreeNodeKind::Inner(inner) => serialize_inner_with_prefix(inner, self.arrays()),
        }
    }

    pub fn make_from_wire(
        raw_node: &[u8],
    ) -> Result<Option<SharedIntrusive<SHAMapTreeNode>>, SHAMapCodecError> {
        let Some((&node_type, payload)) = raw_node.split_last() else {
            return Ok(None);
        };

        let node = match node_type {
            WIRE_TYPE_TRANSACTION => make_transaction_node(payload, None)?,
            WIRE_TYPE_ACCOUNT_STATE => make_account_state_node(payload, None)?,
            WIRE_TYPE_INNER => make_full_inner(payload, None)?,
            WIRE_TYPE_COMPRESSED_INNER => make_compressed_inner(payload)?,
            WIRE_TYPE_TRANSACTION_WITH_META => make_transaction_with_meta_node(payload, None)?,
            other => {
                tracing::warn!(
                    target: "shamap",
                    wire_type = other,
                    wire_bytes = raw_node.len(),
                    "Failed to decode wire node"
                );
                return Err(SHAMapCodecError::UnknownWireType(other));
            }
        };

        Ok(Some(node))
    }

    pub fn make_from_prefix(
        raw_node: &[u8],
        hash: SHAMapHash,
    ) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
        if raw_node.len() < u32::BITS as usize / 8 {
            tracing::warn!(target: "shamap", "Failed to decode prefix node");
            return Err(SHAMapCodecError::ShortPrefixNode);
        }

        let (prefix_bytes, payload) = raw_node.split_at(4);
        let prefix = u32::from_be_bytes(
            prefix_bytes
                .try_into()
                .expect("prefix split must yield exactly four bytes"),
        );

        match prefix {
            HASH_PREFIX_TRANSACTION_ID => make_transaction_node(payload, Some(hash)),
            HASH_PREFIX_LEAF_NODE => make_account_state_node(payload, Some(hash)),
            HASH_PREFIX_INNER_NODE => make_full_inner(payload, Some(hash)),
            HASH_PREFIX_TX_NODE => make_transaction_with_meta_node(payload, Some(hash)),
            other => {
                tracing::warn!(target: "shamap", "Failed to decode prefix node");
                Err(SHAMapCodecError::UnknownPrefixType(other))
            }
        }
    }
}

unsafe impl IntrusiveObject for SHAMapTreeNode {
    type Owner = CompactIntrusiveOwner;

    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
        &self.ref_counts
    }

    fn partial_destructor(&self) {
        // OPTIMIZATION: use the lock-free inner_arrays presence check instead of
        // acquiring the kind RwLock just to distinguish node type.
        // inner_arrays is set once at construction and is immutable thereafter,
        // so reading it without a lock is safe.
        if self.inner_arrays.is_some() {
            let is_branch = self.is_branch.load(Ordering::Relaxed);
            let arrays = self.arrays();
            arrays
                .tagged()
                .iter_non_empty_child_indexes(is_branch, |_, index| {
                    arrays.tagged().set_child_at_index(index, None);
                });
        }
    }
}

fn validate_branch(branch: usize) {
    assert!(branch < BRANCH_FACTOR, "branch must be within 0..16");
}

fn capacity_for_children(num_children: usize) -> usize {
    TAGGED_POINTER_BOUNDARIES
        .iter()
        .copied()
        .find(|capacity| num_children <= *capacity)
        .expect("SHAMap inner nodes cannot have more than 16 children")
}

fn boundary_index(num_children: usize) -> usize {
    TAGGED_POINTER_BOUNDARIES
        .iter()
        .position(|capacity| num_children <= *capacity)
        .expect("SHAMap inner nodes cannot have more than 16 children")
}

fn tagged_arrays_layout(capacity: usize) -> Layout {
    let hashes = Layout::array::<SHAMapHash>(capacity).expect("valid hash array layout");
    let children = Layout::array::<SharedIntrusive<SHAMapTreeNode>>(capacity)
        .expect("valid child array layout");
    let (layout, _) = hashes
        .extend(children)
        .expect("valid tagged pointer layout");
    layout.pad_to_align()
}

fn child_offset(capacity: usize) -> usize {
    let hashes = Layout::array::<SHAMapHash>(capacity).expect("valid hash array layout");
    let children = Layout::array::<SharedIntrusive<SHAMapTreeNode>>(capacity)
        .expect("valid child array layout");
    let (_, offset) = hashes
        .extend(children)
        .expect("valid tagged pointer layout");
    offset
}

fn allocate_tagged_arrays(capacity: usize) -> (NonNull<u8>, Layout) {
    let layout = tagged_arrays_layout(capacity);
    let raw = unsafe { alloc(layout) };
    let Some(ptr) = NonNull::new(raw) else {
        handle_alloc_error(layout);
    };
    (ptr, layout)
}

fn children_ptr(ptr: NonNull<u8>, capacity: usize) -> *mut SharedIntrusive<SHAMapTreeNode> {
    unsafe { ptr.as_ptr().add(child_offset(capacity)).cast() }
}

fn serialize_leaf_for_wire(leaf: &SHAMapLeafNodeData) -> Vec<u8> {
    let wire_type = match leaf.node_type {
        SHAMapNodeType::Inner => panic!("inner nodes are not serialized as leaves"),
        SHAMapNodeType::TransactionNm => WIRE_TYPE_TRANSACTION,
        SHAMapNodeType::TransactionMd => WIRE_TYPE_TRANSACTION_WITH_META,
        SHAMapNodeType::AccountState => WIRE_TYPE_ACCOUNT_STATE,
    };

    let mut bytes = Vec::with_capacity(leaf.item.size() + Uint256::BYTES + 1);
    bytes.extend_from_slice(leaf.item.data());
    if !matches!(leaf.node_type, SHAMapNodeType::TransactionNm) {
        bytes.extend_from_slice(leaf.item.key().data());
    }
    bytes.push(wire_type);
    bytes
}

fn serialize_leaf_with_prefix(leaf: &SHAMapLeafNodeData) -> Vec<u8> {
    let prefix = match leaf.node_type {
        SHAMapNodeType::Inner => panic!("inner nodes are not serialized as leaves"),
        SHAMapNodeType::TransactionNm => HASH_PREFIX_TRANSACTION_ID,
        SHAMapNodeType::TransactionMd => HASH_PREFIX_TX_NODE,
        SHAMapNodeType::AccountState => HASH_PREFIX_LEAF_NODE,
    };

    let mut bytes = Vec::with_capacity(4 + leaf.item.size() + Uint256::BYTES);
    bytes.extend_from_slice(&prefix.to_be_bytes());
    bytes.extend_from_slice(leaf.item.data());
    if !matches!(leaf.node_type, SHAMapNodeType::TransactionNm) {
        bytes.extend_from_slice(leaf.item.key().data());
    }
    bytes
}

fn serialize_inner_for_wire(
    inner: &SHAMapInnerNodeData,
    arrays: &InnerNodeArrays,
) -> Result<Vec<u8>, SHAMapCodecError> {
    if inner.is_empty() {
        return Err(SHAMapCodecError::EmptyInnerNodeSerialization);
    }

    if inner.branch_count() < 12 {
        let mut bytes = Vec::with_capacity(inner.branch_count() * (Uint256::BYTES + 1) + 1);
        for branch in 0..BRANCH_FACTOR {
            if inner.is_empty_branch(branch) {
                continue;
            }
            let hash = arrays.tagged().get_hash(inner.is_branch, branch);
            bytes.extend_from_slice(hash.as_uint256().data());
            bytes.push(branch as u8);
        }
        bytes.push(WIRE_TYPE_COMPRESSED_INNER);
        Ok(bytes)
    } else {
        let mut bytes = Vec::with_capacity(BRANCH_FACTOR * Uint256::BYTES + 1);
        for i in 0..BRANCH_FACTOR {
            let hash = arrays.tagged().get_hash(inner.is_branch, i);
            bytes.extend_from_slice(hash.as_uint256().data());
        }
        bytes.push(WIRE_TYPE_INNER);
        Ok(bytes)
    }
}

fn serialize_inner_with_prefix(
    inner: &SHAMapInnerNodeData,
    arrays: &InnerNodeArrays,
) -> Result<Vec<u8>, SHAMapCodecError> {
    if inner.is_empty() {
        return Err(SHAMapCodecError::EmptyInnerNodeSerialization);
    }

    let mut bytes = Vec::with_capacity(4 + BRANCH_FACTOR * Uint256::BYTES);
    bytes.extend_from_slice(&HASH_PREFIX_INNER_NODE.to_be_bytes());
    for i in 0..BRANCH_FACTOR {
        let hash = arrays.tagged().get_hash(inner.is_branch, i);
        bytes.extend_from_slice(hash.as_uint256().data());
    }
    Ok(bytes)
}

fn make_transaction_node(
    data: &[u8],
    known_hash: Option<SHAMapHash>,
) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
    validate_leaf_payload(SHAMapNodeType::TransactionNm, data)?;
    let key = sha512_half_bytes(HASH_PREFIX_TRANSACTION_ID, [data]);
    let item = SHAMapItem::new(key, data.to_vec());
    Ok(make_shared_intrusive(match known_hash {
        Some(hash) => {
            SHAMapTreeNode::new_leaf_with_hash(SHAMapNodeType::TransactionNm, item, 0, hash)
        }
        None => SHAMapTreeNode::new_leaf(SHAMapNodeType::TransactionNm, item, 0),
    }))
}

fn make_transaction_with_meta_node(
    data: &[u8],
    known_hash: Option<SHAMapHash>,
) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
    if data.len() < Uint256::BYTES {
        return Err(SHAMapCodecError::ShortTransactionWithMetaNode(data.len()));
    }

    let split = data.len() - Uint256::BYTES;
    let (payload, tag_bytes) = data.split_at(split);
    validate_leaf_payload(SHAMapNodeType::TransactionMd, payload)?;
    let tag = Uint256::from_slice(tag_bytes).expect("slice length should already be validated");
    let item = SHAMapItem::new(tag, payload.to_vec());

    Ok(make_shared_intrusive(match known_hash {
        Some(hash) => {
            SHAMapTreeNode::new_leaf_with_hash(SHAMapNodeType::TransactionMd, item, 0, hash)
        }
        None => SHAMapTreeNode::new_leaf(SHAMapNodeType::TransactionMd, item, 0),
    }))
}

fn make_account_state_node(
    data: &[u8],
    known_hash: Option<SHAMapHash>,
) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
    if data.len() < Uint256::BYTES {
        return Err(SHAMapCodecError::ShortAccountStateNode(data.len()));
    }

    let split = data.len() - Uint256::BYTES;
    let (payload, tag_bytes) = data.split_at(split);
    validate_leaf_payload(SHAMapNodeType::AccountState, payload)?;
    let tag = Uint256::from_slice(tag_bytes).expect("slice length should already be validated");
    if tag.is_zero() {
        return Err(SHAMapCodecError::InvalidAccountStateNode);
    }

    let item = SHAMapItem::new(tag, payload.to_vec());
    Ok(make_shared_intrusive(match known_hash {
        Some(hash) => {
            SHAMapTreeNode::new_leaf_with_hash(SHAMapNodeType::AccountState, item, 0, hash)
        }
        None => SHAMapTreeNode::new_leaf(SHAMapNodeType::AccountState, item, 0),
    }))
}

fn validate_leaf_payload(node_type: SHAMapNodeType, data: &[u8]) -> Result<(), SHAMapCodecError> {
    if data.len() < MIN_SHAMAP_ITEM_BYTES {
        return Err(SHAMapCodecError::ShortLeafNode {
            node_type,
            len: data.len(),
        });
    }
    Ok(())
}

fn make_full_inner(
    data: &[u8],
    known_hash: Option<SHAMapHash>,
) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
    if data.len() != BRANCH_FACTOR * Uint256::BYTES {
        return Err(SHAMapCodecError::InvalidFullInnerSize(data.len()));
    }

    let node = make_shared_intrusive(SHAMapTreeNode::new_inner_with_capacity(0, BRANCH_FACTOR));
    {
        let mut kind = node.kind.write();
        let SHAMapTreeNodeKind::Inner(inner) = &mut *kind else {
            unreachable!("new_inner must create an inner node");
        };

        for (branch, chunk) in data.chunks_exact(Uint256::BYTES).enumerate() {
            let hash = SHAMapHash::new(
                Uint256::from_slice(chunk).expect("chunk length should match uint256"),
            );
            node.arrays().tagged().set_hash_at_index(branch, hash);
            if hash.is_non_zero() {
                inner.is_branch |= 1 << branch;
            }
        }
        node.arrays()
            .tagged_mut()
            .resize(inner.is_branch, inner.branch_count());
        node.is_branch.store(inner.is_branch, Ordering::Relaxed);
    }

    if let Some(hash) = known_hash {
        node.set_hash(hash);
    } else {
        node.update_hash();
    }

    Ok(node)
}

fn make_compressed_inner(data: &[u8]) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
    let chunk_size = Uint256::BYTES + 1;
    if !data.len().is_multiple_of(chunk_size) || data.len() > chunk_size * BRANCH_FACTOR {
        return Err(SHAMapCodecError::InvalidCompressedInnerSize(data.len()));
    }

    let node = make_shared_intrusive(SHAMapTreeNode::new_inner_with_capacity(0, BRANCH_FACTOR));
    {
        let mut kind = node.kind.write();
        let SHAMapTreeNodeKind::Inner(inner) = &mut *kind else {
            unreachable!("new_inner must create an inner node");
        };

        for chunk in data.chunks_exact(chunk_size) {
            let (hash_bytes, position_bytes) = chunk.split_at(Uint256::BYTES);
            let position = position_bytes[0];
            if position as usize >= BRANCH_FACTOR {
                return Err(SHAMapCodecError::InvalidCompressedInnerBranch(position));
            }

            let hash = SHAMapHash::new(
                Uint256::from_slice(hash_bytes).expect("chunk length should match uint256"),
            );
            node.arrays()
                .tagged()
                .set_hash_at_index(position as usize, hash);
            if hash.is_non_zero() {
                inner.is_branch |= 1 << position;
            }
        }
        node.arrays()
            .tagged_mut()
            .resize(inner.is_branch, inner.branch_count());
        node.is_branch.store(inner.is_branch, Ordering::Relaxed);
    }

    node.update_hash();
    Ok(node)
}

fn compute_inner_hash(inner: &SHAMapInnerNodeData, arrays: &InnerNodeArrays) -> SHAMapHash {
    if inner.is_branch == 0 {
        return SHAMapHash::default();
    }

    let mut hasher = Sha512::new();
    hasher.update(HASH_PREFIX_INNER_NODE.to_be_bytes());
    arrays.tagged().iter_children(inner.is_branch, |_, hash| {
        hasher.update(hash.as_uint256().data());
    });
    let digest = hasher.finalize();
    let mut out = [0_u8; Uint256::BYTES];
    out.copy_from_slice(&digest[..Uint256::BYTES]);
    SHAMapHash::new(Uint256::from_array(out))
}

fn compute_leaf_hash(node_type: SHAMapNodeType, item: &SHAMapItem) -> SHAMapHash {
    let prefix = match node_type {
        SHAMapNodeType::Inner => panic!("inner nodes do not have leaf hashes"),
        SHAMapNodeType::TransactionNm => HASH_PREFIX_TRANSACTION_ID,
        SHAMapNodeType::TransactionMd => HASH_PREFIX_TX_NODE,
        SHAMapNodeType::AccountState => HASH_PREFIX_LEAF_NODE,
    };
    let hash = if matches!(node_type, SHAMapNodeType::TransactionNm) {
        sha512_half_bytes(prefix, [item.data()])
    } else {
        sha512_half_bytes(prefix, [item.data(), item.key().data()])
    };

    SHAMapHash::new(hash)
}

fn sha512_half_bytes<I, T>(prefix: u32, parts: I) -> Uint256
where
    I: IntoIterator<Item = T>,
    T: AsRef<[u8]>,
{
    let mut hasher = Sha512::new();
    hasher.update(prefix.to_be_bytes());
    for part in parts {
        hasher.update(part.as_ref());
    }

    let digest = hasher.finalize();
    let mut bytes = [0u8; Uint256::BYTES];
    bytes.copy_from_slice(&digest[..Uint256::BYTES]);
    Uint256::from_array(bytes)
}

#[cfg(test)]
mod tests {
    use super::{
        BRANCH_FACTOR, HASH_PREFIX_INNER_NODE, HASH_PREFIX_LEAF_NODE, HASH_PREFIX_TX_NODE,
        SHAMapCodecError, SHAMapItem, SHAMapNodeType, SHAMapTreeNode, SHAMapTreeNodeKind,
        TaggedPointer, WIRE_TYPE_ACCOUNT_STATE, WIRE_TYPE_COMPRESSED_INNER, WIRE_TYPE_INNER,
        tagged_arrays_layout,
    };
    use basics::base_uint::Uint256;
    use basics::intrusive_pointer::{IntrusiveObject, make_shared_intrusive};
    use basics::sha_map_hash::SHAMapHash;
    use std::sync::atomic::Ordering;

    fn sample_uint256(fill: u8) -> Uint256 {
        Uint256::from_array([fill; 32])
    }

    fn sample_hash(fill: u8) -> SHAMapHash {
        SHAMapHash::new(sample_uint256(fill))
    }

    fn same_node(
        left: &basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>,
        right: &basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>,
    ) -> bool {
        std::ptr::eq(&**left, &**right)
    }

    #[test]
    fn tagged_pointer_capacity_tags_match_cpp_boundaries() {
        for children in 0..=2 {
            let tagged = TaggedPointer::new(children);
            assert_eq!(tagged.tag(), 0);
            assert_eq!(tagged.capacity(), 2);
            assert!(!tagged.is_dense());
        }
        for children in 3..=4 {
            let tagged = TaggedPointer::new(children);
            assert_eq!(tagged.tag(), 1);
            assert_eq!(tagged.capacity(), 4);
            assert!(!tagged.is_dense());
        }
        for children in 5..=6 {
            let tagged = TaggedPointer::new(children);
            assert_eq!(tagged.tag(), 2);
            assert_eq!(tagged.capacity(), 6);
            assert!(!tagged.is_dense());
        }
        for children in 7..=BRANCH_FACTOR {
            let tagged = TaggedPointer::new(children);
            assert_eq!(tagged.tag(), 3);
            assert_eq!(tagged.capacity(), BRANCH_FACTOR);
            assert!(tagged.is_dense());
        }
    }

    #[test]
    fn tagged_pointer_child_index_matches_sparse_popcount_and_dense_identity() {
        let sparse = TaggedPointer::new(3);
        let branches = (1 << 1) | (1 << 5) | (1 << 9);
        assert_eq!(sparse.child_index(branches, 0), None);
        assert_eq!(sparse.child_index(branches, 1), Some(0));
        assert_eq!(sparse.child_index(branches, 5), Some(1));
        assert_eq!(sparse.child_index(branches, 9), Some(2));
        assert_eq!(sparse.child_index(branches, 15), None);

        let dense = TaggedPointer::new(BRANCH_FACTOR);
        assert_eq!(dense.child_index(0, 0), Some(0));
        assert_eq!(dense.child_index(0, 7), Some(7));
        assert_eq!(dense.child_index(0, 15), Some(15));
    }

    #[test]
    fn tagged_pointer_rebuild_preserves_hashes_and_loaded_children() {
        let mut tagged = TaggedPointer::new(2);
        let src_branches = (1 << 1) | (1 << 5);
        let branch_1_index = tagged
            .child_index(src_branches, 1)
            .expect("branch 1 should be present");
        let branch_5_index = tagged
            .child_index(src_branches, 5)
            .expect("branch 5 should be present");
        let child = make_shared_intrusive(SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(sample_uint256(5), vec![7; 12]),
            0,
            sample_hash(5),
        ));
        let child_weak = child.downgrade();

        tagged.set_hash_at_index(branch_1_index, sample_hash(1));
        tagged.set_hash_at_index(branch_5_index, sample_hash(5));
        tagged.set_child_at_index(branch_5_index, Some(child));
        assert!(!child_weak.expired());

        let dst_branches = src_branches | (1 << 3) | (1 << 12);
        tagged.rebuild(src_branches, dst_branches, 4);
        assert_eq!(tagged.capacity(), 4);
        assert_eq!(tagged.get_hash(dst_branches, 1), sample_hash(1));
        assert_eq!(tagged.get_hash(dst_branches, 3), SHAMapHash::default());
        assert_eq!(tagged.get_hash(dst_branches, 5), sample_hash(5));
        assert_eq!(tagged.get_hash(dst_branches, 12), SHAMapHash::default());
        let moved_index = tagged
            .child_index(dst_branches, 5)
            .expect("branch 5 should survive rebuild");
        assert!(tagged.has_child_at_index(moved_index));
        assert!(!child_weak.expired());

        let removed_branch_5 = dst_branches & !(1 << 5);
        tagged.rebuild(dst_branches, removed_branch_5, 3);
        assert_eq!(tagged.capacity(), 4);
        assert_eq!(tagged.child_index(removed_branch_5, 5), None);
        assert!(child_weak.expired());
        assert_eq!(tagged.get_hash(removed_branch_5, 1), sample_hash(1));
    }

    #[test]
    fn full_and_compressed_inner_decode_resize_to_cpp_capacity_classes() {
        let mut compressed = Vec::new();
        compressed.extend_from_slice(sample_hash(0x11).as_uint256().data());
        compressed.push(2);
        compressed.extend_from_slice(sample_hash(0x22).as_uint256().data());
        compressed.push(15);
        compressed.push(WIRE_TYPE_COMPRESSED_INNER);
        let compressed_node = SHAMapTreeNode::make_from_wire(&compressed)
            .expect("compressed inner should decode")
            .expect("compressed inner should return a node");
        assert_eq!(compressed_node.branch_count(), 2);
        assert_eq!(compressed_node.arrays().tagged().capacity(), 2);
        assert_eq!(compressed_node.get_child_hash(2), sample_hash(0x11));
        assert_eq!(compressed_node.get_child_hash(15), sample_hash(0x22));

        let mut full = vec![0_u8; BRANCH_FACTOR * Uint256::BYTES];
        for branch in [0_usize, 1, 3, 5, 7, 9, 11] {
            let start = branch * Uint256::BYTES;
            full[start..start + Uint256::BYTES]
                .copy_from_slice(sample_hash(branch as u8 + 1).as_uint256().data());
        }
        full.push(WIRE_TYPE_INNER);
        let full_node = SHAMapTreeNode::make_from_wire(&full)
            .expect("full inner should decode")
            .expect("full inner should return a node");
        assert_eq!(full_node.branch_count(), 7);
        assert_eq!(full_node.arrays().tagged().capacity(), BRANCH_FACTOR);
        assert_eq!(full_node.get_child_hash(11), sample_hash(12));
        assert_eq!(full_node.get_child_hash(12), SHAMapHash::default());
    }

    #[test]
    fn common_node_fields_match_cpp_roles() {
        let node = make_shared_intrusive(SHAMapTreeNode::new_inner(9));
        assert!(node.is_inner());
        assert!(!node.is_leaf());
        assert_eq!(node.get_type(), SHAMapNodeType::Inner);
        assert_eq!(node.cowid(), 9);
        node.unshare();
        assert_eq!(node.cowid(), 0);
        assert!(node.is_empty());
        assert_eq!(node.branch_count(), 0);
        assert_eq!(node.get_hash(), SHAMapHash::default());
        assert_eq!(BRANCH_FACTOR, 16);
    }

    #[test]
    fn inner_node_keeps_branch_occupancy_separate_from_child_hashes() {
        let parent = make_shared_intrusive(SHAMapTreeNode::new_inner(1));
        let child = make_shared_intrusive(SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(3), vec![1; 12]),
            0,
        ));

        parent.set_child(2, Some(child));
        assert!(!parent.is_empty_branch(2));
        assert_eq!(parent.get_child_hash(2), SHAMapHash::default());
        assert!(parent.get_child(2).is_some());

        parent.set_child_hash(2, sample_hash(7));
        assert_eq!(parent.get_child_hash(2), sample_hash(7));
        assert!(!parent.is_empty_branch(2));
    }

    #[test]
    fn inner_partial_destructor_clears_loaded_children_but_keeps_hashes() {
        let parent = make_shared_intrusive(SHAMapTreeNode::new_inner(1));
        let child = make_shared_intrusive(SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(sample_uint256(4), vec![2; 12]),
            0,
            sample_hash(5),
        ));
        let child_weak = child.downgrade();

        parent.set_child_hash(1, sample_hash(5));
        parent.share_child(1, &child);
        drop(child);
        assert!(!child_weak.expired());

        IntrusiveObject::partial_destructor(&*parent);

        assert!(child_weak.expired());
        assert_eq!(parent.get_child_hash(1), sample_hash(5));
        assert!(parent.get_child(1).is_none());
        assert!(!parent.is_empty_branch(1));
    }

    #[test]
    fn compact_pointer_and_tagged_array_layout_matches_reference_shape() {
        use basics::intrusive_pointer::{SharedIntrusive, SharedWeakUnion, WeakIntrusive};

        assert_eq!(std::mem::size_of::<SharedIntrusive<SHAMapTreeNode>>(), 8);
        assert_eq!(std::mem::size_of::<WeakIntrusive<SHAMapTreeNode>>(), 8);
        assert_eq!(std::mem::size_of::<SharedWeakUnion<SHAMapTreeNode>>(), 8);
        assert_eq!(tagged_arrays_layout(2).size(), 80);
        assert_eq!(tagged_arrays_layout(4).size(), 160);
        assert_eq!(tagged_arrays_layout(6).size(), 240);
        assert_eq!(tagged_arrays_layout(16).size(), 640);
    }

    #[test]
    fn clone_with_cowid_preserves_structure() {
        let parent = make_shared_intrusive(SHAMapTreeNode::new_inner(7));
        let child = make_shared_intrusive(SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionMd,
            SHAMapItem::new(sample_uint256(2), vec![3; 16]),
            0,
            sample_hash(6),
        ));
        parent.set_hash(sample_hash(1));
        parent.set_child_hash(3, sample_hash(6));
        parent.share_child(3, &child);
        parent.set_full_below_gen(22);

        let clone = parent.clone_with_cowid(11);
        assert_eq!(clone.cowid(), 11);
        assert_eq!(clone.get_hash(), sample_hash(1));
        assert_eq!(clone.branch_count(), 1);
        assert_eq!(clone.get_child_hash(3), sample_hash(6));
        assert!(clone.get_child(3).is_some());
        assert!(clone.is_full_below(22));
        let kind = clone.kind.write();
        assert!(matches!(&*kind, SHAMapTreeNodeKind::Inner(_)));
    }

    #[test]
    fn leaf_hashes_match_cpp_prefix_rules() {
        let key =
            Uint256::from_hex("ABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABAB")
                .expect("hex should parse");
        let data = vec![
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C,
        ];
        let item = SHAMapItem::new(key, data);

        let transaction = make_shared_intrusive(SHAMapTreeNode::new_leaf(
            SHAMapNodeType::TransactionNm,
            item.clone(),
            1,
        ));
        let account_state = make_shared_intrusive(SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            item.clone(),
            1,
        ));
        let transaction_with_meta = make_shared_intrusive(SHAMapTreeNode::new_leaf(
            SHAMapNodeType::TransactionMd,
            item,
            1,
        ));

        assert_eq!(
            transaction.get_hash().as_uint256(),
            &Uint256::from_hex("8D3E86DF0BB54DE1CA5EDD19A7FE40F867C6E8F582C10F1A4070D9B1EE29860A")
                .expect("hex should parse")
        );
        assert_eq!(
            account_state.get_hash().as_uint256(),
            &Uint256::from_hex("7366628114AD2CE841EF829E33329F01D0707FF3D2A0615019737CE5D26839E1")
                .expect("hex should parse")
        );
        assert_eq!(
            transaction_with_meta.get_hash().as_uint256(),
            &Uint256::from_hex("1BEC28450379604C872F97ADE3C14F06E995519966D62610622FC51645A7FF64")
                .expect("hex should parse")
        );
    }

    #[test]
    fn set_item_recomputes_leaf_hash_and_reports_when_it_changed() {
        let key = sample_uint256(0xAB);
        let leaf = make_shared_intrusive(SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![1; 12]),
            9,
        ));
        let original_hash = leaf.get_hash();

        assert!(leaf.set_item(SHAMapItem::new(key, vec![2; 12])));
        assert_ne!(leaf.get_hash(), original_hash);
        assert_eq!(
            leaf.peek_item().expect("leaf should keep an item").data(),
            &[2; 12]
        );

        assert!(!leaf.set_item(SHAMapItem::new(key, vec![2; 12])));
    }

    #[test]
    fn canonicalize_child_reuses_existing_loaded_child() {
        let parent = make_shared_intrusive(SHAMapTreeNode::new_inner(1));
        let child = make_shared_intrusive(SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(sample_uint256(5), vec![7; 12]),
            0,
            sample_hash(9),
        ));
        let competing_child = make_shared_intrusive(SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(sample_uint256(6), vec![8; 12]),
            0,
            sample_hash(9),
        ));

        parent.set_child_hash(4, sample_hash(9));
        let first = parent.canonicalize_child(4, child.clone());
        let second = parent.canonicalize_child(4, competing_child);

        assert!(same_node(&first, &child));
        assert!(same_node(&second, &child));
        assert!(same_node(
            &parent.get_child(4).expect("child should be cached"),
            &child
        ));
    }

    #[test]
    fn canonicalize_child_preserves_existing_full_below_mark_on_attached_child() {
        let parent = make_shared_intrusive(SHAMapTreeNode::new_inner(1));
        let child = make_shared_intrusive(SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(sample_uint256(7), vec![9; 12]),
            0,
            sample_hash(0x19),
        ));
        child.set_full_below_gen(22);

        parent.set_child_hash(4, sample_hash(0x19));
        let attached = parent.canonicalize_child(4, child.clone());

        assert!(same_node(&attached, &child));
        assert_eq!(attached.full_below_gen.load(Ordering::Relaxed), 22);
    }

    #[test]
    fn leaf_wire_and_prefix_codecs_match_cpp_layouts() {
        let key = sample_uint256(0xAB);
        let hash = sample_hash(0xCD);
        let payload = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
        let leaf = make_shared_intrusive(SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, payload.clone()),
            0,
            hash,
        ));

        let wire = leaf
            .serialize_for_wire()
            .expect("wire serialization should succeed");
        let prefix = leaf
            .serialize_with_prefix()
            .expect("prefix serialization should succeed");

        let mut expected_wire = payload.clone();
        expected_wire.extend_from_slice(key.data());
        expected_wire.push(WIRE_TYPE_ACCOUNT_STATE);
        assert_eq!(wire, expected_wire);

        let mut expected_prefix = HASH_PREFIX_LEAF_NODE.to_be_bytes().to_vec();
        expected_prefix.extend_from_slice(&payload);
        expected_prefix.extend_from_slice(key.data());
        assert_eq!(prefix, expected_prefix);

        let parsed_wire = SHAMapTreeNode::make_from_wire(&wire)
            .expect("wire decoding should succeed")
            .expect("wire decoding should return a node");
        assert_eq!(parsed_wire.get_type(), SHAMapNodeType::AccountState);
        assert_eq!(
            parsed_wire
                .peek_item()
                .expect("parsed account-state node should have an item"),
            SHAMapItem::new(key, payload.clone())
        );

        let parsed_prefix = SHAMapTreeNode::make_from_prefix(&prefix, hash)
            .expect("prefix decoding should succeed");
        assert_eq!(parsed_prefix.get_hash(), hash);
        assert_eq!(
            parsed_prefix
                .peek_item()
                .expect("parsed account-state node should have an item"),
            SHAMapItem::new(key, payload)
        );
    }

    #[test]
    fn inner_wire_and_prefix_codecs_match_cpp_layouts() {
        let sparse = make_shared_intrusive(SHAMapTreeNode::new_inner(1));
        sparse.set_child_hash(2, sample_hash(0x11));
        sparse.set_child_hash(15, sample_hash(0x22));

        let sparse_wire = sparse
            .serialize_for_wire()
            .expect("sparse inner wire serialization should succeed");
        assert_eq!(sparse_wire.last(), Some(&WIRE_TYPE_COMPRESSED_INNER));
        assert_eq!(sparse_wire.len(), 2 * (Uint256::BYTES + 1) + 1);
        assert_eq!(
            &sparse_wire[0..Uint256::BYTES],
            sample_hash(0x11).as_uint256().data()
        );
        assert_eq!(sparse_wire[Uint256::BYTES], 2);
        let second_hash_start = Uint256::BYTES + 1;
        assert_eq!(
            &sparse_wire[second_hash_start..second_hash_start + Uint256::BYTES],
            sample_hash(0x22).as_uint256().data()
        );
        assert_eq!(sparse_wire[second_hash_start + Uint256::BYTES], 15);

        let sparse_round_trip = SHAMapTreeNode::make_from_wire(&sparse_wire)
            .expect("compressed inner decoding should succeed")
            .expect("wire decoding should return a node");
        assert!(sparse_round_trip.is_inner());
        assert_eq!(sparse_round_trip.branch_count(), 2);
        assert_eq!(sparse_round_trip.get_child_hash(2), sample_hash(0x11));
        assert_eq!(sparse_round_trip.get_child_hash(15), sample_hash(0x22));

        let dense = make_shared_intrusive(SHAMapTreeNode::new_inner(1));
        for branch in 0..12 {
            dense.set_child_hash(branch, sample_hash(branch as u8 + 1));
        }

        let dense_wire = dense
            .serialize_for_wire()
            .expect("dense inner wire serialization should succeed");
        assert_eq!(dense_wire.last(), Some(&WIRE_TYPE_INNER));
        assert_eq!(dense_wire.len(), BRANCH_FACTOR * Uint256::BYTES + 1);

        let dense_prefix = dense
            .serialize_with_prefix()
            .expect("dense inner prefix serialization should succeed");
        assert_eq!(&dense_prefix[..4], &HASH_PREFIX_INNER_NODE.to_be_bytes());
        assert_eq!(dense_prefix.len(), 4 + BRANCH_FACTOR * Uint256::BYTES);

        let known_hash = sample_hash(0xFE);
        let parsed_prefix = SHAMapTreeNode::make_from_prefix(&dense_prefix, known_hash)
            .expect("dense prefix decoding should succeed");
        assert_eq!(parsed_prefix.get_hash(), known_hash);
        assert_eq!(parsed_prefix.branch_count(), 12);
        assert_eq!(parsed_prefix.get_child_hash(11), sample_hash(12));
    }

    #[test]
    fn update_hash_deep_refreshes_loaded_child_hashes_before_hashing_parent() {
        let parent = make_shared_intrusive(SHAMapTreeNode::new_inner(1));
        let child = make_shared_intrusive(SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(9), vec![7; 12]),
            0,
        ));

        parent.set_child_hash(5, sample_hash(1));
        parent.share_child(5, &child);
        let stale_parent_hash = {
            parent.update_hash();
            parent.get_hash()
        };

        assert_ne!(parent.get_child_hash(5), child.get_hash());
        parent.update_hash_deep();

        assert_eq!(parent.get_child_hash(5), child.get_hash());
        assert_ne!(parent.get_hash(), stale_parent_hash);
    }

    #[test]
    fn transaction_with_meta_prefix_round_trip_preserves_item_and_hash() {
        let key = sample_uint256(0x44);
        let hash = sample_hash(0xAA);
        let payload = vec![9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2];
        let node = make_shared_intrusive(SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionMd,
            SHAMapItem::new(key, payload.clone()),
            0,
            hash,
        ));

        let prefix = node
            .serialize_with_prefix()
            .expect("tx+meta prefix serialization should succeed");
        assert_eq!(&prefix[..4], &HASH_PREFIX_TX_NODE.to_be_bytes());

        let parsed = SHAMapTreeNode::make_from_prefix(&prefix, hash)
            .expect("tx+meta prefix decoding should succeed");
        assert_eq!(parsed.get_type(), SHAMapNodeType::TransactionMd);
        assert_eq!(parsed.get_hash(), hash);
        assert_eq!(
            parsed
                .peek_item()
                .expect("parsed tx+meta node should have an item"),
            SHAMapItem::new(key, payload)
        );
    }

    #[test]
    fn invalid_wire_and_prefix_inputs_are_rejected() {
        assert!(
            SHAMapTreeNode::make_from_wire(&[])
                .expect("empty wire input should not error")
                .is_none()
        );
        assert_eq!(
            SHAMapTreeNode::make_from_wire(&[99]).expect_err("unknown wire type should error"),
            SHAMapCodecError::UnknownWireType(99)
        );
        assert_eq!(
            SHAMapTreeNode::make_from_prefix(&[0, 1, 2], sample_hash(1))
                .expect_err("short prefix node should error"),
            SHAMapCodecError::ShortPrefixNode
        );
        assert_eq!(
            SHAMapTreeNode::make_from_wire(&[1, 2, 3, WIRE_TYPE_ACCOUNT_STATE])
                .expect_err("short account-state node should error"),
            SHAMapCodecError::ShortAccountStateNode(3)
        );
        let mut bad_account_state = vec![1; 12];
        bad_account_state.extend_from_slice(Uint256::zero().data());
        bad_account_state.push(WIRE_TYPE_ACCOUNT_STATE);
        assert_eq!(
            SHAMapTreeNode::make_from_wire(&bad_account_state)
                .expect_err("zero-key account-state node should error"),
            SHAMapCodecError::InvalidAccountStateNode
        );
        let mut bad_compressed_inner = vec![0; Uint256::BYTES];
        bad_compressed_inner.push(16);
        bad_compressed_inner.push(WIRE_TYPE_COMPRESSED_INNER);
        assert_eq!(
            SHAMapTreeNode::make_from_wire(&bad_compressed_inner)
                .expect_err("out-of-range compressed-inner branch should error"),
            SHAMapCodecError::InvalidCompressedInnerBranch(16)
        );
    }
}
