#![allow(clippy::type_complexity)]
//! `xrpl/shamap/SHAMapTreeNode.h`, `SHAMapInnerNode.h`, and
//! `SHAMapLeafNode.h` compatibility surface.
//!
//! This chooses a concrete owner plus enum layout instead of reference base-class
//! polymorphism so we can preserve intrusive lifetimes without requiring
//! trait-object intrusive pointers in the first SHAMap slice.

use crate::item::{SHAMapItem, shamap_item_memory_stats};
use basics::base_uint::Uint256;
use basics::intrusive_pointer::{IntrusiveObject, SharedIntrusive, SharedIntrusiveAdopt};
use basics::intrusive_ref_counts::IntrusiveRefCounts;
use basics::sha_map_hash::SHAMapHash;
use sha2::{Digest, Sha512};
use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use std::fmt;
use std::marker::PhantomData;
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicBool, AtomicU16, AtomicU32, AtomicU64, Ordering};

static ALLOCATED_INNER_NODES: AtomicU64 = AtomicU64::new(0);
static ALLOCATED_LEAF_NODES: AtomicU64 = AtomicU64::new(0);
static ACTIVE_INNER_NODES: AtomicU64 = AtomicU64::new(0);
static ACTIVE_LEAF_NODES: AtomicU64 = AtomicU64::new(0);
static ALLOCATED_CHILD_SLOTS: AtomicU64 = AtomicU64::new(0);
static LOADED_CHILD_LINKS: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SHAMapMemoryStats {
    pub allocated_inner_nodes: u64,
    pub allocated_leaf_nodes: u64,
    pub active_inner_nodes: u64,
    pub active_leaf_nodes: u64,
    pub allocated_child_slots: u64,
    pub loaded_child_links: u64,
    pub allocated_items: u64,
    pub allocated_item_bytes: u64,
    pub structural_bytes: u64,
}
pub fn shamap_memory_stats() -> SHAMapMemoryStats {
    let allocated_inner_nodes = ALLOCATED_INNER_NODES.load(Ordering::Relaxed);
    let allocated_leaf_nodes = ALLOCATED_LEAF_NODES.load(Ordering::Relaxed);
    let allocated_child_slots = ALLOCATED_CHILD_SLOTS.load(Ordering::Relaxed);
    let (allocated_items, allocated_item_bytes) = shamap_item_memory_stats();
    SHAMapMemoryStats {
        allocated_inner_nodes,
        allocated_leaf_nodes,
        active_inner_nodes: ACTIVE_INNER_NODES.load(Ordering::Relaxed),
        active_leaf_nodes: ACTIVE_LEAF_NODES.load(Ordering::Relaxed),
        allocated_child_slots,
        loaded_child_links: LOADED_CHILD_LINKS.load(Ordering::Relaxed),
        allocated_items,
        allocated_item_bytes,
        structural_bytes: allocated_inner_nodes
            .saturating_mul(64)
            .saturating_add(allocated_leaf_nodes.saturating_mul(56))
            .saturating_add(allocated_item_bytes)
            .saturating_add(allocated_child_slots.saturating_mul(
                (std::mem::size_of::<SHAMapHash>()
                    + std::mem::size_of::<Option<SharedIntrusive<SHAMapTreeNode>>>())
                    as u64,
            )),
    }
}

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

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SHAMapNodeType {
    Inner = 1,
    TransactionNm = 2,
    TransactionMd = 3,
    AccountState = 4,
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
                ptr::write(children.add(index), None);
            }
        }
        let raw = ptr.as_ptr() as usize;
        debug_assert_eq!(raw & 0b11, 0);
        debug_assert_eq!(layout.align() & 0b11, 0);
        ALLOCATED_CHILD_SLOTS.fetch_add(capacity as u64, Ordering::Relaxed);
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

    fn children(&self) -> *mut Option<SharedIntrusive<SHAMapTreeNode>> {
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
        unsafe { (&*self.children().add(index)).clone() }
    }

    fn has_child_at_index(&self, index: usize) -> bool {
        debug_assert!(index < self.capacity());
        unsafe { (&*self.children().add(index)).is_some() }
    }

    fn set_child_at_index(&self, index: usize, child: Option<SharedIntrusive<SHAMapTreeNode>>) {
        debug_assert!(index < self.capacity());
        unsafe {
            let slot = &mut *self.children().add(index);
            match (slot.is_some(), child.is_some()) {
                (false, true) => {
                    LOADED_CHILD_LINKS.fetch_add(1, Ordering::Relaxed);
                }
                (true, false) => {
                    LOADED_CHILD_LINKS.fetch_sub(1, Ordering::Relaxed);
                }
                _ => {}
            }
            *slot = child;
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
            let child = unsafe { (&mut *self.children().add(src_index)).take() };
            if child.is_some() {
                LOADED_CHILD_LINKS.fetch_sub(1, Ordering::Relaxed);
            }
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
                if (&*children.add(index)).is_some() {
                    LOADED_CHILD_LINKS.fetch_sub(1, Ordering::Relaxed);
                }
                ptr::drop_in_place(hashes.add(index));
                ptr::drop_in_place(children.add(index));
            }
            dealloc(ptr.as_ptr(), tagged_arrays_layout(capacity));
        }
        ALLOCATED_CHILD_SLOTS.fetch_sub(capacity as u64, Ordering::Relaxed);
        self.tagged = 0;
    }
}

/// Public prefix/base view for concrete SHAMap allocations. Public handles stay
/// `SharedIntrusive<SHAMapTreeNode>` while factories allocate concrete shells.
#[repr(C, align(8))]
pub struct SHAMapTreeNode {
    ref_counts: IntrusiveRefCounts,
    hash: std::cell::UnsafeCell<SHAMapHash>,
    cowid: AtomicU32,
    node_type: SHAMapNodeType,
    base_padding: [u8; 3],
}
#[repr(C)]
pub struct SHAMapInnerNode {
    node: SHAMapTreeNode,
    tagged: std::cell::UnsafeCell<TaggedPointer>,
    is_branch: AtomicU16,
    children_lock: AtomicU16,
    full_below_gen: AtomicU32,
}
#[repr(C)]
pub struct SHAMapLeafNode {
    node: SHAMapTreeNode,
    item: std::cell::UnsafeCell<Option<SHAMapItem>>,
}
const _: () = assert!(std::mem::size_of::<SHAMapTreeNode>() == 48);
const _: () = assert!(std::mem::align_of::<SHAMapTreeNode>() == 8);
const _: () = assert!(std::mem::size_of::<SHAMapInnerNode>() == 64);
const _: () = assert!(std::mem::align_of::<SHAMapInnerNode>() == 8);
const _: () = assert!(std::mem::size_of::<SHAMapLeafNode>() == 56);
const _: () = assert!(std::mem::align_of::<SHAMapLeafNode>() == 8);
const _: () = assert!(std::mem::size_of::<SharedIntrusive<SHAMapTreeNode>>() == 8);
unsafe impl Sync for SHAMapTreeNode {}
unsafe impl Send for SHAMapTreeNode {}
unsafe impl Sync for SHAMapInnerNode {}
unsafe impl Send for SHAMapInnerNode {}
unsafe impl Sync for SHAMapLeafNode {}
unsafe impl Send for SHAMapLeafNode {}
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
struct InnerLock<'a>(&'a SHAMapInnerNode);
impl Drop for InnerLock<'_> {
    fn drop(&mut self) {
        self.0.children_lock.store(0, Ordering::Release);
    }
}
// Leaf item synchronization must not consume a COW-ID bit: all `u32` COW
// values, including the high bit, are public and valid. Address-striped locks
// serialize leaf item access without adding a byte to the 56-byte leaf layout.
const NODE_LOCK_STRIPES: usize = 256;
static LEAF_ITEM_LOCKS: [AtomicBool; NODE_LOCK_STRIPES] =
    [const { AtomicBool::new(false) }; NODE_LOCK_STRIPES];
static NODE_HASH_LOCKS: [AtomicBool; NODE_LOCK_STRIPES] =
    [const { AtomicBool::new(false) }; NODE_LOCK_STRIPES];

// Test-only scheduling hooks make the COW/leaf-item interleaving reproducible
// without adding a byte to either concrete runtime node layout.
#[cfg(test)]
mod hash_lock_test_hooks {
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    pub(super) static TARGET: AtomicUsize = AtomicUsize::new(0);
    pub(super) static PAUSE_WRITER: AtomicBool = AtomicBool::new(false);
    pub(super) static WRITER_ACQUIRED: AtomicBool = AtomicBool::new(false);

    pub(super) fn after_write_acquire(address: usize) {
        if TARGET.load(Ordering::SeqCst) == address && PAUSE_WRITER.load(Ordering::SeqCst) {
            WRITER_ACQUIRED.store(true, Ordering::SeqCst);
            while PAUSE_WRITER.load(Ordering::SeqCst) {
                std::thread::yield_now();
            }
        }
    }

    pub(super) fn reset() {
        PAUSE_WRITER.store(false, Ordering::SeqCst);
        WRITER_ACQUIRED.store(false, Ordering::SeqCst);
        TARGET.store(0, Ordering::SeqCst);
    }
}

#[cfg(test)]
mod leaf_lock_test_hooks {
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    pub(super) static PAUSE_AFTER_ACQUIRE: AtomicBool = AtomicBool::new(false);
    pub(super) static ACQUIRED: AtomicUsize = AtomicUsize::new(0);
    pub(super) static UNSHARE_ENTERED: AtomicUsize = AtomicUsize::new(0);

    pub(super) fn after_acquire() {
        if PAUSE_AFTER_ACQUIRE.load(Ordering::SeqCst) {
            ACQUIRED.fetch_add(1, Ordering::SeqCst);
            while PAUSE_AFTER_ACQUIRE.load(Ordering::SeqCst) {
                std::thread::yield_now();
            }
        }
    }

    pub(super) fn reset() {
        PAUSE_AFTER_ACQUIRE.store(false, Ordering::SeqCst);
        ACQUIRED.store(0, Ordering::SeqCst);
        UNSHARE_ENTERED.store(0, Ordering::SeqCst);
    }
}

struct NodeStripedLock(&'static AtomicBool);
impl NodeStripedLock {
    fn acquire(lock: &'static AtomicBool) -> Self {
        loop {
            if lock
                .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                return Self(lock);
            }
            std::hint::spin_loop();
        }
    }
}
impl Drop for NodeStripedLock {
    fn drop(&mut self) {
        self.0.store(false, Ordering::Release);
    }
}
type LeafLock = NodeStripedLock;
impl SHAMapInnerNode {
    fn tagged(&self) -> &TaggedPointer {
        unsafe { &*self.tagged.get() }
    }
    fn tagged_mut(&self) -> &mut TaggedPointer {
        unsafe { &mut *self.tagged.get() }
    }
    fn lock(&self) -> InnerLock<'_> {
        loop {
            if self
                .children_lock
                .compare_exchange(0, u16::MAX, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                return InnerLock(self);
            }
            std::hint::spin_loop();
        }
    }
}
impl SHAMapLeafNode {
    fn item_lock(&self) -> &'static AtomicBool {
        let address = self as *const Self as usize;
        &LEAF_ITEM_LOCKS[(address >> 3) % NODE_LOCK_STRIPES]
    }

    fn lock(&self) -> LeafLock {
        let guard = LeafLock::acquire(self.item_lock());
        #[cfg(test)]
        leaf_lock_test_hooks::after_acquire();
        guard
    }
    fn item(&self) -> &Option<SHAMapItem> {
        unsafe { &*self.item.get() }
    }
    fn item_mut(&self) -> &mut Option<SHAMapItem> {
        unsafe { &mut *self.item.get() }
    }
}
impl SHAMapTreeNode {
    fn base(cowid: u32, node_type: SHAMapNodeType, hash: SHAMapHash) -> Self {
        Self {
            ref_counts: IntrusiveRefCounts::new(),
            hash: std::cell::UnsafeCell::new(hash),
            cowid: AtomicU32::new(cowid),
            node_type,
            base_padding: [0; 3],
        }
    }
    pub fn new_inner(cowid: u32) -> SharedIntrusive<Self> {
        Self::new_inner_with_capacity(cowid, 0)
    }
    fn new_inner_with_capacity(cowid: u32, capacity: usize) -> SharedIntrusive<Self> {
        let raw = Box::into_raw(Box::new(SHAMapInnerNode {
            node: Self::base(cowid, SHAMapNodeType::Inner, SHAMapHash::default()),
            tagged: std::cell::UnsafeCell::new(TaggedPointer::new(capacity)),
            is_branch: AtomicU16::new(0),
            children_lock: AtomicU16::new(0),
            full_below_gen: AtomicU32::new(0),
        }));
        ALLOCATED_INNER_NODES.fetch_add(1, Ordering::Relaxed);
        ACTIVE_INNER_NODES.fetch_add(1, Ordering::Relaxed);
        unsafe {
            SharedIntrusive::from_raw_with_owner(
                (&mut (*raw).node) as *mut Self,
                raw,
                SharedIntrusiveAdopt::NoIncrement,
            )
        }
    }
    pub fn new_leaf(
        node_type: SHAMapNodeType,
        item: SHAMapItem,
        cowid: u32,
    ) -> SharedIntrusive<Self> {
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
    ) -> SharedIntrusive<Self> {
        assert!(
            item.size() >= MIN_SHAMAP_ITEM_BYTES,
            "SHAMap leaf item payload below minimum size"
        );
        assert_ne!(node_type, SHAMapNodeType::Inner, "inner is not a leaf type");
        let raw = Box::into_raw(Box::new(SHAMapLeafNode {
            node: Self::base(cowid, node_type, hash),
            item: std::cell::UnsafeCell::new(Some(item)),
        }));
        ALLOCATED_LEAF_NODES.fetch_add(1, Ordering::Relaxed);
        ACTIVE_LEAF_NODES.fetch_add(1, Ordering::Relaxed);
        unsafe {
            SharedIntrusive::from_raw_with_owner(
                (&mut (*raw).node) as *mut Self,
                raw,
                SharedIntrusiveAdopt::NoIncrement,
            )
        }
    }
    fn inner(&self) -> &SHAMapInnerNode {
        assert!(self.is_inner(), "inner operation on leaf");
        unsafe { &*(self as *const Self as *const SHAMapInnerNode) }
    }
    fn leaf(&self) -> &SHAMapLeafNode {
        assert!(self.is_leaf(), "leaf operation on inner");
        unsafe { &*(self as *const Self as *const SHAMapLeafNode) }
    }
    pub fn cowid(&self) -> u32 {
        self.cowid.load(Ordering::Acquire)
    }
    pub fn unshare(&self) {
        if self.is_leaf() {
            // Lock the item first. This makes the COW transition and all
            // UnsafeCell access mutually exclusive: a writer either mutates
            // while still owned or observes zero and rejects the operation.
            #[cfg(test)]
            leaf_lock_test_hooks::UNSHARE_ENTERED.fetch_add(1, Ordering::SeqCst);
            let _guard = self.leaf().lock();
            self.cowid.store(0, Ordering::Release);
        } else {
            self.cowid.store(0, Ordering::Release);
        }
    }
    fn hash_lock(&self) -> NodeStripedLock {
        let address = self as *const Self as usize;
        NodeStripedLock::acquire(&NODE_HASH_LOCKS[(address >> 3) % NODE_LOCK_STRIPES])
    }

    fn hash_write_lock(&self) -> NodeStripedLock {
        let guard = self.hash_lock();
        #[cfg(test)]
        hash_lock_test_hooks::after_write_acquire(self as *const Self as usize);
        guard
    }

    fn get_hash_locked(&self) -> SHAMapHash {
        unsafe { *self.hash.get() }
    }

    fn set_hash_locked(&self, hash: SHAMapHash) {
        unsafe { *self.hash.get() = hash }
    }

    pub fn get_hash(&self) -> SHAMapHash {
        let _guard = self.hash_lock();
        self.get_hash_locked()
    }
    pub fn set_hash(&self, hash: SHAMapHash) {
        let _guard = self.hash_write_lock();
        self.set_hash_locked(hash)
    }
    pub fn zero_hash(&self) {
        self.set_hash(SHAMapHash::default())
    }
    pub fn get_type(&self) -> SHAMapNodeType {
        self.node_type
    }
    #[inline]
    pub fn is_leaf(&self) -> bool {
        self.node_type != SHAMapNodeType::Inner
    }
    #[inline]
    pub fn is_inner(&self) -> bool {
        self.node_type == SHAMapNodeType::Inner
    }
    pub fn clone_with_cowid(&self, cowid: u32) -> SharedIntrusive<Self> {
        if self.is_leaf() {
            let leaf = self.leaf();
            let _l = leaf.lock();
            return Self::new_leaf_with_hash(
                self.node_type,
                leaf.item().as_ref().expect("active leaf").clone(),
                cowid,
                self.get_hash(),
            );
        }
        let src = self.inner();
        let _src = src.lock();
        let branches = src.is_branch.load(Ordering::Relaxed);
        let cloned = Self::new_inner_with_capacity(cowid, branches.count_ones() as usize);
        cloned.set_hash(self.get_hash());
        {
            let dst = cloned.inner();
            let _dst = dst.lock();
            dst.is_branch.store(branches, Ordering::Relaxed);
            dst.full_below_gen.store(
                src.full_below_gen.load(Ordering::Relaxed),
                Ordering::Relaxed,
            );
            for branch in 0..BRANCH_FACTOR {
                if branches & (1 << branch) == 0 {
                    continue;
                }
                let si = src.tagged().child_index(branches, branch).unwrap();
                let di = dst.tagged().child_index(branches, branch).unwrap();
                dst.tagged()
                    .set_hash_at_index(di, src.tagged().get_hash(branches, branch));
                if let Some(child) = src.tagged().get_child_at_index(si) {
                    dst.tagged().set_child_at_index(di, Some(child));
                }
            }
        }
        cloned
    }
    pub fn is_empty(&self) -> bool {
        self.is_inner() && self.inner().is_branch.load(Ordering::Relaxed) == 0
    }
    pub fn is_empty_branch(&self, branch: usize) -> bool {
        validate_branch(branch);
        self.is_inner() && (self.inner().is_branch.load(Ordering::Relaxed) & (1 << branch)) == 0
    }
    pub fn branch_count(&self) -> usize {
        if self.is_inner() {
            self.inner().is_branch.load(Ordering::Relaxed).count_ones() as usize
        } else {
            0
        }
    }
    pub fn get_child_hash(&self, branch: usize) -> SHAMapHash {
        validate_branch(branch);
        if !self.is_inner() {
            return SHAMapHash::default();
        }
        let i = self.inner();
        let _l = i.lock();
        let b = i.is_branch.load(Ordering::Relaxed);
        i.tagged().get_hash(b, branch)
    }
    pub fn set_child_hash(&self, branch: usize, hash: SHAMapHash) {
        validate_branch(branch);
        let i = self.inner();
        let _l = i.lock();
        let src = i.is_branch.load(Ordering::Relaxed);
        let dst = if hash.is_non_zero() {
            src | (1 << branch)
        } else {
            src & !(1 << branch)
        };
        i.tagged_mut().rebuild(src, dst, dst.count_ones() as usize);
        i.is_branch.store(dst, Ordering::Relaxed);
        if hash.is_non_zero() {
            let n = i.tagged().child_index(dst, branch).unwrap();
            i.tagged().set_hash_at_index(n, hash)
        }
    }
    pub fn set_child(&self, branch: usize, child: Option<SharedIntrusive<Self>>) {
        validate_branch(branch);
        assert!(
            self.cowid() != 0,
            "owned inner nodes must have a non-zero cowid"
        );
        let i = self.inner();
        let _l = i.lock();
        let src = i.is_branch.load(Ordering::Relaxed);
        let dst = if child.is_some() {
            src | (1 << branch)
        } else {
            src & !(1 << branch)
        };
        i.tagged_mut().rebuild(src, dst, dst.count_ones() as usize);
        i.is_branch.store(dst, Ordering::Relaxed);
        if let Some(child) = child {
            let n = i.tagged().child_index(dst, branch).unwrap();
            i.tagged().set_hash_at_index(n, SHAMapHash::default());
            i.tagged().set_child_at_index(n, Some(child));
        }
        self.zero_hash()
    }
    pub fn share_child(&self, branch: usize, child: &SharedIntrusive<Self>) {
        validate_branch(branch);
        assert!(
            self.cowid() != 0,
            "owned inner nodes must have a non-zero cowid"
        );
        let i = self.inner();
        let _l = i.lock();
        let b = i.is_branch.load(Ordering::Relaxed);
        let n = i
            .tagged()
            .child_index(b, branch)
            .expect("branch must already exist");
        i.tagged().set_child_at_index(n, Some(child.clone()))
    }
    pub fn get_child(&self, branch: usize) -> Option<SharedIntrusive<Self>> {
        validate_branch(branch);
        if !self.is_inner() {
            return None;
        }
        let i = self.inner();
        let _l = i.lock();
        let b = i.is_branch.load(Ordering::Relaxed);
        i.tagged()
            .child_index(b, branch)
            .and_then(|n| i.tagged().get_child_at_index(n))
    }
    pub fn release_loaded_children(&self) {
        if !self.is_inner() {
            return;
        }
        let i = self.inner();
        let _l = i.lock();
        let b = i.is_branch.load(Ordering::Relaxed);
        i.tagged()
            .iter_non_empty_child_indexes(b, |_, n| i.tagged().set_child_at_index(n, None));
    }
    pub fn has_child(&self, branch: usize) -> bool {
        validate_branch(branch);
        if !self.is_inner() {
            return false;
        }
        let i = self.inner();
        let _l = i.lock();
        let b = i.is_branch.load(Ordering::Relaxed);
        i.tagged()
            .child_index(b, branch)
            .is_some_and(|n| i.tagged().has_child_at_index(n))
    }
    pub fn has_any_loaded_child(&self) -> bool {
        if !self.is_inner() {
            return false;
        }
        let i = self.inner();
        let _l = i.lock();
        let b = i.is_branch.load(Ordering::Relaxed);
        let mut yes = false;
        i.tagged()
            .iter_non_empty_child_indexes(b, |_, n| yes |= i.tagged().has_child_at_index(n));
        yes
    }
    pub fn canonicalize_child(
        &self,
        branch: usize,
        node: SharedIntrusive<Self>,
    ) -> SharedIntrusive<Self> {
        validate_branch(branch);
        assert_eq!(
            node.get_hash(),
            self.get_child_hash(branch),
            "canonicalized node hash must match the stored branch hash"
        );
        let i = self.inner();
        let _l = i.lock();
        let b = i.is_branch.load(Ordering::Relaxed);
        let n = i
            .tagged()
            .child_index(b, branch)
            .expect("branch must already exist");
        if let Some(old) = i.tagged().get_child_at_index(n) {
            old
        } else {
            i.tagged().set_child_at_index(n, Some(node.clone()));
            node
        }
    }
    pub fn is_full_below(&self, generation: u32) -> bool {
        self.is_inner() && self.inner().full_below_gen.load(Ordering::Relaxed) == generation
    }
    pub fn set_full_below_gen(&self, generation: u32) {
        if self.is_inner() {
            self.inner()
                .full_below_gen
                .store(generation, Ordering::Relaxed)
        }
    }

    pub fn peek_item(&self) -> Option<SHAMapItem> {
        if !self.is_leaf() {
            return None;
        }
        let l = self.leaf();
        let _g = l.lock();
        l.item().as_ref().cloned()
    }
    pub fn set_item(&self, item: SHAMapItem) -> bool {
        let l = self.leaf();
        let _g = l.lock();
        // The ownership decision and item mutation must share this guard. An
        // unshare that wins first publishes zero before releasing the same lock,
        // so a later writer cannot mutate a now-shareable leaf.
        assert!(
            self.cowid.load(Ordering::Acquire) != 0,
            "owned leaf nodes must have a non-zero cowid"
        );
        let old = self.get_hash();
        *l.item_mut() = Some(item);
        let next = compute_leaf_hash(self.node_type, l.item().as_ref().expect("active leaf"));
        self.set_hash(next);
        old != next
    }
    pub fn update_hash(&self) {
        let next = if self.is_inner() {
            let i = self.inner();
            let _g = i.lock();
            compute_inner_hash(i.is_branch.load(Ordering::Relaxed), i.tagged())
        } else {
            let l = self.leaf();
            let _g = l.lock();
            compute_leaf_hash(self.node_type, l.item().as_ref().expect("active leaf"))
        };
        self.set_hash(next)
    }
    pub fn update_hash_deep(&self) {
        let i = self.inner();
        let _g = i.lock();
        let b = i.is_branch.load(Ordering::Relaxed);
        i.tagged().iter_non_empty_child_indexes(b, |_, n| {
            if let Some(c) = i.tagged().get_child_at_index(n) {
                i.tagged().set_hash_at_index(n, c.get_hash())
            }
        });
        self.set_hash(compute_inner_hash(b, i.tagged()))
    }
    pub fn serialize_for_wire(&self) -> Result<Vec<u8>, SHAMapCodecError> {
        if self.is_inner() {
            let i = self.inner();
            let _g = i.lock();
            serialize_inner_for_wire(i.is_branch.load(Ordering::Relaxed), i.tagged())
        } else {
            let l = self.leaf();
            let _g = l.lock();
            Ok(serialize_leaf_for_wire(
                self.node_type,
                l.item().as_ref().expect("active leaf"),
            ))
        }
    }
    pub fn serialize_with_prefix(&self) -> Result<Vec<u8>, SHAMapCodecError> {
        if self.is_inner() {
            let i = self.inner();
            let _g = i.lock();
            serialize_inner_with_prefix(i.is_branch.load(Ordering::Relaxed), i.tagged())
        } else {
            let l = self.leaf();
            let _g = l.lock();
            Ok(serialize_leaf_with_prefix(
                self.node_type,
                l.item().as_ref().expect("active leaf"),
            ))
        }
    }
    pub fn make_from_wire(raw: &[u8]) -> Result<Option<SharedIntrusive<Self>>, SHAMapCodecError> {
        let Some((&ty, data)) = raw.split_last() else {
            return Ok(None);
        };
        Ok(Some(match ty {
            WIRE_TYPE_TRANSACTION => make_transaction_node(data, None)?,
            WIRE_TYPE_ACCOUNT_STATE => make_account_state_node(data, None)?,
            WIRE_TYPE_INNER => make_full_inner(data, None)?,
            WIRE_TYPE_COMPRESSED_INNER => make_compressed_inner(data)?,
            WIRE_TYPE_TRANSACTION_WITH_META => make_transaction_with_meta_node(data, None)?,
            other => return Err(SHAMapCodecError::UnknownWireType(other)),
        }))
    }
    pub fn make_from_prefix(
        raw: &[u8],
        hash: SHAMapHash,
    ) -> Result<SharedIntrusive<Self>, SHAMapCodecError> {
        if raw.len() < 4 {
            return Err(SHAMapCodecError::ShortPrefixNode);
        }
        let (p, d) = raw.split_at(4);
        match u32::from_be_bytes(p.try_into().unwrap()) {
            HASH_PREFIX_TRANSACTION_ID => make_transaction_node(d, Some(hash)),
            HASH_PREFIX_LEAF_NODE => make_account_state_node(d, Some(hash)),
            HASH_PREFIX_INNER_NODE => make_full_inner(d, Some(hash)),
            HASH_PREFIX_TX_NODE => make_transaction_with_meta_node(d, Some(hash)),
            x => Err(SHAMapCodecError::UnknownPrefixType(x)),
        }
    }
    fn partial_inner(&self) {
        let i = self.inner();
        ACTIVE_INNER_NODES.fetch_sub(1, Ordering::Relaxed);
        let _g = i.lock();
        let b = i.is_branch.load(Ordering::Relaxed);
        i.tagged()
            .iter_non_empty_child_indexes(b, |_, n| i.tagged().set_child_at_index(n, None));
    }
    fn partial_leaf(&self) {
        let l = self.leaf();
        ACTIVE_LEAF_NODES.fetch_sub(1, Ordering::Relaxed);
        let _g = l.lock();
        drop(l.item_mut().take());
    }
}
impl IntrusiveObject for SHAMapTreeNode {
    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
        &self.ref_counts
    }

    fn partial_destructor(&self) {
        if self.is_inner() {
            self.partial_inner()
        } else {
            self.partial_leaf()
        }
    }

    fn initialize_intrusive_owner<Owner: IntrusiveObject>(&self, _owner: std::ptr::NonNull<Owner>) {
        // The compact base discriminator supplies the same concrete destruction
        // dispatch as rippled's vtable. Registering every live node in the
        // generic owner map would add an out-of-object allocation per node.
    }

    fn dispatch_intrusive_partial_destroy(&self) {
        self.ref_counts
            .dispatch_partial_destroy_with(|| self.partial_destructor());
    }

    fn dispatch_intrusive_final_destroy(&self) {
        let raw = self as *const Self as *mut Self;
        unsafe {
            if self.is_inner() {
                drop(Box::from_raw(raw.cast::<SHAMapInnerNode>()));
            } else {
                drop(Box::from_raw(raw.cast::<SHAMapLeafNode>()));
            }
        }
    }
}
impl IntrusiveObject for SHAMapInnerNode {
    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
        self.node.intrusive_ref_counts()
    }
    fn partial_destructor(&self) {
        self.node.partial_inner()
    }
}
impl IntrusiveObject for SHAMapLeafNode {
    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
        self.node.intrusive_ref_counts()
    }
    fn partial_destructor(&self) {
        self.node.partial_leaf()
    }
}
impl Drop for SHAMapInnerNode {
    fn drop(&mut self) {
        if !self.node.ref_counts.partial_destroy_started() {
            ACTIVE_INNER_NODES.fetch_sub(1, Ordering::Relaxed);
        }
        ALLOCATED_INNER_NODES.fetch_sub(1, Ordering::Relaxed);
    }
}
impl Drop for SHAMapLeafNode {
    fn drop(&mut self) {
        if !self.node.ref_counts.partial_destroy_started() {
            ACTIVE_LEAF_NODES.fetch_sub(1, Ordering::Relaxed);
        }
        ALLOCATED_LEAF_NODES.fetch_sub(1, Ordering::Relaxed);
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
    let children = Layout::array::<Option<SharedIntrusive<SHAMapTreeNode>>>(capacity)
        .expect("valid child array layout");
    let (layout, _) = hashes
        .extend(children)
        .expect("valid tagged pointer layout");
    layout.pad_to_align()
}

fn child_offset(capacity: usize) -> usize {
    let hashes = Layout::array::<SHAMapHash>(capacity).expect("valid hash array layout");
    let children = Layout::array::<Option<SharedIntrusive<SHAMapTreeNode>>>(capacity)
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

fn children_ptr(ptr: NonNull<u8>, capacity: usize) -> *mut Option<SharedIntrusive<SHAMapTreeNode>> {
    unsafe { ptr.as_ptr().add(child_offset(capacity)).cast() }
}

fn serialize_leaf_for_wire(node_type: SHAMapNodeType, item: &SHAMapItem) -> Vec<u8> {
    let ty = match node_type {
        SHAMapNodeType::Inner => panic!("inner nodes are not serialized as leaves"),
        SHAMapNodeType::TransactionNm => WIRE_TYPE_TRANSACTION,
        SHAMapNodeType::TransactionMd => WIRE_TYPE_TRANSACTION_WITH_META,
        SHAMapNodeType::AccountState => WIRE_TYPE_ACCOUNT_STATE,
    };
    let mut out = Vec::with_capacity(item.size() + Uint256::BYTES + 1);
    out.extend_from_slice(item.data());
    if node_type != SHAMapNodeType::TransactionNm {
        out.extend_from_slice(item.key().data())
    }
    out.push(ty);
    out
}
fn serialize_leaf_with_prefix(node_type: SHAMapNodeType, item: &SHAMapItem) -> Vec<u8> {
    let p = match node_type {
        SHAMapNodeType::Inner => panic!("inner nodes are not serialized as leaves"),
        SHAMapNodeType::TransactionNm => HASH_PREFIX_TRANSACTION_ID,
        SHAMapNodeType::TransactionMd => HASH_PREFIX_TX_NODE,
        SHAMapNodeType::AccountState => HASH_PREFIX_LEAF_NODE,
    };
    let mut out = Vec::with_capacity(4 + item.size() + Uint256::BYTES);
    out.extend_from_slice(&p.to_be_bytes());
    out.extend_from_slice(item.data());
    if node_type != SHAMapNodeType::TransactionNm {
        out.extend_from_slice(item.key().data())
    }
    out
}
fn serialize_inner_for_wire(
    branches: u16,
    arrays: &TaggedPointer,
) -> Result<Vec<u8>, SHAMapCodecError> {
    if branches == 0 {
        return Err(SHAMapCodecError::EmptyInnerNodeSerialization);
    }
    if branches.count_ones() < 12 {
        let mut out = Vec::new();
        for b in 0..BRANCH_FACTOR {
            if branches & (1 << b) != 0 {
                out.extend_from_slice(arrays.get_hash(branches, b).as_uint256().data());
                out.push(b as u8)
            }
        }
        out.push(WIRE_TYPE_COMPRESSED_INNER);
        Ok(out)
    } else {
        let mut out = Vec::new();
        for b in 0..BRANCH_FACTOR {
            out.extend_from_slice(arrays.get_hash(branches, b).as_uint256().data())
        }
        out.push(WIRE_TYPE_INNER);
        Ok(out)
    }
}
fn serialize_inner_with_prefix(
    branches: u16,
    arrays: &TaggedPointer,
) -> Result<Vec<u8>, SHAMapCodecError> {
    if branches == 0 {
        return Err(SHAMapCodecError::EmptyInnerNodeSerialization);
    }
    let mut out = Vec::with_capacity(4 + BRANCH_FACTOR * Uint256::BYTES);
    out.extend_from_slice(&HASH_PREFIX_INNER_NODE.to_be_bytes());
    for b in 0..BRANCH_FACTOR {
        out.extend_from_slice(arrays.get_hash(branches, b).as_uint256().data())
    }
    Ok(out)
}
fn make_transaction_node(
    data: &[u8],
    known: Option<SHAMapHash>,
) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
    validate_leaf_payload(SHAMapNodeType::TransactionNm, data)?;
    let item = SHAMapItem::new(
        sha512_half_bytes(HASH_PREFIX_TRANSACTION_ID, [data]),
        data.to_vec(),
    );
    Ok(match known {
        Some(hash) => {
            SHAMapTreeNode::new_leaf_with_hash(SHAMapNodeType::TransactionNm, item, 0, hash)
        }
        None => SHAMapTreeNode::new_leaf(SHAMapNodeType::TransactionNm, item, 0),
    })
}
fn make_transaction_with_meta_node(
    data: &[u8],
    known: Option<SHAMapHash>,
) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
    if data.len() < Uint256::BYTES {
        return Err(SHAMapCodecError::ShortTransactionWithMetaNode(data.len()));
    }
    let (payload, key) = data.split_at(data.len() - Uint256::BYTES);
    validate_leaf_payload(SHAMapNodeType::TransactionMd, payload)?;
    let item = SHAMapItem::new(Uint256::from_slice(key).unwrap(), payload.to_vec());
    Ok(match known {
        Some(hash) => {
            SHAMapTreeNode::new_leaf_with_hash(SHAMapNodeType::TransactionMd, item, 0, hash)
        }
        None => SHAMapTreeNode::new_leaf(SHAMapNodeType::TransactionMd, item, 0),
    })
}
fn make_account_state_node(
    data: &[u8],
    known: Option<SHAMapHash>,
) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
    if data.len() < Uint256::BYTES {
        return Err(SHAMapCodecError::ShortAccountStateNode(data.len()));
    }
    let (payload, key) = data.split_at(data.len() - Uint256::BYTES);
    validate_leaf_payload(SHAMapNodeType::AccountState, payload)?;
    let key = Uint256::from_slice(key).unwrap();
    if key.is_zero() {
        return Err(SHAMapCodecError::InvalidAccountStateNode);
    }
    let item = SHAMapItem::new(key, payload.to_vec());
    Ok(match known {
        Some(hash) => {
            SHAMapTreeNode::new_leaf_with_hash(SHAMapNodeType::AccountState, item, 0, hash)
        }
        None => SHAMapTreeNode::new_leaf(SHAMapNodeType::AccountState, item, 0),
    })
}
fn validate_leaf_payload(node_type: SHAMapNodeType, data: &[u8]) -> Result<(), SHAMapCodecError> {
    if data.len() < MIN_SHAMAP_ITEM_BYTES {
        Err(SHAMapCodecError::ShortLeafNode {
            node_type,
            len: data.len(),
        })
    } else {
        Ok(())
    }
}
fn make_full_inner(
    data: &[u8],
    known: Option<SHAMapHash>,
) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
    if data.len() != BRANCH_FACTOR * Uint256::BYTES {
        return Err(SHAMapCodecError::InvalidFullInnerSize(data.len()));
    }
    let node = SHAMapTreeNode::new_inner_with_capacity(0, BRANCH_FACTOR);
    let i = node.inner();
    let _g = i.lock();
    let mut branches: u16 = 0;
    for (b, chunk) in data.chunks_exact(Uint256::BYTES).enumerate() {
        let hash = SHAMapHash::new(Uint256::from_slice(chunk).unwrap());
        i.tagged().set_hash_at_index(b, hash);
        if hash.is_non_zero() {
            branches |= 1 << b
        }
    }
    i.tagged_mut()
        .resize(branches, branches.count_ones() as usize);
    i.is_branch.store(branches, Ordering::Relaxed);
    drop(_g);
    if let Some(hash) = known {
        node.set_hash(hash)
    } else {
        node.update_hash()
    }
    Ok(node)
}
fn make_compressed_inner(data: &[u8]) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError> {
    let chunk = Uint256::BYTES + 1;
    if !data.len().is_multiple_of(chunk) || data.len() > chunk * BRANCH_FACTOR {
        return Err(SHAMapCodecError::InvalidCompressedInnerSize(data.len()));
    }
    let node = SHAMapTreeNode::new_inner_with_capacity(0, BRANCH_FACTOR);
    let i = node.inner();
    let _g = i.lock();
    let mut branches: u16 = 0;
    for c in data.chunks_exact(chunk) {
        let (h, p) = c.split_at(Uint256::BYTES);
        let b = p[0] as usize;
        if b >= BRANCH_FACTOR {
            return Err(SHAMapCodecError::InvalidCompressedInnerBranch(p[0]));
        }
        let hash = SHAMapHash::new(Uint256::from_slice(h).unwrap());
        i.tagged().set_hash_at_index(b, hash);
        if hash.is_non_zero() {
            branches |= 1 << b
        }
    }
    i.tagged_mut()
        .resize(branches, branches.count_ones() as usize);
    i.is_branch.store(branches, Ordering::Relaxed);
    drop(_g);
    node.update_hash();
    Ok(node)
}
fn compute_inner_hash(branches: u16, arrays: &TaggedPointer) -> SHAMapHash {
    if branches == 0 {
        return SHAMapHash::default();
    }
    let mut h = Sha512::new();
    h.update(HASH_PREFIX_INNER_NODE.to_be_bytes());
    arrays.iter_children(branches, |_, x| h.update(x.as_uint256().data()));
    let digest = h.finalize();
    let mut out = [0; Uint256::BYTES];
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
    SHAMapHash::new(if node_type == SHAMapNodeType::TransactionNm {
        sha512_half_bytes(prefix, [item.data()])
    } else {
        sha512_half_bytes(prefix, [item.data(), item.key().data()])
    })
}
fn sha512_half_bytes<I, T>(prefix: u32, parts: I) -> Uint256
where
    I: IntoIterator<Item = T>,
    T: AsRef<[u8]>,
{
    let mut h = Sha512::new();
    h.update(prefix.to_be_bytes());
    for p in parts {
        h.update(p.as_ref())
    }
    let d = h.finalize();
    let mut out = [0; Uint256::BYTES];
    out.copy_from_slice(&d[..Uint256::BYTES]);
    Uint256::from_array(out)
}

#[cfg(test)]
mod tests {
    use super::{
        BRANCH_FACTOR, HASH_PREFIX_INNER_NODE, HASH_PREFIX_LEAF_NODE, HASH_PREFIX_TX_NODE,
        SHAMapCodecError, SHAMapInnerNode, SHAMapItem, SHAMapLeafNode, SHAMapNodeType,
        SHAMapTreeNode, TaggedPointer, WIRE_TYPE_ACCOUNT_STATE, WIRE_TYPE_COMPRESSED_INNER,
        WIRE_TYPE_INNER,
    };
    use basics::base_uint::Uint256;
    use basics::intrusive_pointer::SharedIntrusive;
    use basics::sha_map_hash::SHAMapHash;
    use std::sync::atomic::Ordering;
    use std::sync::mpsc;
    use std::thread;
    use std::time::Duration;

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
        let child = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(sample_uint256(5), vec![7; 12]),
            0,
            sample_hash(5),
        );
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
        assert_eq!(compressed_node.inner().tagged().capacity(), 2);
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
        assert_eq!(full_node.inner().tagged().capacity(), BRANCH_FACTOR);
        assert_eq!(full_node.get_child_hash(11), sample_hash(12));
        assert_eq!(full_node.get_child_hash(12), SHAMapHash::default());
    }

    #[test]
    fn concrete_runtime_layouts_match_cpp_measurements() {
        assert_eq!(std::mem::size_of::<SHAMapInnerNode>(), 64);
        assert_eq!(std::mem::align_of::<SHAMapInnerNode>(), 8);
        assert_eq!(std::mem::size_of::<SHAMapLeafNode>(), 56);
        assert_eq!(std::mem::align_of::<SHAMapLeafNode>(), 8);
        assert_eq!(std::mem::size_of::<SharedIntrusive<SHAMapTreeNode>>(), 8);
        assert_eq!(
            std::mem::size_of::<Option<SharedIntrusive<SHAMapTreeNode>>>(),
            8
        );
    }

    #[test]
    fn compact_nodes_do_not_allocate_generic_owner_registry_entries() {
        let inner = SHAMapTreeNode::new_inner(1);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(0x91), vec![0x22; 12]),
            1,
        );
        assert!(!inner.ref_counts.has_registered_owner_metadata());
        assert!(!leaf.ref_counts.has_registered_owner_metadata());
    }

    #[test]
    fn common_node_fields_match_cpp_roles() {
        let node = SHAMapTreeNode::new_inner(9);
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
        let parent = SHAMapTreeNode::new_inner(1);
        let child = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(3), vec![1; 12]),
            0,
        );

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
        let parent = SHAMapTreeNode::new_inner(1);
        let child = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(sample_uint256(4), vec![2; 12]),
            0,
            sample_hash(5),
        );
        let child_weak = child.downgrade();

        parent.set_child_hash(1, sample_hash(5));
        parent.share_child(1, &child);
        drop(child);
        assert!(!child_weak.expired());

        let parent_raw = &*parent as *const SHAMapTreeNode;
        let parent_weak = parent.downgrade();
        drop(parent);
        assert!(parent_weak.expired());
        assert!(child_weak.expired());
        // Weak ownership retains the allocation shell and immutable topology.
        let partially_destroyed = unsafe { &*parent_raw };
        assert_eq!(partially_destroyed.get_child_hash(1), sample_hash(5));
        assert!(partially_destroyed.get_child(1).is_none());
        assert!(!partially_destroyed.is_empty_branch(1));
        drop(parent_weak);
    }

    #[test]
    fn clone_with_cowid_preserves_structure() {
        let parent = SHAMapTreeNode::new_inner(7);
        let child = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionMd,
            SHAMapItem::new(sample_uint256(2), vec![3; 16]),
            0,
            sample_hash(6),
        );
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
        assert!(clone.is_inner());
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

        let transaction = SHAMapTreeNode::new_leaf(SHAMapNodeType::TransactionNm, item.clone(), 1);
        let account_state = SHAMapTreeNode::new_leaf(SHAMapNodeType::AccountState, item.clone(), 1);
        let transaction_with_meta =
            SHAMapTreeNode::new_leaf(SHAMapNodeType::TransactionMd, item, 1);

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
    fn concurrent_hash_read_waits_for_compact_node_writer() {
        use super::hash_lock_test_hooks::{PAUSE_WRITER, TARGET, WRITER_ACQUIRED, reset};

        reset();
        let node = SHAMapTreeNode::new_inner(1);
        let next = sample_hash(0xE1);
        TARGET.store((&*node as *const SHAMapTreeNode) as usize, Ordering::SeqCst);
        PAUSE_WRITER.store(true, Ordering::SeqCst);

        let writer = {
            let node = node.clone();
            thread::spawn(move || node.set_hash(next))
        };
        while !WRITER_ACQUIRED.load(Ordering::SeqCst) {
            thread::yield_now();
        }

        let (done_tx, done_rx) = mpsc::channel();
        let reader = {
            let node = node.clone();
            thread::spawn(move || {
                done_tx.send(node.get_hash()).expect("hash reader receiver");
            })
        };
        assert!(
            done_rx.recv_timeout(Duration::from_millis(50)).is_err(),
            "hash reader must not access UnsafeCell while writer owns its stripe"
        );

        PAUSE_WRITER.store(false, Ordering::SeqCst);
        writer.join().expect("hash writer should join");
        assert_eq!(
            done_rx
                .recv_timeout(Duration::from_secs(1))
                .expect("hash reader should resume"),
            next
        );
        reader.join().expect("hash reader should join");
        reset();
    }

    #[test]
    fn leaf_unshare_waits_for_item_lock_and_rejects_post_unshare_mutation() {
        use super::leaf_lock_test_hooks::{ACQUIRED, PAUSE_AFTER_ACQUIRE, UNSHARE_ENTERED, reset};

        reset();
        let key = sample_uint256(0xAB);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![1; 12]),
            9,
        );
        let updated = SHAMapItem::new(key, vec![2; 12]);
        let expected = updated.clone();

        PAUSE_AFTER_ACQUIRE.store(true, Ordering::SeqCst);
        let writer = {
            let leaf = leaf.clone();
            thread::spawn(move || leaf.set_item(updated))
        };
        while ACQUIRED.load(Ordering::SeqCst) == 0 {
            thread::yield_now();
        }

        let (done_tx, done_rx) = mpsc::channel();
        let unshare = {
            let leaf = leaf.clone();
            thread::spawn(move || {
                leaf.unshare();
                done_tx.send(()).expect("unshare completion receiver");
            })
        };
        while UNSHARE_ENTERED.load(Ordering::SeqCst) == 0 {
            thread::yield_now();
        }
        // The writer owns LeafLock and has not entered the item UnsafeCell yet;
        // unshare has started but must not clear its lock bit or return.
        assert!(done_rx.try_recv().is_err());
        assert_eq!(leaf.cowid(), 9);

        PAUSE_AFTER_ACQUIRE.store(false, Ordering::SeqCst);
        assert!(writer.join().expect("leaf writer should complete"));
        done_rx
            .recv_timeout(Duration::from_secs(1))
            .expect("unshare should complete once the item lock is released");
        unshare.join().expect("unshare thread should join");

        assert_eq!(leaf.cowid(), 0);
        assert_eq!(leaf.peek_item(), Some(expected.clone()));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            leaf.set_item(SHAMapItem::new(key, vec![3; 12]));
        }));
        assert!(rejected.is_err());
        assert_eq!(leaf.peek_item(), Some(expected));
        reset();
    }

    #[test]
    fn leaf_lock_preserves_high_bit_cowid() {
        let key = sample_uint256(0xCD);
        let cowid = 0x8000_1234;
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![1; 12]),
            cowid,
        );

        assert_eq!(leaf.cowid(), cowid);
        assert_eq!(leaf.peek_item(), Some(SHAMapItem::new(key, vec![1; 12])));
        assert!(leaf.set_item(SHAMapItem::new(key, vec![2; 12])));
        assert_eq!(leaf.cowid(), cowid);
        leaf.unshare();
        assert_eq!(leaf.cowid(), 0);
    }

    #[test]
    fn set_item_recomputes_leaf_hash_and_reports_when_it_changed() {
        let key = sample_uint256(0xAB);
        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, vec![1; 12]),
            9,
        );
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
        let parent = SHAMapTreeNode::new_inner(1);
        let child = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(sample_uint256(5), vec![7; 12]),
            0,
            sample_hash(9),
        );
        let competing_child = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionNm,
            SHAMapItem::new(sample_uint256(6), vec![8; 12]),
            0,
            sample_hash(9),
        );

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
    fn canonicalize_child_preserves_existing_full_below_mark_on_attached_inner() {
        let parent = SHAMapTreeNode::new_inner(1);
        let child = SHAMapTreeNode::new_inner(0);
        child.set_hash(sample_hash(0x19));
        child.set_full_below_gen(22);

        parent.set_child_hash(4, sample_hash(0x19));
        let attached = parent.canonicalize_child(4, child.clone());

        assert!(same_node(&attached, &child));
        assert!(attached.is_full_below(22));
    }

    #[test]
    fn leaf_wire_and_prefix_codecs_match_cpp_layouts() {
        let key = sample_uint256(0xAB);
        let hash = sample_hash(0xCD);
        let payload = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
        let leaf = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, payload.clone()),
            0,
            hash,
        );

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
        let sparse = SHAMapTreeNode::new_inner(1);
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

        let dense = SHAMapTreeNode::new_inner(1);
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
        let parent = SHAMapTreeNode::new_inner(1);
        let child = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(9), vec![7; 12]),
            0,
        );

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
        let node = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::TransactionMd,
            SHAMapItem::new(key, payload.clone()),
            0,
            hash,
        );

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
