//! `xrpl/shamap/Family.h` compatibility surface.
//!
//! This centralizes the currently landed shared resources that sit above
//! `StorageTree` and `SyncTree`:
//! - the shared tree-node cache,
//! - the shared full-below cache,
//! - a fetch seam for backed sync paths, now including a
//!   `NodeObject`-shaped storage fetch boundary,
//! - a missing-node reporting seam,
//! - a storage write seam for backed flush paths.

use crate::node_object::NodeObject;
use crate::storage::{NodeObjectType, NodeStoreSink, StoredNode};
use crate::tree_node::SHAMapCodecError;
use crate::tree_node::SHAMapTreeNode;
use crate::tree_node_cache::TreeNodeCache;
use basics::base_uint::Uint256;
use basics::blob::Blob;
use basics::hardened_hash::HardenedHashBuilder;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::shared_weak_cache_pointer::SharedWeakCachePointer;
use basics::tagged_cache::{CacheClock, TaggedCache};
use parking_lot::Mutex;
use std::hash::BuildHasher;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use time::Duration;

fn full_sync_fetch_debug_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("QUAXAR_FULL_SYNC_DEBUG_FETCH")
            .map(|value| value == "1" || value.eq_ignore_ascii_case("true"))
            .unwrap_or(false)
    })
}

macro_rules! full_sync_fetch_debug {
    ($($arg:tt)*) => {
        if crate::owners::family::full_sync_fetch_debug_enabled() {
            tracing::debug!(target: "shamap", $($arg)*);
        }
    };
}

pub trait FullBelowCache: Send + Sync {
    fn generation(&self) -> u32;
    fn touch_if_exists(&self, hash: Uint256) -> bool;
    fn insert(&self, hash: Uint256);

    fn sweep(&self) {}

    fn clear(&self) {
        self.reset();
    }

    fn reset(&self) {}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NullFullBelowCache {
    generation: u32,
}

impl NullFullBelowCache {
    pub fn new(generation: u32) -> Self {
        Self { generation }
    }
}

impl FullBelowCache for NullFullBelowCache {
    fn generation(&self) -> u32 {
        self.generation
    }

    fn touch_if_exists(&self, _hash: Uint256) -> bool {
        false
    }

    fn insert(&self, _hash: Uint256) {}
}

pub struct FullBelowCacheImpl<C = basics::tagged_cache::MonotonicClock, S = HardenedHashBuilder>
where
    C: CacheClock,
    S: BuildHasher + Clone,
{
    generation: std::sync::atomic::AtomicU32,
    cache: TaggedCache<Uint256, (), C, S, SharedWeakCachePointer<()>, Arc<()>>,
}

impl<C, S> std::fmt::Debug for FullBelowCacheImpl<C, S>
where
    C: CacheClock,
    S: BuildHasher + Clone,
{
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("FullBelowCacheImpl")
            .field(
                "generation",
                &self.generation.load(std::sync::atomic::Ordering::Relaxed),
            )
            .field("entries", &self.size())
            .finish()
    }
}

impl<C, S> FullBelowCacheImpl<C, S>
where
    C: CacheClock,
    S: BuildHasher + Clone,
{
    /// Returns the current number of entries held in the full-below cache.
    pub fn size(&self) -> usize {
        self.cache.get_cache_size()
    }

    pub fn new(generation: u32, clock: C, hasher: S, target_size: usize) -> Self {
        Self::new_with_expiration(
            generation,
            clock,
            hasher,
            target_size,
            Duration::minutes(10),
        )
    }

    pub fn new_with_expiration(
        generation: u32,
        clock: C,
        hasher: S,
        target_size: usize,
        expiration: Duration,
    ) -> Self {
        Self {
            generation: std::sync::atomic::AtomicU32::new(generation),
            cache: TaggedCache::with_hasher(
                "FullBelowCache",
                target_size,
                expiration,
                clock,
                hasher,
            ),
        }
    }
}

impl<C, S> FullBelowCache for FullBelowCacheImpl<C, S>
where
    C: CacheClock + Send + Sync,
    S: BuildHasher + Clone + Send + Sync,
{
    fn generation(&self) -> u32 {
        self.generation.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn touch_if_exists(&self, hash: Uint256) -> bool {
        self.cache.fetch(&hash).is_some()
    }

    fn insert(&self, hash: Uint256) {
        let mut value = Arc::new(());
        self.cache.canonicalize_replace_client(&hash, &mut value);
    }

    fn sweep(&self) {
        self.cache.sweep();
    }

    fn clear(&self) {
        self.cache.clear();
        self.generation
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    fn reset(&self) {
        self.cache.reset();
        self.generation
            .store(1, std::sync::atomic::Ordering::Relaxed);
    }
}

/// Shared-reference impl so a persistent `FullBelowCacheImpl` can be reused
/// across ticks without moving it into each `SHAMapFamily`.
impl<C, S> FullBelowCache for &FullBelowCacheImpl<C, S>
where
    C: CacheClock + Send + Sync,
    S: BuildHasher + Clone + Send + Sync,
{
    fn generation(&self) -> u32 {
        self.generation.load(std::sync::atomic::Ordering::Relaxed)
    }
    fn touch_if_exists(&self, hash: Uint256) -> bool {
        self.cache.fetch(&hash).is_some()
    }
    fn insert(&self, hash: Uint256) {
        let mut value = Arc::new(());
        self.cache.canonicalize_replace_client(&hash, &mut value);
    }
}

impl<T> FullBelowCache for Arc<T>
where
    T: FullBelowCache,
{
    fn generation(&self) -> u32 {
        (**self).generation()
    }

    fn touch_if_exists(&self, hash: Uint256) -> bool {
        (**self).touch_if_exists(hash)
    }

    fn insert(&self, hash: Uint256) {
        (**self).insert(hash);
    }

    fn sweep(&self) {
        (**self).sweep();
    }

    fn clear(&self) {
        (**self).clear();
    }

    fn reset(&self) {
        (**self).reset();
    }
}

pub trait SHAMapNodeFetcher: Send + Sync + 'static {
    fn fetch_node(&self, _hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        None
    }

    fn fetch_node_object(&self, _hash: SHAMapHash, _ledger_seq: u32) -> Option<NodeObject> {
        None
    }

    fn fetch_node_blob(&self, _hash: SHAMapHash) -> Option<Blob> {
        None
    }
}

#[derive(Debug, Default)]
pub struct NullNodeFetcher;

impl SHAMapNodeFetcher for NullNodeFetcher {}

pub trait MissingNodeReporter: Send + Sync + 'static {
    fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256);
    fn missing_node_acquire_by_hash(&self, ref_hash: Uint256, ref_num: u32);

    fn reset(&self) {}
}

#[derive(Debug, Default)]
pub struct NullMissingNodeReporter;

impl MissingNodeReporter for NullMissingNodeReporter {
    fn missing_node_acquire_by_seq(&self, _ref_num: u32, _node_hash: Uint256) {}

    fn missing_node_acquire_by_hash(&self, _ref_hash: Uint256, _ref_num: u32) {}
}

impl<T> MissingNodeReporter for Arc<T>
where
    T: MissingNodeReporter + ?Sized,
{
    fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
        (**self).missing_node_acquire_by_seq(ref_num, node_hash);
    }

    fn missing_node_acquire_by_hash(&self, ref_hash: Uint256, ref_num: u32) {
        (**self).missing_node_acquire_by_hash(ref_hash, ref_num);
    }

    fn reset(&self) {
        (**self).reset();
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JournalLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

pub trait SHAMapJournal: Send + Sync + std::fmt::Debug + 'static {
    fn log(&self, level: JournalLevel, message: &str);
}

#[derive(Debug, Default)]
pub struct NullJournal;

impl SHAMapJournal for NullJournal {
    fn log(&self, _level: JournalLevel, _message: &str) {}
}

pub struct NodeFamilyMissingNodeReporter<L, A> {
    max_seq: Mutex<u32>,
    hash_by_seq: L,
    acquire: A,
    journal: Arc<dyn SHAMapJournal>,
}

impl<L, A> std::fmt::Debug for NodeFamilyMissingNodeReporter<L, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let max_seq = *self.max_seq.lock();
        f.debug_struct("NodeFamilyMissingNodeReporter")
            .field("max_seq", &max_seq)
            .finish()
    }
}

impl<L, A> NodeFamilyMissingNodeReporter<L, A>
where
    L: Fn(u32) -> Uint256 + Send + Sync + 'static,
    A: Fn(Uint256, u32) + Send + Sync + 'static,
{
    pub fn new(hash_by_seq: L, acquire: A) -> Self {
        Self::new_with_journal(hash_by_seq, acquire, Arc::new(NullJournal))
    }

    pub fn new_with_journal(hash_by_seq: L, acquire: A, journal: Arc<dyn SHAMapJournal>) -> Self {
        Self {
            max_seq: Mutex::new(0),
            hash_by_seq,
            acquire,
            journal,
        }
    }

    fn acquire_if_nonzero(&self, hash: Uint256, seq: u32) {
        if hash.is_zero() {
            return;
        }

        self.journal
            .log(JournalLevel::Error, &format!("Missing node in {hash}"));
        (self.acquire)(hash, seq);
    }
}

impl<L, A> MissingNodeReporter for NodeFamilyMissingNodeReporter<L, A>
where
    L: Fn(u32) -> Uint256 + Send + Sync + 'static,
    A: Fn(Uint256, u32) + Send + Sync + 'static,
{
    fn missing_node_acquire_by_seq(&self, mut seq: u32, _node_hash: Uint256) {
        self.journal
            .log(JournalLevel::Error, &format!("Missing node in {seq}"));

        let mut max_seq = self.max_seq.lock();
        if *max_seq == 0 {
            *max_seq = seq;

            loop {
                seq = *max_seq;
                drop(max_seq);

                self.acquire_if_nonzero((self.hash_by_seq)(seq), seq);

                max_seq = self.max_seq.lock();
                if *max_seq == seq {
                    break;
                }
            }
        } else if *max_seq < seq {
            *max_seq = seq;
        }
    }

    fn missing_node_acquire_by_hash(&self, ref_hash: Uint256, ref_num: u32) {
        self.acquire_if_nonzero(ref_hash, ref_num);
    }

    fn reset(&self) {
        *self.max_seq.lock() = 0;
    }
}

pub struct OwnerBackedFetchState {
    full: AtomicBool,
}

impl std::fmt::Debug for OwnerBackedFetchState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OwnerBackedFetchState")
            .field("full", &self.is_full())
            .finish()
    }
}

impl Default for OwnerBackedFetchState {
    fn default() -> Self {
        Self::new(false)
    }
}

impl Clone for OwnerBackedFetchState {
    fn clone(&self) -> Self {
        Self::new(self.is_full())
    }
}

impl OwnerBackedFetchState {
    pub fn new(full: bool) -> Self {
        Self {
            full: AtomicBool::new(full),
        }
    }

    pub fn is_full(&self) -> bool {
        self.full.load(Ordering::Acquire)
    }

    pub fn set_full(&self) {
        self.full.store(true, Ordering::Release);
    }

    pub fn clear_full(&self) {
        self.full.store(false, Ordering::Release);
    }

    pub fn report_missing_node_once<C, S, FB, F, MR, NS>(
        &self,
        ledger_seq: u32,
        hash: SHAMapHash,
        family: &SHAMapFamily<C, S, FB, F, MR, NS>,
    ) where
        MR: MissingNodeReporter,
    {
        if self.full.swap(false, Ordering::AcqRel) {
            family.missing_node_acquire_by_seq(ledger_seq, *hash.as_uint256());
        }
    }
}

pub(crate) enum CachedFetchResult {
    Found(SharedIntrusive<SHAMapTreeNode>),
    Missing,
    InvalidBlob,
}

#[derive(Debug)]
pub struct SHAMapFamily<C, S, FB, F, MR = NullMissingNodeReporter, NS = ()> {
    tree_node_cache: Arc<TreeNodeCache<C, S>>,
    full_below_cache: FB,
    fetcher: F,
    missing_node_reporter: MR,
    node_store: Option<Mutex<NS>>,
    journal: Arc<dyn SHAMapJournal>,
}

impl<C, S, FB, F, MR> SHAMapFamily<C, S, FB, F, MR, ()> {
    pub fn new(
        tree_node_cache: Arc<TreeNodeCache<C, S>>,
        full_below_cache: FB,
        fetcher: F,
        missing_node_reporter: MR,
    ) -> Self {
        Self::new_with_journal(
            tree_node_cache,
            full_below_cache,
            fetcher,
            missing_node_reporter,
            Arc::new(NullJournal),
        )
    }

    pub fn new_with_journal(
        tree_node_cache: Arc<TreeNodeCache<C, S>>,
        full_below_cache: FB,
        fetcher: F,
        missing_node_reporter: MR,
        journal: Arc<dyn SHAMapJournal>,
    ) -> Self {
        Self {
            tree_node_cache,
            full_below_cache,
            fetcher,
            missing_node_reporter,
            node_store: None,
            journal,
        }
    }
}

impl<C, S, FB, F, MR, NS> SHAMapFamily<C, S, FB, F, MR, NS> {
    pub fn new_with_node_store(
        tree_node_cache: Arc<TreeNodeCache<C, S>>,
        full_below_cache: FB,
        fetcher: F,
        missing_node_reporter: MR,
        node_store: NS,
    ) -> Self {
        Self::new_with_node_store_and_journal(
            tree_node_cache,
            full_below_cache,
            fetcher,
            missing_node_reporter,
            node_store,
            Arc::new(NullJournal),
        )
    }

    pub fn new_with_node_store_and_journal(
        tree_node_cache: Arc<TreeNodeCache<C, S>>,
        full_below_cache: FB,
        fetcher: F,
        missing_node_reporter: MR,
        node_store: NS,
        journal: Arc<dyn SHAMapJournal>,
    ) -> Self {
        Self {
            tree_node_cache,
            full_below_cache,
            fetcher,
            missing_node_reporter,
            node_store: Some(Mutex::new(node_store)),
            journal,
        }
    }

    pub fn tree_node_cache(&self) -> Arc<TreeNodeCache<C, S>> {
        self.tree_node_cache.clone()
    }

    pub fn cache_lookup(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>
    where
        C: CacheClock,
        S: BuildHasher + Clone,
    {
        self.tree_node_cache.fetch(hash.as_uint256())
    }

    pub fn canonicalize(&self, hash: SHAMapHash, node: &mut SharedIntrusive<SHAMapTreeNode>)
    where
        C: CacheClock,
        S: BuildHasher + Clone,
    {
        self.tree_node_cache
            .canonicalize_replace_client(hash.as_uint256(), node);
    }

    pub fn fetch_cached_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>
    where
        C: CacheClock,
        S: BuildHasher + Clone,
        F: SHAMapNodeFetcher,
    {
        match self.fetch_cached_node_result(hash) {
            CachedFetchResult::Found(node) => Some(node),
            CachedFetchResult::Missing | CachedFetchResult::InvalidBlob => None,
        }
    }

    pub(crate) fn fetch_cached_node_result(&self, hash: SHAMapHash) -> CachedFetchResult
    where
        C: CacheClock,
        S: BuildHasher + Clone,
        F: SHAMapNodeFetcher,
    {
        self.fetch_cached_node_result_with_ledger_seq(hash, 0)
    }

    pub(crate) fn fetch_cached_node_result_with_ledger_seq(
        &self,
        hash: SHAMapHash,
        ledger_seq: u32,
    ) -> CachedFetchResult
    where
        C: CacheClock,
        S: BuildHasher + Clone,
        F: SHAMapNodeFetcher,
    {
        if let Some(found) = self.cache_lookup(hash) {
            full_sync_fetch_debug!(
                "[full_debug][family_fetch] ledger_seq={} hash={} source=tree_cache result=hit",
                ledger_seq,
                hash
            );
            return CachedFetchResult::Found(found);
        }

        self.with_fetcher(|fetcher| {
            let mut fetched = if let Some(node) = fetcher.fetch_node(hash) {
                full_sync_fetch_debug!(
                    "[full_debug][family_fetch] ledger_seq={} hash={} source=fetch_node result=hit",
                    ledger_seq,
                    hash
                );
                node
            } else if let Some(object) = fetcher.fetch_node_object(hash, ledger_seq) {
                match SHAMapTreeNode::make_from_prefix(object.data(), hash) {
                    Ok(node) => {
                        full_sync_fetch_debug!(
                            "[full_debug][family_fetch] ledger_seq={} hash={} source=node_object result=hit bytes={}",
                            ledger_seq,
                            hash,
                            object.data().len()
                        );
                        node
                    }
                    Err(err) => {
                        self.log_warn(&format!(
                            "invalid fetched node object for hash {hash}: {err:?}"
                        ));
                        full_sync_fetch_debug!(
                            "[full_debug][family_fetch] ledger_seq={} hash={} source=node_object result=decode_fail err={:?}",
                            ledger_seq,
                            hash,
                            err
                        );
                        return CachedFetchResult::InvalidBlob;
                    }
                }
            } else if let Some(blob) = fetcher.fetch_node_blob(hash) {
                match SHAMapTreeNode::make_from_prefix(&blob, hash) {
                    Ok(node) => {
                        full_sync_fetch_debug!(
                            "[full_debug][family_fetch] ledger_seq={} hash={} source=blob result=hit bytes={}",
                            ledger_seq,
                            hash,
                            blob.len()
                        );
                        node
                    }
                    Err(err) => {
                        self.log_warn(&format!(
                            "invalid fetched node blob for hash {hash}: {err:?}"
                        ));
                        full_sync_fetch_debug!(
                            "[full_debug][family_fetch] ledger_seq={} hash={} source=blob result=decode_fail err={:?}",
                            ledger_seq,
                            hash,
                            err
                        );
                        return CachedFetchResult::InvalidBlob;
                    }
                }
            } else {
                full_sync_fetch_debug!(
                    "[full_debug][family_fetch] ledger_seq={} hash={} source=all result=miss",
                    ledger_seq,
                    hash
                );
                return CachedFetchResult::Missing;
            };

            self.canonicalize(hash, &mut fetched);
            CachedFetchResult::Found(fetched)
        })
    }

    pub fn fetch_cached_node_or_acquire_by_seq(
        &self,
        hash: SHAMapHash,
        ledger_seq: u32,
    ) -> Option<SharedIntrusive<SHAMapTreeNode>>
    where
        C: CacheClock,
        S: BuildHasher + Clone,
        F: SHAMapNodeFetcher,
        MR: MissingNodeReporter,
    {
        match self.fetch_cached_node_result_with_ledger_seq(hash, ledger_seq) {
            CachedFetchResult::Found(node) => Some(node),
            CachedFetchResult::Missing => {
                self.missing_node_acquire_by_seq(ledger_seq, *hash.as_uint256());
                None
            }
            CachedFetchResult::InvalidBlob => None,
        }
    }

    pub fn with_full_below_cache<T>(&self, callback: impl FnOnce(&FB) -> T) -> T {
        callback(&self.full_below_cache)
    }

    pub fn with_fetcher<T>(&self, callback: impl FnOnce(&F) -> T) -> T {
        callback(&self.fetcher)
    }

    pub fn with_sync_resources<T>(&self, callback: impl FnOnce(&FB, &F) -> T) -> T {
        callback(&self.full_below_cache, &self.fetcher)
    }

    pub fn with_node_store<T>(&self, callback: impl FnOnce(&mut NS) -> T) -> T {
        let mut node_store = self
            .node_store
            .as_ref()
            .expect("family node-store seam must be configured before use")
            .lock();
        callback(&mut *node_store)
    }

    pub fn store_node(&self, node: StoredNode)
    where
        NS: NodeStoreSink,
    {
        self.with_node_store(|node_store| node_store.store(node));
    }

    pub fn write_node(
        &self,
        object_type: NodeObjectType,
        ledger_seq: u32,
        mut node: SharedIntrusive<SHAMapTreeNode>,
    ) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapCodecError>
    where
        C: CacheClock,
        S: BuildHasher + Clone,
        NS: NodeStoreSink,
    {
        assert_eq!(
            node.cowid(),
            0,
            "family write_node requires a shareable node produced by walk_subtree"
        );

        let key = *node.get_hash().as_uint256();
        self.canonicalize(node.get_hash(), &mut node);

        let data = node.serialize_with_prefix()?;
        self.store_node(StoredNode::new(object_type, data, key, ledger_seq));
        Ok(node)
    }

    pub fn log(&self, level: JournalLevel, message: &str) {
        self.journal.log(level, message);
    }

    pub fn log_trace(&self, message: &str) {
        self.log(JournalLevel::Trace, message);
    }

    pub fn log_debug(&self, message: &str) {
        self.log(JournalLevel::Debug, message);
    }

    pub fn log_info(&self, message: &str) {
        self.log(JournalLevel::Info, message);
    }

    pub fn log_warn(&self, message: &str) {
        self.log(JournalLevel::Warn, message);
    }

    pub fn log_error(&self, message: &str) {
        self.log(JournalLevel::Error, message);
    }

    pub fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256)
    where
        MR: MissingNodeReporter,
    {
        self.missing_node_reporter
            .missing_node_acquire_by_seq(ref_num, node_hash);
    }

    pub fn missing_node_acquire_by_hash(&self, ref_hash: Uint256, ref_num: u32)
    where
        MR: MissingNodeReporter,
    {
        self.missing_node_reporter
            .missing_node_acquire_by_hash(ref_hash, ref_num);
    }

    pub fn reset(&self)
    where
        C: CacheClock,
        S: BuildHasher + Clone,
        FB: FullBelowCache,
        MR: MissingNodeReporter,
    {
        self.missing_node_reporter.reset();
        self.full_below_cache.reset();
        self.tree_node_cache.reset();
    }

    pub fn sweep(&self)
    where
        C: CacheClock,
        S: BuildHasher + Clone,
        FB: FullBelowCache,
    {
        self.full_below_cache.sweep();
        self.tree_node_cache.sweep();
    }
}

#[cfg(test)]
mod tests {
    use super::{
        FullBelowCache, FullBelowCacheImpl, HardenedHashBuilder, JournalLevel, MissingNodeReporter,
        NodeFamilyMissingNodeReporter, NullMissingNodeReporter, NullNodeFetcher, SHAMapFamily,
        SHAMapJournal, SHAMapNodeFetcher,
    };
    use crate::item::SHAMapItem;
    use crate::node_id::SHAMapNodeId;
    use crate::node_object::NodeObject;
    use crate::storage::{NodeObjectType, NodeStoreSink, StorageTree, StoredNode};
    use crate::sync::{SyncState, SyncTree};
    use crate::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use crate::tree_node_cache::TreeNodeCache;
    use basics::base_uint::Uint256;
    use basics::blob::Blob;
    use basics::intrusive_pointer::SharedIntrusive;
    use basics::sha_map_hash::SHAMapHash;
    use basics::tagged_cache::ManualClock;
    use parking_lot::Mutex;
    use std::collections::HashMap;
    use std::sync::Arc;
    use time::Duration;

    #[derive(Debug)]
    struct RecordingFullBelowCache {
        generation: std::sync::atomic::AtomicU32,
        inserted: parking_lot::Mutex<Vec<Uint256>>,
        sweeps: std::sync::atomic::AtomicUsize,
        clears: std::sync::atomic::AtomicUsize,
        resets: std::sync::atomic::AtomicUsize,
    }

    impl Default for RecordingFullBelowCache {
        fn default() -> Self {
            Self {
                generation: std::sync::atomic::AtomicU32::new(0),
                inserted: parking_lot::Mutex::new(Vec::new()),
                sweeps: std::sync::atomic::AtomicUsize::new(0),
                clears: std::sync::atomic::AtomicUsize::new(0),
                resets: std::sync::atomic::AtomicUsize::new(0),
            }
        }
    }

    impl RecordingFullBelowCache {
        fn new(generation: u32) -> Self {
            Self {
                generation: std::sync::atomic::AtomicU32::new(generation),
                ..Self::default()
            }
        }
    }

    impl FullBelowCache for RecordingFullBelowCache {
        fn generation(&self) -> u32 {
            self.generation.load(std::sync::atomic::Ordering::Relaxed)
        }

        fn touch_if_exists(&self, _hash: Uint256) -> bool {
            false
        }

        fn insert(&self, hash: Uint256) {
            self.inserted.lock().push(hash);
        }

        fn sweep(&self) {
            self.sweeps
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }

        fn clear(&self) {
            self.clears
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            self.inserted.lock().clear();
            self.generation
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }

        fn reset(&self) {
            self.resets
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            self.inserted.lock().clear();
            self.generation
                .store(1, std::sync::atomic::Ordering::Relaxed);
        }
    }

    #[derive(Debug, Default)]
    struct RecordingNodeFetcher {
        nodes: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
        fetches: Mutex<Vec<SHAMapHash>>,
    }

    impl RecordingNodeFetcher {
        fn with_node(hash: SHAMapHash, node: SharedIntrusive<SHAMapTreeNode>) -> Self {
            let mut nodes = HashMap::new();
            nodes.insert(hash, node);
            Self {
                nodes,
                fetches: Mutex::new(Vec::new()),
            }
        }
    }

    impl SHAMapNodeFetcher for RecordingNodeFetcher {
        fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.fetches.lock().push(hash);
            self.nodes.get(&hash).cloned()
        }
    }

    #[derive(Debug, Default)]
    struct BlobOnlyFetcher {
        blobs: HashMap<SHAMapHash, Blob>,
        fetches: Mutex<Vec<SHAMapHash>>,
    }

    impl SHAMapNodeFetcher for BlobOnlyFetcher {
        fn fetch_node_blob(&self, hash: SHAMapHash) -> Option<Blob> {
            self.fetches.lock().push(hash);
            self.blobs.get(&hash).cloned()
        }
    }

    #[derive(Debug, Default)]
    struct ObjectOnlyFetcher {
        objects: HashMap<SHAMapHash, NodeObject>,
        fetches: Mutex<Vec<(SHAMapHash, u32)>>,
    }

    impl SHAMapNodeFetcher for ObjectOnlyFetcher {
        fn fetch_node_object(&self, hash: SHAMapHash, ledger_seq: u32) -> Option<NodeObject> {
            self.fetches.lock().push((hash, ledger_seq));
            self.objects.get(&hash).cloned()
        }
    }

    #[derive(Debug, Default)]
    struct RecordingMissingNodeReporter {
        by_seq: Mutex<Vec<(u32, Uint256)>>,
        by_hash: Mutex<Vec<(Uint256, u32)>>,
        resets: Mutex<usize>,
    }

    impl MissingNodeReporter for RecordingMissingNodeReporter {
        fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
            self.by_seq.lock().push((ref_num, node_hash));
        }

        fn missing_node_acquire_by_hash(&self, ref_hash: Uint256, ref_num: u32) {
            self.by_hash.lock().push((ref_hash, ref_num));
        }

        fn reset(&self) {
            *self.resets.lock() += 1;
        }
    }

    #[derive(Default)]
    struct RecordingNodeStore {
        stored: Vec<StoredNode>,
    }

    impl NodeStoreSink for RecordingNodeStore {
        fn store(&mut self, node: StoredNode) {
            self.stored.push(node);
        }
    }

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

    fn sample_leaf(fill: u8) -> SharedIntrusive<SHAMapTreeNode> {
        SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(Uint256::from_array([fill; 32]), vec![fill; 12]),
            0,
        )
    }

    #[test]
    fn family_reset_and_sweep_bridge_shared_caches() {
        let cache = Arc::new(TreeNodeCache::new(
            "family-tree",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let canonical = sample_leaf(0x11);
        let mut cached = canonical.clone();
        assert!(!cache.canonicalize_replace_client(canonical.get_hash().as_uint256(), &mut cached));

        let family = SHAMapFamily::new(
            cache.clone(),
            RecordingFullBelowCache::new(9),
            NullNodeFetcher,
            NullMissingNodeReporter,
        );

        assert_eq!(cache.get_track_size(), 1);
        family.sweep();
        family.reset();

        family.with_full_below_cache(|full_below| {
            assert_eq!(
                full_below.sweeps.load(std::sync::atomic::Ordering::Relaxed),
                1
            );
            assert_eq!(
                full_below.clears.load(std::sync::atomic::Ordering::Relaxed),
                0
            );
            assert_eq!(
                full_below.resets.load(std::sync::atomic::Ordering::Relaxed),
                1
            );
        });
        assert_eq!(cache.get_track_size(), 0);
    }

    #[test]
    fn full_below_cache_clear_bumps_generation() {
        let cache =
            FullBelowCacheImpl::new(7, ManualClock::new(0), HardenedHashBuilder::default(), 8);
        let hash = Uint256::from_array([0x33; 32]);

        cache.insert(hash);
        assert_eq!(cache.generation(), 7);
        assert!(cache.touch_if_exists(hash));

        cache.clear();

        assert_eq!(cache.generation(), 8);
        assert!(!cache.touch_if_exists(hash));

        cache.reset();

        assert_eq!(cache.generation(), 1);
        assert!(!cache.touch_if_exists(hash));
    }

    #[test]
    fn sync_tree_get_missing_nodes_with_family_uses_shared_full_below_cache_and_fetcher() {
        let root = SHAMapTreeNode::new_inner(0);
        let leaf = sample_leaf(0x22);
        root.set_child_hash(3, leaf.get_hash());
        root.update_hash_deep();

        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "sync-tree",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            RecordingFullBelowCache::new(7),
            RecordingNodeFetcher::with_node(leaf.get_hash(), leaf.clone()),
            NullMissingNodeReporter,
        );
        let mut tree = SyncTree::from_root(root, true, 55, SyncState::Synching);

        let missing = tree.get_missing_nodes_with_family(8, &mut None, &family, &mut || 0);

        assert!(missing.is_empty());
        assert_eq!(tree.state(), SyncState::Modifying);
        family.with_full_below_cache(|full_below| {
            assert_eq!(
                full_below.inserted.lock().clone(),
                vec![*tree.root().get_hash().as_uint256()]
            );
        });
        family.with_fetcher(|fetcher| {
            assert_eq!(fetcher.fetches.lock().clone(), vec![leaf.get_hash()]);
        });
    }

    #[test]
    fn sync_tree_get_missing_nodes_with_family_reuses_deferred_restart_shape_for_nested_fetches() {
        let missing_leaf_hash = SHAMapHash::new(Uint256::from_array([0x39; 32]));
        let fetched_inner = SHAMapTreeNode::new_inner(1);
        fetched_inner.set_child_hash(7, missing_leaf_hash);
        fetched_inner.update_hash_deep();

        let root = SHAMapTreeNode::new_inner(0);
        root.set_child_hash(4, fetched_inner.get_hash());
        root.update_hash();

        let mut nodes = HashMap::new();
        nodes.insert(fetched_inner.get_hash(), fetched_inner.clone());
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "sync-tree-nested",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            RecordingFullBelowCache::new(8),
            RecordingNodeFetcher {
                nodes,
                fetches: Mutex::new(Vec::new()),
            },
            NullMissingNodeReporter,
        );
        let mut tree = SyncTree::from_root(root, true, 56, SyncState::Synching);

        let missing = tree.get_missing_nodes_with_family(8, &mut None, &family, &mut || 0);

        assert_eq!(
            missing,
            vec![(
                SHAMapNodeId::default()
                    .get_child_node_id(4)
                    .expect("child id should exist")
                    .get_child_node_id(7)
                    .expect("grandchild id should exist"),
                *missing_leaf_hash.as_uint256(),
            )]
        );
        assert!(tree.is_synching());
        family.with_fetcher(|fetcher| {
            assert_eq!(
                fetcher.fetches.lock().clone(),
                vec![fetched_inner.get_hash(), missing_leaf_hash]
            );
        });
    }

    #[test]
    fn storage_tree_new_with_family_uses_shared_tree_node_cache() {
        let cache = Arc::new(TreeNodeCache::new(
            "storage-tree",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let family = SHAMapFamily::new(
            cache.clone(),
            RecordingFullBelowCache::new(5),
            NullNodeFetcher,
            NullMissingNodeReporter,
        );

        let canonical = sample_leaf(0x33);
        let mut cached = canonical.clone();
        assert!(!cache.canonicalize_replace_client(canonical.get_hash().as_uint256(), &mut cached));

        let duplicate = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            canonical
                .peek_item()
                .expect("canonical leaf should carry an item"),
            1,
            canonical.get_hash(),
        );
        let mut tree = StorageTree::new_with_family(1, true, 91, &family);
        tree.root().set_child(1, Some(duplicate));
        tree.root().update_hash_deep();

        let mut sink = RecordingNodeStore::default();
        tree.flush_dirty(NodeObjectType::AccountNode, &mut sink)
            .expect("family-backed storage tree should flush cleanly");

        let resolved = tree
            .root()
            .get_child(1)
            .expect("flushed branch should keep a loaded child");
        assert!(std::ptr::eq(&*resolved, &*canonical));
        assert_eq!(sink.stored.len(), 2);
    }

    #[test]
    fn family_reports_missing_nodes_through_the_reporter_seam() {
        #[derive(Debug)]
        struct SharedReporter(Arc<Mutex<RecordingMissingNodeReporter>>);

        impl MissingNodeReporter for SharedReporter {
            fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
                self.0
                    .lock()
                    .missing_node_acquire_by_seq(ref_num, node_hash);
            }

            fn missing_node_acquire_by_hash(&self, ref_hash: Uint256, ref_num: u32) {
                self.0
                    .lock()
                    .missing_node_acquire_by_hash(ref_hash, ref_num);
            }

            fn reset(&self) {
                self.0.lock().reset();
            }
        }

        let recorder = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "reporter",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            RecordingFullBelowCache::new(1),
            NullNodeFetcher,
            SharedReporter(recorder.clone()),
        );
        let node_hash = Uint256::from_array([0xA5; 32]);
        let ledger_hash = Uint256::from_array([0xB6; 32]);

        family.missing_node_acquire_by_seq(91, node_hash);
        family.missing_node_acquire_by_hash(ledger_hash, 92);
        family.reset();

        let reporter = recorder.lock();
        assert_eq!(*reporter.by_seq.lock(), vec![(91, node_hash)]);
        assert_eq!(*reporter.by_hash.lock(), vec![(ledger_hash, 92)]);
        assert_eq!(*reporter.resets.lock(), 1);
    }

    #[test]
    fn fetch_cached_node_reuses_family_tree_cache_before_fetcher() {
        let cache = Arc::new(TreeNodeCache::new(
            "fetch-cache",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let canonical = sample_leaf(0x44);
        let mut cached = canonical.clone();
        assert!(!cache.canonicalize_replace_client(canonical.get_hash().as_uint256(), &mut cached));

        let family = SHAMapFamily::new(
            cache,
            RecordingFullBelowCache::new(1),
            RecordingNodeFetcher::with_node(canonical.get_hash(), sample_leaf(0x45)),
            NullMissingNodeReporter,
        );

        let resolved = family
            .fetch_cached_node(canonical.get_hash())
            .expect("cached family node should be returned");

        assert!(std::ptr::eq(&*resolved, &*canonical));
        family.with_fetcher(|fetcher| assert!(fetcher.fetches.lock().is_empty()));
    }

    #[test]
    fn fetch_cached_node_decodes_raw_blobs_and_populates_the_cache() {
        let cache = Arc::new(TreeNodeCache::new(
            "fetch-blob",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let fetched = sample_leaf(0x46);
        let mut blobs = HashMap::new();
        blobs.insert(
            fetched.get_hash(),
            fetched
                .serialize_with_prefix()
                .expect("sample leaf should serialize with prefix"),
        );

        let family = SHAMapFamily::new(
            cache.clone(),
            RecordingFullBelowCache::new(1),
            BlobOnlyFetcher {
                blobs,
                fetches: Mutex::new(Vec::new()),
            },
            NullMissingNodeReporter,
        );

        let first = family
            .fetch_cached_node(fetched.get_hash())
            .expect("raw node blob should decode");
        let second = family
            .fetch_cached_node(fetched.get_hash())
            .expect("decoded node should be cached");

        assert_eq!(first.get_hash(), fetched.get_hash());
        assert!(std::ptr::eq(&*first, &*second));
        family.with_fetcher(|fetcher| {
            assert_eq!(fetcher.fetches.lock().clone(), vec![fetched.get_hash()])
        });
        let cached = cache
            .fetch(fetched.get_hash().as_uint256())
            .expect("decoded node should be present in the cache");
        assert!(std::ptr::eq(&*cached, &*first));
    }

    #[test]
    fn fetch_cached_node_decodes_node_objects_and_populates_the_cache() {
        let cache = Arc::new(TreeNodeCache::new(
            "fetch-node-object",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let fetched = sample_leaf(0x47);
        let mut objects = HashMap::new();
        objects.insert(
            fetched.get_hash(),
            NodeObject::new(
                NodeObjectType::AccountNode,
                fetched
                    .serialize_with_prefix()
                    .expect("sample leaf should serialize with prefix"),
                *fetched.get_hash().as_uint256(),
            ),
        );

        let family = SHAMapFamily::new(
            cache.clone(),
            RecordingFullBelowCache::new(1),
            ObjectOnlyFetcher {
                objects,
                fetches: Mutex::new(Vec::new()),
            },
            NullMissingNodeReporter,
        );

        let first = family
            .fetch_cached_node(fetched.get_hash())
            .expect("node object should decode");
        let second = family
            .fetch_cached_node(fetched.get_hash())
            .expect("decoded node should be cached");

        assert_eq!(first.get_hash(), fetched.get_hash());
        assert!(std::ptr::eq(&*first, &*second));
        family.with_fetcher(|fetcher| {
            assert_eq!(
                fetcher.fetches.lock().clone(),
                vec![(fetched.get_hash(), 0)]
            )
        });
        let cached = cache
            .fetch(fetched.get_hash().as_uint256())
            .expect("decoded node should be present in the cache");
        assert!(std::ptr::eq(&*cached, &*first));
    }

    #[test]
    fn fetch_cached_node_or_acquire_by_seq_reports_misses() {
        #[derive(Debug)]
        struct SharedReporter(Arc<Mutex<RecordingMissingNodeReporter>>);

        impl MissingNodeReporter for SharedReporter {
            fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
                self.0
                    .lock()
                    .missing_node_acquire_by_seq(ref_num, node_hash);
            }

            fn missing_node_acquire_by_hash(&self, ref_hash: Uint256, ref_num: u32) {
                self.0
                    .lock()
                    .missing_node_acquire_by_hash(ref_hash, ref_num);
            }
        }

        let recorder = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "missing-seq",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            RecordingFullBelowCache::new(1),
            NullNodeFetcher,
            SharedReporter(recorder.clone()),
        );
        let missing = SHAMapHash::new(Uint256::from_array([0x55; 32]));

        assert!(
            family
                .fetch_cached_node_or_acquire_by_seq(missing, 600)
                .is_none()
        );
        let reporter = recorder.lock();
        assert_eq!(*reporter.by_seq.lock(), vec![(600, *missing.as_uint256())]);
    }

    #[test]
    fn fetch_cached_node_or_acquire_by_seq_forwards_ledger_seq_to_node_object_fetches() {
        let cache = Arc::new(TreeNodeCache::new(
            "fetch-node-object-by-seq",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let fetched = sample_leaf(0x48);
        let mut objects = HashMap::new();
        objects.insert(
            fetched.get_hash(),
            NodeObject::new(
                NodeObjectType::AccountNode,
                fetched
                    .serialize_with_prefix()
                    .expect("sample leaf should serialize with prefix"),
                *fetched.get_hash().as_uint256(),
            ),
        );

        let family = SHAMapFamily::new(
            cache,
            RecordingFullBelowCache::new(1),
            ObjectOnlyFetcher {
                objects,
                fetches: Mutex::new(Vec::new()),
            },
            NullMissingNodeReporter,
        );

        let resolved = family
            .fetch_cached_node_or_acquire_by_seq(fetched.get_hash(), 601)
            .expect("node object should decode through the ledger-seq path");
        assert_eq!(resolved.get_hash(), fetched.get_hash());
        family.with_fetcher(|fetcher| {
            assert_eq!(
                fetcher.fetches.lock().clone(),
                vec![(fetched.get_hash(), 601)]
            )
        });
    }

    #[test]
    fn invalid_raw_blobs_log_a_warning_without_reporting_a_missing_node() {
        #[derive(Debug)]
        struct SharedReporter(Arc<Mutex<RecordingMissingNodeReporter>>);

        impl MissingNodeReporter for SharedReporter {
            fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
                self.0
                    .lock()
                    .missing_node_acquire_by_seq(ref_num, node_hash);
            }

            fn missing_node_acquire_by_hash(&self, ref_hash: Uint256, ref_num: u32) {
                self.0
                    .lock()
                    .missing_node_acquire_by_hash(ref_hash, ref_num);
            }
        }

        let cache = Arc::new(TreeNodeCache::new(
            "invalid-blob",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
        let journal = Arc::new(RecordingJournal::default());
        let hash = SHAMapHash::new(Uint256::from_array([0x5A; 32]));
        let mut blobs = HashMap::new();
        blobs.insert(hash, vec![0x00, 0xFF, 0x7F]);

        let family = SHAMapFamily::new_with_journal(
            cache,
            RecordingFullBelowCache::new(1),
            BlobOnlyFetcher {
                blobs,
                fetches: Mutex::new(Vec::new()),
            },
            SharedReporter(reporter.clone()),
            journal.clone(),
        );

        assert!(
            family
                .fetch_cached_node_or_acquire_by_seq(hash, 700)
                .is_none()
        );
        assert!(reporter.lock().by_seq.lock().is_empty());
        assert_eq!(journal.entries().len(), 1);
        assert_eq!(journal.entries()[0].0, JournalLevel::Warn);
        assert!(journal.entries()[0].1.contains("invalid fetched node blob"));
    }

    #[test]
    fn node_family_missing_node_reporter_coalesces_reentrant_seq_requests() {
        fn seq_hash(seq: u32) -> Uint256 {
            Uint256::from_u64(seq as u64)
        }

        #[derive(Debug)]
        struct ReentrantAcquire {
            reporter: Mutex<Option<std::sync::Weak<dyn MissingNodeReporter>>>,
            acquired: Mutex<Vec<(Uint256, u32)>>,
        }

        impl ReentrantAcquire {
            fn new() -> Arc<Self> {
                Arc::new(Self {
                    reporter: Mutex::new(None),
                    acquired: Mutex::new(Vec::new()),
                })
            }
        }

        let journal = Arc::new(RecordingJournal::default());
        let acquire_state = ReentrantAcquire::new();
        let acquire_callback = {
            let acquire_state = acquire_state.clone();
            move |hash, seq| {
                acquire_state.acquired.lock().push((hash, seq));
                if seq == 610
                    && let Some(reporter) = acquire_state
                        .reporter
                        .lock()
                        .as_ref()
                        .and_then(std::sync::Weak::upgrade)
                {
                    reporter.missing_node_acquire_by_seq(612, Uint256::from_array([0xCC; 32]));
                    reporter.missing_node_acquire_by_seq(611, Uint256::from_array([0xDD; 32]));
                }
            }
        };
        let reporter = Arc::new(NodeFamilyMissingNodeReporter::new_with_journal(
            seq_hash,
            acquire_callback,
            journal.clone(),
        ));
        *acquire_state.reporter.lock() = Some(Arc::downgrade(
            &(reporter.clone() as Arc<dyn MissingNodeReporter>),
        ));

        reporter.missing_node_acquire_by_seq(610, Uint256::from_array([0xAA; 32]));

        assert_eq!(
            *acquire_state.acquired.lock(),
            vec![(seq_hash(610), 610), (seq_hash(612), 612)]
        );
        assert_eq!(
            journal.entries(),
            vec![
                (JournalLevel::Error, "Missing node in 610".to_owned()),
                (
                    JournalLevel::Error,
                    format!("Missing node in {}", seq_hash(610)),
                ),
                (JournalLevel::Error, "Missing node in 612".to_owned()),
                (JournalLevel::Error, "Missing node in 611".to_owned()),
                (
                    JournalLevel::Error,
                    format!("Missing node in {}", seq_hash(612)),
                ),
            ]
        );
    }

    #[test]
    fn node_family_missing_node_reporter_hash_path_and_reset_match_cpp_shape() {
        fn seq_hash(seq: u32) -> Uint256 {
            Uint256::from_u64(seq as u64)
        }

        let journal = Arc::new(RecordingJournal::default());
        let acquired = Arc::new(Mutex::new(Vec::new()));
        let reporter = NodeFamilyMissingNodeReporter::new_with_journal(
            seq_hash,
            {
                let acquired = acquired.clone();
                move |hash, seq| {
                    acquired.lock().push((hash, seq));
                }
            },
            journal.clone(),
        );

        reporter.missing_node_acquire_by_hash(seq_hash(700), 700);
        reporter.missing_node_acquire_by_seq(701, Uint256::from_array([0x11; 32]));
        reporter.reset();
        reporter.missing_node_acquire_by_seq(702, Uint256::from_array([0x22; 32]));
        reporter.missing_node_acquire_by_hash(Uint256::zero(), 703);

        assert_eq!(
            *acquired.lock(),
            vec![
                (seq_hash(700), 700),
                (seq_hash(701), 701),
                (seq_hash(702), 702),
            ]
        );
        assert_eq!(
            journal.entries(),
            vec![
                (
                    JournalLevel::Error,
                    format!("Missing node in {}", seq_hash(700)),
                ),
                (JournalLevel::Error, "Missing node in 701".to_owned()),
                (
                    JournalLevel::Error,
                    format!("Missing node in {}", seq_hash(701)),
                ),
                (JournalLevel::Error, "Missing node in 702".to_owned()),
                (
                    JournalLevel::Error,
                    format!("Missing node in {}", seq_hash(702)),
                ),
            ]
        );
    }

    #[test]
    fn family_write_node_uses_owned_node_store_and_canonical_cache() {
        let cache = Arc::new(TreeNodeCache::new(
            "family-store",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let canonical = sample_leaf(0x66);
        let mut cached = canonical.clone();
        assert!(!cache.canonicalize_replace_client(canonical.get_hash().as_uint256(), &mut cached));

        let duplicate = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            canonical
                .peek_item()
                .expect("canonical leaf should carry an item"),
            0,
            canonical.get_hash(),
        );
        let expected_bytes = canonical
            .serialize_with_prefix()
            .expect("leaf should serialize with a prefix");

        let family = SHAMapFamily::new_with_node_store(
            cache,
            RecordingFullBelowCache::new(1),
            NullNodeFetcher,
            NullMissingNodeReporter,
            RecordingNodeStore::default(),
        );

        let resolved = family
            .write_node(NodeObjectType::AccountNode, 700, duplicate)
            .expect("family write_node should serialize and store");

        assert!(std::ptr::eq(&*resolved, &*canonical));
        family.with_node_store(|node_store| {
            assert_eq!(
                node_store.stored,
                vec![StoredNode::new(
                    NodeObjectType::AccountNode,
                    expected_bytes,
                    *canonical.get_hash().as_uint256(),
                    700,
                )]
            );
        });
    }
}
