//! Rust migration boundary for `xrpl/basics/TaggedCache.h`.
//!
//! This module covers the semantics exercised by the current `TaggedCache` and
//! `KeyCache` unit tests:
//! - partition-aware storage,
//! - strong/weak cache entry transitions,
//! - deterministic clock-driven sweeping,
//! - canonicalization behavior.
//!
//! It now includes explicit logging and metrics seams plus intrusive-pointer
//! cache support with explicit caller-provided integration seams.

use crate::hardened_hash::HardenedHashBuilder;
use crate::intrusive_pointer::{
    IntrusiveObject, SharedIntrusive, SharedWeakUnion, make_shared_intrusive,
};
use crate::mutex::RecursiveMutex;
use crate::partitioned_unordered_map::{PartitionKey, PartitionedUnorderedMap};
use crate::shared_weak_cache_pointer::SharedWeakCachePointer;
use std::borrow::Borrow;
use std::collections::HashMap as StdHashMap;
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::ops::Deref;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;
use time::Duration;

pub trait CacheClock: Send + Sync + 'static {
    fn now(&self) -> Duration;
}

#[derive(Debug, Clone)]
pub struct MonotonicClock {
    start: Instant,
}

impl Default for MonotonicClock {
    fn default() -> Self {
        Self {
            start: Instant::now(),
        }
    }
}

impl CacheClock for MonotonicClock {
    fn now(&self) -> Duration {
        Duration::nanoseconds(self.start.elapsed().as_nanos() as i64)
    }
}

/// Deterministic clock for compatibility tests.
#[derive(Debug, Default)]
pub struct ManualClock {
    seconds: AtomicI64,
}

impl ManualClock {
    pub fn new(seconds: i64) -> Self {
        Self {
            seconds: AtomicI64::new(seconds),
        }
    }

    pub fn set(&self, seconds: i64) {
        self.seconds.store(seconds, Ordering::SeqCst);
    }

    pub fn advance_seconds(&self, seconds: i64) {
        self.seconds.fetch_add(seconds, Ordering::SeqCst);
    }
}

impl CacheClock for ManualClock {
    fn now(&self) -> Duration {
        Duration::seconds(self.seconds.load(Ordering::SeqCst))
    }
}

impl<C> CacheClock for Arc<C>
where
    C: CacheClock + ?Sized,
{
    fn now(&self) -> Duration {
        self.as_ref().now()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TaggedCacheMetricsSnapshot {
    size: usize,
    track_size: usize,
    hit_rate: u64,
    hits: u64,
    misses: u64,
}

impl TaggedCacheMetricsSnapshot {
    pub fn size(&self) -> usize {
        self.size
    }

    pub fn track_size(&self) -> usize {
        self.track_size
    }

    pub fn hit_rate(&self) -> u64 {
        self.hit_rate
    }

    pub fn hits(&self) -> u64 {
        self.hits
    }

    pub fn misses(&self) -> u64 {
        self.misses
    }
}

pub trait TaggedCacheMetrics: Send + Sync + 'static {
    fn observe(&self, name: &str, snapshot: &TaggedCacheMetricsSnapshot);
}

pub trait TaggedCacheLogger: Send + Sync + 'static {
    fn trace(&self, message: &str);
    fn debug(&self, message: &str);
}

#[derive(Debug, Default)]
pub struct NullTaggedCacheMetrics;

impl TaggedCacheMetrics for NullTaggedCacheMetrics {
    fn observe(&self, _name: &str, _snapshot: &TaggedCacheMetricsSnapshot) {}
}

#[derive(Debug, Default)]
pub struct NullTaggedCacheLogger;

impl TaggedCacheLogger for NullTaggedCacheLogger {
    fn trace(&self, _message: &str) {}
    fn debug(&self, _message: &str) {}
}

#[derive(Clone)]
struct TaggedCacheInstrumentation {
    metrics: Arc<dyn TaggedCacheMetrics>,
    logger: Arc<dyn TaggedCacheLogger>,
}

impl Default for TaggedCacheInstrumentation {
    fn default() -> Self {
        Self {
            metrics: Arc::new(NullTaggedCacheMetrics),
            logger: Arc::new(NullTaggedCacheLogger),
        }
    }
}

impl fmt::Debug for TaggedCacheInstrumentation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TaggedCacheInstrumentation")
            .finish_non_exhaustive()
    }
}

pub trait CacheStrongPointer<T>: Clone + Deref<Target = T> {
    fn from_value(value: T) -> Self;
}

impl<T> CacheStrongPointer<T> for Arc<T> {
    fn from_value(value: T) -> Self {
        Arc::new(value)
    }
}

impl<T> CacheStrongPointer<T> for SharedIntrusive<T>
where
    T: IntrusiveObject,
{
    fn from_value(value: T) -> Self {
        make_shared_intrusive(value)
    }
}

pub trait CachePointer<T, SP>: Clone {
    fn from_strong(value: SP) -> Self;
    fn strong_clone(&self) -> Option<SP>;
    fn lock(&self) -> Option<SP>;
    fn is_strong(&self) -> bool;
    fn expired(&self) -> bool;
    fn convert_to_weak(&mut self) -> bool;
    fn set_strong(&mut self, value: SP);
    fn use_count(&self) -> usize;

    fn is_weak(&self) -> bool {
        !self.is_strong()
    }
}

impl<T> CachePointer<T, Arc<T>> for SharedWeakCachePointer<T> {
    fn from_strong(value: Arc<T>) -> Self {
        SharedWeakCachePointer::from_arc(value)
    }

    fn strong_clone(&self) -> Option<Arc<T>> {
        SharedWeakCachePointer::strong_clone(self)
    }

    fn lock(&self) -> Option<Arc<T>> {
        SharedWeakCachePointer::lock(self)
    }

    fn is_strong(&self) -> bool {
        SharedWeakCachePointer::is_strong(self)
    }

    fn expired(&self) -> bool {
        SharedWeakCachePointer::expired(self)
    }

    fn convert_to_weak(&mut self) -> bool {
        SharedWeakCachePointer::convert_to_weak(self)
    }

    fn set_strong(&mut self, value: Arc<T>) {
        SharedWeakCachePointer::set_strong(self, value);
    }

    fn use_count(&self) -> usize {
        SharedWeakCachePointer::use_count(self)
    }
}

impl<T> CachePointer<T, SharedIntrusive<T>> for SharedWeakUnion<T>
where
    T: IntrusiveObject,
{
    fn from_strong(value: SharedIntrusive<T>) -> Self {
        SharedWeakUnion::from(value)
    }

    fn strong_clone(&self) -> Option<SharedIntrusive<T>> {
        let strong = self.get_strong();
        (!strong.is_null()).then_some(strong)
    }

    fn lock(&self) -> Option<SharedIntrusive<T>> {
        let strong = SharedWeakUnion::lock(self);
        (!strong.is_null()).then_some(strong)
    }

    fn is_strong(&self) -> bool {
        SharedWeakUnion::is_strong(self)
    }

    fn expired(&self) -> bool {
        SharedWeakUnion::expired(self)
    }

    fn convert_to_weak(&mut self) -> bool {
        SharedWeakUnion::convert_to_weak(self)
    }

    fn set_strong(&mut self, value: SharedIntrusive<T>) {
        *self = SharedWeakUnion::from(value);
    }

    fn use_count(&self) -> usize {
        SharedWeakUnion::use_count(self)
    }
}

#[derive(Debug)]
struct ValueEntry<T, P, SP> {
    ptr: P,
    last_access: Duration,
    marker: std::marker::PhantomData<(T, SP)>,
}

impl<T, P, SP> ValueEntry<T, P, SP>
where
    P: CachePointer<T, SP>,
{
    fn new(last_access: Duration, ptr: SP) -> Self {
        Self {
            ptr: P::from_strong(ptr),
            last_access,
            marker: std::marker::PhantomData,
        }
    }

    fn touch(&mut self, now: Duration) {
        self.last_access = now;
    }
}

#[derive(Debug)]
struct KeyOnlyEntry {
    last_access: Duration,
}

impl KeyOnlyEntry {
    fn new(last_access: Duration) -> Self {
        Self { last_access }
    }

    fn touch(&mut self, now: Duration) {
        self.last_access = now;
    }
}

#[derive(Debug)]
pub struct TaggedCacheState<K, T, P, SP, S> {
    cache_count: usize,
    cache: PartitionedUnorderedMap<K, ValueEntry<T, P, SP>, S>,
    hits: u64,
    misses: u64,
}

impl<K, T, P, SP, S> TaggedCacheState<K, T, P, SP, S>
where
    K: Eq + Hash + PartitionKey + Clone,
    P: CachePointer<T, SP>,
    SP: Clone,
    S: BuildHasher + Clone,
{
    fn initial_fetch<Q>(&mut self, key: &Q, now: Duration) -> Option<SP>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + PartitionKey + ?Sized,
    {
        let mut expired = false;
        let mut result = None;

        if let Some(entry) = self.cache.get_mut(key) {
            if entry.ptr.is_strong() {
                self.hits += 1;
                entry.touch(now);
                result = entry.ptr.strong_clone();
            } else if let Some(cached) = entry.ptr.lock() {
                self.cache_count += 1;
                entry.touch(now);
                entry.ptr.set_strong(cached.clone());
                result = Some(cached);
            } else {
                expired = true;
            }
        }

        if expired {
            self.cache.remove(key);
        }

        result
    }
}

#[derive(Debug)]
struct KeyCacheState<K, S> {
    cache: PartitionedUnorderedMap<K, KeyOnlyEntry, S>,
}

pub struct TaggedCache<
    K,
    T,
    C = MonotonicClock,
    S = HardenedHashBuilder,
    P = SharedWeakCachePointer<T>,
    SP = Arc<T>,
> {
    name: String,
    target_size: usize,
    target_age: Duration,
    clock: C,
    instrumentation: TaggedCacheInstrumentation,
    state: RecursiveMutex<TaggedCacheState<K, T, P, SP, S>>,
}

impl<K, T, C, S, P, SP> fmt::Debug for TaggedCache<K, T, C, S, P, SP>
where
    C: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TaggedCache")
            .field("name", &self.name)
            .field("target_size", &self.target_size)
            .field("target_age", &self.target_age)
            .field("clock", &self.clock)
            .finish_non_exhaustive()
    }
}

impl<K, T, C, P, SP> TaggedCache<K, T, C, HardenedHashBuilder, P, SP>
where
    K: Eq + Hash + PartitionKey + Clone + Send + Sync,
    C: CacheClock,
    P: CachePointer<T, SP>,
    SP: Clone + Send + Sync,
{
    pub fn new(name: impl Into<String>, size: usize, expiration: Duration, clock: C) -> Self {
        Self::with_hasher(
            name,
            size,
            expiration,
            clock,
            HardenedHashBuilder::default(),
        )
    }
}

impl<K, T, C, S, P, SP> TaggedCache<K, T, C, S, P, SP>
where
    K: Eq + Hash + PartitionKey + Clone + Send + Sync,
    C: CacheClock,
    P: CachePointer<T, SP>,
    SP: Clone + Send + Sync,
    S: BuildHasher + Clone,
{
    pub fn with_hasher(
        name: impl Into<String>,
        size: usize,
        expiration: Duration,
        clock: C,
        hasher: S,
    ) -> Self {
        Self {
            name: name.into(),
            target_size: size,
            target_age: expiration,
            clock,
            instrumentation: TaggedCacheInstrumentation::default(),
            state: RecursiveMutex::new(TaggedCacheState {
                cache_count: 0,
                cache: PartitionedUnorderedMap::with_hasher(None, hasher),
                hits: 0,
                misses: 0,
            }),
        }
    }

    pub fn with_instrumentation(
        name: impl Into<String>,
        size: usize,
        expiration: Duration,
        clock: C,
        hasher: S,
        metrics: Arc<dyn TaggedCacheMetrics>,
        logger: Arc<dyn TaggedCacheLogger>,
    ) -> Self {
        Self {
            name: name.into(),
            target_size: size,
            target_age: expiration,
            clock,
            instrumentation: TaggedCacheInstrumentation { metrics, logger },
            state: RecursiveMutex::new(TaggedCacheState {
                cache_count: 0,
                cache: PartitionedUnorderedMap::with_hasher(None, hasher),
                hits: 0,
                misses: 0,
            }),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn target_size(&self) -> usize {
        self.target_size
    }

    pub const fn target_age(&self) -> Duration {
        self.target_age
    }

    pub fn clock(&self) -> &C {
        &self.clock
    }

    /// Expose the cache mutex for callers that need the same lock ordering
    /// behavior as the reference `peekMutex()` seam.
    pub fn peek_mutex(&self) -> &RecursiveMutex<TaggedCacheState<K, T, P, SP, S>> {
        &self.state
    }

    pub fn size(&self) -> usize {
        self.get_track_size()
    }

    pub fn get_cache_size(&self) -> usize {
        self.state
            .lock()
            .expect("TaggedCache mutex must not be poisoned")
            .cache_count
    }

    pub fn get_track_size(&self) -> usize {
        self.state
            .lock()
            .expect("TaggedCache mutex must not be poisoned")
            .cache
            .len()
    }

    /// Returns the aggregate entry capacity reserved by the cache partitions.
    pub fn total_capacity(&self) -> usize {
        self.state
            .lock()
            .expect("TaggedCache mutex must not be poisoned")
            .cache
            .total_capacity()
    }

    pub fn get_hit_rate(&self) -> f32 {
        let state = self
            .state
            .lock()
            .expect("TaggedCache mutex must not be poisoned");
        let total = (state.hits + state.misses) as f32;
        state.hits as f32 * (100.0 / total.max(1.0))
    }

    pub fn rate(&self) -> f64 {
        let state = self
            .state
            .lock()
            .expect("TaggedCache mutex must not be poisoned");
        let total = state.hits + state.misses;
        if total == 0 {
            0.0
        } else {
            state.hits as f64 / total as f64
        }
    }

    pub fn metrics_snapshot(&self) -> TaggedCacheMetricsSnapshot {
        let state = self
            .state
            .lock()
            .expect("TaggedCache mutex must not be poisoned");
        let total = state.hits + state.misses;
        let hit_rate = if total == 0 {
            0
        } else {
            (state.hits * 100) / total
        };
        TaggedCacheMetricsSnapshot {
            size: state.cache_count,
            track_size: state.cache.len(),
            hit_rate,
            hits: state.hits,
            misses: state.misses,
        }
    }

    pub fn collect_metrics(&self) {
        let snapshot = self.metrics_snapshot();
        self.instrumentation.metrics.observe(&self.name, &snapshot);
    }

    pub fn clear(&self) {
        let mut state = self
            .state
            .lock()
            .expect("TaggedCache mutex must not be poisoned");
        state.cache.clear();
        state.cache_count = 0;
    }

    pub fn reset(&self) {
        let mut state = self
            .state
            .lock()
            .expect("TaggedCache mutex must not be poisoned");
        state.cache.clear();
        state.cache_count = 0;
        state.hits = 0;
        state.misses = 0;
    }

    pub fn touch_if_exists<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash + PartitionKey + ?Sized,
    {
        let mut state = self
            .state
            .lock()
            .expect("TaggedCache mutex must not be poisoned");
        if let Some(entry) = state.cache.get_mut(key) {
            entry.touch(self.clock.now());
            state.hits += 1;
            true
        } else {
            state.misses += 1;
            false
        }
    }

    pub fn sweep(&self) {
        let now = self.clock.now();
        let mut swept_pointers = Vec::new();
        let lock_hold_duration;
        {
            let mut state = self
                .state
                .lock()
                .expect("TaggedCache mutex must not be poisoned");
            let lock_hold_start = Instant::now();
            let when_expire =
                expiration_cutoff(now, self.target_age, self.target_size, state.cache.len());

            if self.target_size != 0 && state.cache.len() > self.target_size {
                self.instrumentation.logger.trace(&format!(
                    "{} is growing fast {} of {} aging at {:?} of {:?}",
                    self.name,
                    state.cache.len(),
                    self.target_size,
                    now - when_expire,
                    self.target_age
                ));
            }

            let track_before = state.cache.len();
            let strong_cache_before = state.cache_count;
            let capacity_before = state.cache.total_capacity();
            let mut all_counts = SweepCounts::default();
            for partition in state.cache.map_mut() {
                let (counts, mut removed, _keys) = sweep_value_partition(partition, when_expire);
                if counts.cache_removals != 0 || counts.map_removals != 0 {
                    self.instrumentation.logger.debug(&format!(
                        "TaggedCache partition sweep {}: cache = {}-{}, map-={}",
                        self.name,
                        partition.len(),
                        counts.cache_removals,
                        counts.map_removals
                    ));
                }
                all_counts.cache_removals += counts.cache_removals;
                all_counts.map_removals += counts.map_removals;
                all_counts.strong_removals += counts.strong_removals;
                all_counts.strong_demotions += counts.strong_demotions;
                all_counts.expired_weak_removals += counts.expired_weak_removals;
                swept_pointers.append(&mut removed);
            }

            state.cache_count = state.cache_count.saturating_sub(all_counts.cache_removals);
            let capacity_entries_released = if all_counts.map_removals != 0 {
                state.cache.shrink_if_sparse()
            } else {
                0
            };
            let capacity_after = state.cache.total_capacity();
            tracing::info!(
                target: "cache_retention",
                event = "tagged_cache_sweep",
                cache_name = self.name.as_str(),
                target_size = self.target_size,
                target_age_seconds = self.target_age.whole_seconds(),
                track_before,
                track_after = state.cache.len(),
                strong_cache_before,
                strong_cache_after = state.cache_count,
                capacity_before,
                capacity_after,
                capacity_entries_released,
                aged_strong_removals = all_counts.strong_removals,
                aged_strong_demotions_to_weak = all_counts.strong_demotions,
                expired_weak_removals = all_counts.expired_weak_removals,
                "TaggedCache retention sweep completed"
            );
            lock_hold_duration = lock_hold_start.elapsed();
        }
        // Match the reference `stuffToSweep` lifetime: removed values are destroyed
        // after the cache lock is released, but before the final duration log.
        drop(swept_pointers);
        self.instrumentation.logger.debug(&format!(
            "{} TaggedCache sweep lock hold duration {}ms",
            self.name,
            lock_hold_duration.as_millis()
        ));
    }

    pub fn del<Q>(&self, key: &Q, valid: bool) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash + PartitionKey + ?Sized,
    {
        let mut state = self
            .state
            .lock()
            .expect("TaggedCache mutex must not be poisoned");

        let mut decrement_cache_count = false;
        let remove_entry;
        let mut removed_from_cache = false;
        if let Some(entry) = state.cache.get_mut(key) {
            if entry.ptr.is_strong() {
                entry.ptr.convert_to_weak();
                decrement_cache_count = true;
                removed_from_cache = true;
            }
            remove_entry = !valid || entry.ptr.expired();
        } else {
            return false;
        }

        if decrement_cache_count {
            state.cache_count = state.cache_count.saturating_sub(1);
        }

        if remove_entry {
            state.cache.remove(key);
        }

        removed_from_cache
    }

    pub fn fetch<Q>(&self, key: &Q) -> Option<SP>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + PartitionKey + ?Sized,
    {
        // rippled's TaggedCache::initialFetch always refreshes lastAccess on
        // every hit (TaggedCache.ipp:724). Always use the primary recursively
        // locked map so active entries retain that refresh before sweeping.
        let mut state = self
            .state
            .lock()
            .expect("TaggedCache mutex must not be poisoned");
        let result = state.initial_fetch(key, self.clock.now());
        if result.is_none() {
            state.misses += 1;
        }
        result
    }

    pub fn fetch_with(&self, key: &K, handler: impl FnOnce() -> Option<SP>) -> Option<SP> {
        // Like fetch(), use the primary recursively locked map so every
        // cached hit refreshes last_access, matching rippled behavior.
        {
            let mut state = self
                .state
                .lock()
                .expect("TaggedCache mutex must not be poisoned");
            if let Some(found) = state.initial_fetch(key, self.clock.now()) {
                return Some(found);
            }
        }

        let created = handler()?;
        let now = self.clock.now();
        let mut state = self
            .state
            .lock()
            .expect("TaggedCache mutex must not be poisoned");
        state.misses += 1;
        if let Some(entry) = state.cache.get_mut(key) {
            entry.touch(now);
            return entry.ptr.strong_clone();
        }

        state
            .cache
            .insert(key.clone(), ValueEntry::new(now, created.clone()));
        state.cache_count += 1;
        Some(created)
    }

    pub fn canonicalize_replace_cache(&self, key: &K, data: &SP) -> bool {
        let mut cloned = data.clone();
        self.canonicalize_with(key, &mut cloned, |_| true)
    }

    pub fn canonicalize_replace_client(&self, key: &K, data: &mut SP) -> bool {
        self.canonicalize_with(key, data, |_| false)
    }

    pub fn canonicalize_with<R>(&self, key: &K, data: &mut SP, replace_callback: R) -> bool
    where
        R: FnOnce(Option<SP>) -> bool,
    {
        let mut state = self
            .state
            .lock()
            .expect("TaggedCache mutex must not be poisoned");

        let mut replace_callback = Some(replace_callback);
        if let Some(entry) = state.cache.get_mut(key) {
            entry.touch(self.clock.now());

            if entry.ptr.is_strong() {
                let cached = entry
                    .ptr
                    .strong_clone()
                    .expect("cached entry should carry a strong pointer");
                if replace_callback
                    .take()
                    .expect("replace callback should run once")(Some(
                    cached.clone(),
                )) {
                    entry.ptr.set_strong(data.clone());
                } else {
                    *data = cached;
                }
                return true;
            }

            if let Some(cached) = entry.ptr.lock() {
                if replace_callback
                    .take()
                    .expect("replace callback should run once")(Some(
                    cached.clone(),
                )) {
                    entry.ptr.set_strong(data.clone());
                } else {
                    entry.ptr.set_strong(cached.clone());
                    *data = cached;
                }

                state.cache_count += 1;
                return true;
            }

            entry.ptr.set_strong(data.clone());
            state.cache_count += 1;
            return false;
        }

        state
            .cache
            .insert(key.clone(), ValueEntry::new(self.clock.now(), data.clone()));
        state.cache_count += 1;
        false
    }

    pub fn insert(&self, key: K, value: T) -> bool
    where
        SP: CacheStrongPointer<T>,
    {
        let mut pointer = SP::from_value(value);
        self.canonicalize_replace_client(&key, &mut pointer)
    }

    pub fn retrieve<Q>(&self, key: &Q) -> Option<T>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + PartitionKey + ?Sized,
        SP: Deref<Target = T>,
        T: Clone,
    {
        self.fetch(key).map(|value| (*value).clone())
    }

    pub fn get_keys(&self) -> Vec<K> {
        // Pre-allocate outside the lock to avoid blocking other threads
        // during potentially expensive heap allocation (rippled parity:
        // TaggedCache::getKeys() memory outside of lock).
        let mut capacity = 0;
        loop {
            let mut result = Vec::with_capacity(capacity);
            let guard = self
                .state
                .lock()
                .expect("TaggedCache mutex must not be poisoned");
            let len = guard.cache.len();
            if result.capacity() >= len {
                result.extend(guard.cache.iter().map(|(key, _)| key.clone()));
                return result;
            }
            // Capacity too small — drop the lock, grow, retry.
            drop(guard);
            capacity = len + len / 4; // 25% headroom for concurrent inserts
        }
    }
}

#[derive(Debug)]
pub struct KeyCache<K, C = MonotonicClock, S = HardenedHashBuilder> {
    name: String,
    target_size: usize,
    target_age: Duration,
    clock: C,
    instrumentation: TaggedCacheInstrumentation,
    state: Mutex<KeyCacheState<K, S>>,
}

impl<K, C> KeyCache<K, C, HardenedHashBuilder>
where
    K: Eq + Hash + PartitionKey + Clone,
    C: CacheClock,
{
    pub fn new(name: impl Into<String>, size: usize, expiration: Duration, clock: C) -> Self {
        Self::with_hasher(
            name,
            size,
            expiration,
            clock,
            HardenedHashBuilder::default(),
        )
    }
}

impl<K, C, S> KeyCache<K, C, S>
where
    K: Eq + Hash + PartitionKey + Clone,
    C: CacheClock,
    S: BuildHasher + Clone,
{
    pub fn with_hasher(
        name: impl Into<String>,
        size: usize,
        expiration: Duration,
        clock: C,
        hasher: S,
    ) -> Self {
        Self {
            name: name.into(),
            target_size: size,
            target_age: expiration,
            clock,
            instrumentation: TaggedCacheInstrumentation::default(),
            state: Mutex::new(KeyCacheState {
                cache: PartitionedUnorderedMap::with_hasher(None, hasher),
            }),
        }
    }

    pub fn with_instrumentation(
        name: impl Into<String>,
        size: usize,
        expiration: Duration,
        clock: C,
        hasher: S,
        logger: Arc<dyn TaggedCacheLogger>,
    ) -> Self {
        Self {
            name: name.into(),
            target_size: size,
            target_age: expiration,
            clock,
            instrumentation: TaggedCacheInstrumentation {
                logger,
                ..TaggedCacheInstrumentation::default()
            },
            state: Mutex::new(KeyCacheState {
                cache: PartitionedUnorderedMap::with_hasher(None, hasher),
            }),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn clock(&self) -> &C {
        &self.clock
    }

    pub fn size(&self) -> usize {
        self.state
            .lock()
            .expect("KeyCache mutex must not be poisoned")
            .cache
            .len()
    }

    /// Returns the aggregate entry capacity reserved by the cache partitions.
    pub fn total_capacity(&self) -> usize {
        self.state
            .lock()
            .expect("KeyCache mutex must not be poisoned")
            .cache
            .total_capacity()
    }

    pub fn clear(&self) {
        self.state
            .lock()
            .expect("KeyCache mutex must not be poisoned")
            .cache
            .clear();
    }

    pub fn insert(&self, key: K) -> bool {
        let now = self.clock.now();
        let mut state = self
            .state
            .lock()
            .expect("KeyCache mutex must not be poisoned");
        if let Some(entry) = state.cache.get_mut(&key) {
            entry.last_access = now;
            false
        } else {
            state.cache.insert(key, KeyOnlyEntry::new(now));
            true
        }
    }

    pub fn touch_if_exists<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash + PartitionKey + ?Sized,
    {
        let mut state = self
            .state
            .lock()
            .expect("KeyCache mutex must not be poisoned");
        if let Some(entry) = state.cache.get_mut(key) {
            entry.touch(self.clock.now());
            true
        } else {
            false
        }
    }

    pub fn sweep(&self) {
        let now = self.clock.now();
        let mut state = self
            .state
            .lock()
            .expect("KeyCache mutex must not be poisoned");
        let lock_hold_start = Instant::now();
        let when_expire =
            expiration_cutoff(now, self.target_age, self.target_size, state.cache.len());

        if self.target_size != 0 && state.cache.len() > self.target_size {
            self.instrumentation.logger.trace(&format!(
                "{} is growing fast {} of {} aging at {:?} of {:?}",
                self.name,
                state.cache.len(),
                self.target_size,
                now - when_expire,
                self.target_age
            ));
        }

        let track_before = state.cache.len();
        let capacity_before = state.cache.total_capacity();
        let mut all_counts = SweepCounts::default();
        for partition in state.cache.map_mut() {
            let counts = sweep_key_partition(partition, when_expire, now);
            if counts.cache_removals != 0 || counts.map_removals != 0 {
                self.instrumentation.logger.debug(&format!(
                    "TaggedCache partition sweep {}: cache = {}-{}, map-={}",
                    self.name,
                    partition.len(),
                    counts.cache_removals,
                    counts.map_removals
                ));
            }
            all_counts.cache_removals += counts.cache_removals;
            all_counts.map_removals += counts.map_removals;
        }
        let capacity_entries_released = if all_counts.map_removals != 0 {
            state.cache.shrink_if_sparse()
        } else {
            0
        };
        let capacity_after = state.cache.total_capacity();
        tracing::info!(
            target: "cache_retention",
            event = "key_cache_sweep",
            cache_name = self.name.as_str(),
            target_size = self.target_size,
            target_age_seconds = self.target_age.whole_seconds(),
            track_before,
            track_after = state.cache.len(),
            capacity_before,
            capacity_after,
            capacity_entries_released,
            aged_key_removals = all_counts.map_removals,
            "KeyCache retention sweep completed"
        );
        // Compaction runs after all removals and performs at most one shrink per
        // partition. Logging its in-lock cost makes any allocator stall visible.
        self.instrumentation.logger.debug(&format!(
            "{} KeyCache sweep lock hold duration {}ms",
            self.name,
            lock_hold_start.elapsed().as_millis()
        ));
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct SweepCounts {
    cache_removals: usize,
    map_removals: usize,
    /// Aged strong entries whose cache reference was the final strong owner.
    strong_removals: usize,
    /// Aged strong entries converted to weak because another owner remains.
    strong_demotions: usize,
    /// Weak tracking entries removed after their final external owner released.
    expired_weak_removals: usize,
}

fn sweep_value_partition<K, T, P, SP, S>(
    partition: &mut StdHashMap<K, ValueEntry<T, P, SP>, S>,
    when_expire: Duration,
) -> (SweepCounts, Vec<P>, Vec<K>)
where
    K: Clone + Eq + Hash,
    P: CachePointer<T, SP>,
    S: BuildHasher,
{
    let mut counts = SweepCounts::default();
    let mut keys_to_remove = Vec::new();
    let mut swept = Vec::new();

    for (key, entry) in partition.iter_mut() {
        if entry.ptr.is_weak() {
            if entry.ptr.expired() {
                counts.map_removals += 1;
                counts.expired_weak_removals += 1;
                keys_to_remove.push(key.clone());
            }
        } else if entry.last_access <= when_expire {
            counts.cache_removals += 1;
            if entry.ptr.use_count() == 1 {
                counts.map_removals += 1;
                counts.strong_removals += 1;
                keys_to_remove.push(key.clone());
            } else {
                counts.strong_demotions += 1;
                entry.ptr.convert_to_weak();
            }
        }
    }

    for key in &keys_to_remove {
        if let Some(entry) = partition.remove(key) {
            swept.push(entry.ptr);
        }
    }

    (counts, swept, Vec::new())
}

fn sweep_key_partition<K, S>(
    partition: &mut StdHashMap<K, KeyOnlyEntry, S>,
    when_expire: Duration,
    now: Duration,
) -> SweepCounts
where
    S: BuildHasher,
{
    let mut counts = SweepCounts::default();
    partition.retain(|_, entry| {
        if entry.last_access > now {
            entry.last_access = now;
            true
        } else {
            let keep = entry.last_access > when_expire;
            if !keep {
                counts.map_removals += 1;
            }
            keep
        }
    });
    counts
}

fn expiration_cutoff(
    now: Duration,
    target_age: Duration,
    target_size: usize,
    size: usize,
) -> Duration {
    if target_size == 0 || size <= target_size {
        now - target_age
    } else {
        let mut effective_age = scale_duration(target_age, target_size, size);
        let minimum_age = Duration::seconds(1);
        if effective_age < minimum_age {
            effective_age = minimum_age;
        }
        now - effective_age
    }
}

fn scale_duration(duration: Duration, numerator: usize, denominator: usize) -> Duration {
    let nanos = duration.whole_nanoseconds();
    Duration::nanoseconds_i128(nanos * numerator as i128 / denominator as i128)
}

#[cfg(test)]
mod tests {
    use super::{
        KeyCache, ManualClock, TaggedCache, TaggedCacheLogger, TaggedCacheMetrics,
        TaggedCacheMetricsSnapshot,
    };
    use crate::intrusive_pointer::{
        IntrusiveObject, SharedIntrusive, SharedWeakUnion, make_shared_intrusive,
    };
    use crate::intrusive_ref_counts::IntrusiveRefCounts;
    use crate::mutex::RecursiveMutex;
    use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
    use std::sync::{Arc, Mutex};
    use time::Duration;

    #[derive(Debug, Default)]
    struct RecordingMetrics {
        snapshots: Mutex<Vec<(String, TaggedCacheMetricsSnapshot)>>,
    }

    impl TaggedCacheMetrics for RecordingMetrics {
        fn observe(&self, name: &str, snapshot: &TaggedCacheMetricsSnapshot) {
            self.snapshots
                .lock()
                .expect("metrics mutex must not be poisoned")
                .push((name.to_owned(), snapshot.clone()));
        }
    }

    #[derive(Debug, Default)]
    struct RecordingLogger {
        traces: Mutex<Vec<String>>,
        debugs: Mutex<Vec<String>>,
    }

    impl TaggedCacheLogger for RecordingLogger {
        fn trace(&self, message: &str) {
            self.traces
                .lock()
                .expect("trace mutex must not be poisoned")
                .push(message.to_owned());
        }

        fn debug(&self, message: &str) {
            self.debugs
                .lock()
                .expect("debug mutex must not be poisoned")
                .push(message.to_owned());
        }
    }

    #[derive(Debug)]
    struct DropOrderingLogger {
        dropped: Arc<AtomicBool>,
    }

    impl TaggedCacheLogger for DropOrderingLogger {
        fn trace(&self, _message: &str) {}

        fn debug(&self, message: &str) {
            if message.contains("partition sweep") {
                assert!(!self.dropped.load(Ordering::SeqCst));
            }
            if message.contains("sweep lock hold duration") {
                assert!(self.dropped.load(Ordering::SeqCst));
            }
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum IntrusiveLifecycle {
        Alive = 1,
        PartiallyDeleted = 2,
        Deleted = 3,
    }

    impl IntrusiveLifecycle {
        fn load(state: &AtomicU8) -> Self {
            match state.load(Ordering::SeqCst) {
                1 => Self::Alive,
                2 => Self::PartiallyDeleted,
                3 => Self::Deleted,
                other => panic!("unexpected intrusive lifecycle state: {other}"),
            }
        }
    }

    #[derive(Debug)]
    struct IntrusiveTracker {
        lifecycle: AtomicU8,
    }

    impl IntrusiveTracker {
        fn new() -> Self {
            Self {
                lifecycle: AtomicU8::new(IntrusiveLifecycle::Alive as u8),
            }
        }
    }

    #[derive(Debug)]
    struct IntrusiveCacheNode {
        ref_counts: IntrusiveRefCounts,
        tracker: Arc<IntrusiveTracker>,
        value: u32,
    }

    impl IntrusiveCacheNode {
        fn new(tracker: Arc<IntrusiveTracker>, value: u32) -> Self {
            Self {
                ref_counts: IntrusiveRefCounts::new(),
                tracker,
                value,
            }
        }
    }

    impl IntrusiveObject for IntrusiveCacheNode {
        fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
            &self.ref_counts
        }

        fn partial_destructor(&self) {
            self.tracker
                .lifecycle
                .store(IntrusiveLifecycle::PartiallyDeleted as u8, Ordering::SeqCst);
        }
    }

    impl Drop for IntrusiveCacheNode {
        fn drop(&mut self) {
            self.tracker
                .lifecycle
                .store(IntrusiveLifecycle::Deleted as u8, Ordering::SeqCst);
        }
    }

    #[test]
    fn tagged_cache_test_cases() {
        let clock = ManualClock::new(0);
        let cache = TaggedCache::<u32, String, _>::new("test", 1, Duration::seconds(1), clock);

        assert_eq!(cache.get_cache_size(), 0);
        assert_eq!(cache.get_track_size(), 0);
        assert!(!cache.insert(1, String::from("one")));
        assert_eq!(cache.get_cache_size(), 1);
        assert_eq!(cache.get_track_size(), 1);
        assert_eq!(cache.retrieve(&1), Some(String::from("one")));

        cache.clock.advance_seconds(1);
        cache.sweep();
        assert_eq!(cache.get_cache_size(), 0);
        assert_eq!(cache.get_track_size(), 0);

        assert!(!cache.insert(2, String::from("two")));
        let kept = cache.fetch(&2).expect("value should exist");
        cache.clock.advance_seconds(1);
        cache.sweep();
        assert_eq!(cache.get_cache_size(), 0);
        assert_eq!(cache.get_track_size(), 1);
        drop(kept);
        cache.clock.advance_seconds(1);
        cache.sweep();
        assert_eq!(cache.get_track_size(), 0);

        assert!(!cache.insert(3, String::from("three")));
        {
            let first = cache.fetch(&3).expect("cached value should exist");
            let mut second = Arc::new(String::from("three"));
            assert!(cache.canonicalize_replace_client(&3, &mut second));
            assert!(Arc::ptr_eq(&first, &second));
        }
        cache.clock.advance_seconds(1);
        cache.sweep();
        assert_eq!(cache.get_track_size(), 0);

        assert!(!cache.insert(4, String::from("four")));
        let original = cache.fetch(&4).expect("cached value should exist");
        cache.clock.advance_seconds(1);
        cache.sweep();
        assert_eq!(cache.get_cache_size(), 0);
        assert_eq!(cache.get_track_size(), 1);

        let mut replacement = Arc::new(String::from("four"));
        assert!(cache.canonicalize_replace_client(&4, &mut replacement));
        assert_eq!(cache.get_cache_size(), 1);
        assert_eq!(cache.get_track_size(), 1);
        assert!(Arc::ptr_eq(&original, &replacement));
    }

    #[test]
    fn key_cache_test_cases() {
        let clock = ManualClock::new(0);
        let cache = KeyCache::<String, _>::new("test", 1, Duration::seconds(2), clock);

        assert_eq!(cache.size(), 0);
        assert!(cache.insert(String::from("one")));
        assert!(!cache.insert(String::from("one")));
        assert_eq!(cache.size(), 1);
        assert!(cache.touch_if_exists("one"));
        cache.clock.advance_seconds(1);
        cache.sweep();
        assert_eq!(cache.size(), 1);
        cache.clock.advance_seconds(1);
        cache.sweep();
        assert_eq!(cache.size(), 0);
        assert!(!cache.touch_if_exists("one"));
    }

    #[test]
    fn key_cache_scales_expiration_when_over_target_size() {
        let clock = ManualClock::new(0);
        let cache = KeyCache::<String, _>::new("test", 2, Duration::seconds(3), clock);

        assert!(cache.insert(String::from("one")));
        cache.clock.advance_seconds(1);
        assert!(cache.insert(String::from("two")));
        cache.clock.advance_seconds(1);
        assert!(cache.insert(String::from("three")));
        cache.clock.advance_seconds(1);

        assert_eq!(cache.size(), 3);
        cache.sweep();
        assert!(cache.size() < 3);
    }

    #[test]
    fn tagged_cache_sweep_compacts_sparse_partitions_and_preserves_survivors() {
        let partitions = std::thread::available_parallelism()
            .map(|parallelism| parallelism.get())
            .unwrap_or(1);
        let entry_count = partitions * 2_048;
        let survivor_count = partitions * 4;
        let clock = ManualClock::new(0);
        let cache =
            TaggedCache::<usize, String, _>::new("compaction", 0, Duration::seconds(2), clock);

        for key in 0..entry_count {
            assert!(!cache.insert(key, key.to_string()));
        }
        cache.clock.advance_seconds(1);
        let survivors = (0..survivor_count)
            .map(|key| cache.fetch(&key).expect("surviving entry should exist"))
            .collect::<Vec<_>>();
        let capacity_before = cache.total_capacity();

        cache.clock.advance_seconds(1);
        cache.sweep();
        let capacity_after = cache.total_capacity();

        assert_eq!(cache.get_track_size(), survivor_count);
        assert!(
            capacity_after * 2 < capacity_before,
            "capacity should fall substantially: {capacity_before} -> {capacity_after}"
        );
        for (key, value) in survivors.iter().enumerate() {
            assert_eq!(value.as_str(), key.to_string());
            let fetched = cache
                .fetch(&key)
                .expect("surviving entry should remain fetchable");
            assert!(Arc::ptr_eq(value, &fetched));
        }
    }

    #[test]
    fn key_cache_sweep_compacts_sparse_partitions_and_preserves_survivors() {
        let partitions = std::thread::available_parallelism()
            .map(|parallelism| parallelism.get())
            .unwrap_or(1);
        let entry_count = partitions * 2_048;
        let survivor_count = partitions * 4;
        let clock = ManualClock::new(0);
        let cache = KeyCache::<usize, _>::new("compaction", 0, Duration::seconds(2), clock);

        for key in 0..entry_count {
            assert!(cache.insert(key));
        }
        cache.clock.advance_seconds(1);
        for key in 0..survivor_count {
            assert!(cache.touch_if_exists(&key));
        }
        let capacity_before = cache.total_capacity();

        cache.clock.advance_seconds(1);
        cache.sweep();
        let capacity_after = cache.total_capacity();

        assert_eq!(cache.size(), survivor_count);
        assert!(
            capacity_after * 2 < capacity_before,
            "capacity should fall substantially: {capacity_before} -> {capacity_after}"
        );
        for key in 0..survivor_count {
            assert!(cache.touch_if_exists(&key));
        }
    }

    #[test]
    fn fetch_with_reuses_cached_value_and_only_builds_once() {
        let clock = ManualClock::new(0);
        let cache = TaggedCache::<u32, String, _>::new("test", 1, Duration::seconds(1), clock);
        let builds = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));

        let first = cache
            .fetch_with(&1, {
                let builds = std::sync::Arc::clone(&builds);
                move || {
                    builds.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    Some(std::sync::Arc::new(String::from("one")))
                }
            })
            .expect("handler should create value");

        let second = cache
            .fetch_with(&1, {
                let builds = std::sync::Arc::clone(&builds);
                move || {
                    builds.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    Some(std::sync::Arc::new(String::from("two")))
                }
            })
            .expect("cached value should be reused");

        assert!(std::sync::Arc::ptr_eq(&first, &second));
        assert_eq!(builds.load(std::sync::atomic::Ordering::SeqCst), 1);
    }

    #[test]
    fn delete_and_reset_update_cache_state() {
        let clock = ManualClock::new(0);
        let cache = TaggedCache::<u32, String, _>::new("test", 1, Duration::seconds(1), clock);

        assert!(!cache.insert(1, String::from("one")));
        assert_eq!(cache.get_cache_size(), 1);
        assert!(cache.del(&1, false));
        assert_eq!(cache.get_cache_size(), 0);
        assert_eq!(cache.get_track_size(), 0);

        assert!(!cache.insert(2, String::from("two")));
        let _ = cache.fetch(&2);
        assert!(cache.get_hit_rate() > 0.0);
        cache.reset();
        assert_eq!(cache.get_cache_size(), 0);
        assert_eq!(cache.get_track_size(), 0);
        assert_eq!(cache.get_hit_rate(), 0.0);
        assert_eq!(cache.rate(), 0.0);
    }

    #[test]
    fn replace_cache_and_get_keys_expose_current_entries() {
        let clock = ManualClock::new(0);
        let cache = TaggedCache::<u32, String, _>::new("test", 2, Duration::seconds(1), clock);

        let original = std::sync::Arc::new(String::from("one"));
        assert!(!cache.canonicalize_replace_cache(&1, &original));

        let replacement = std::sync::Arc::new(String::from("uno"));
        assert!(cache.canonicalize_replace_cache(&1, &replacement));

        let fetched = cache.fetch(&1).expect("value should exist");
        assert!(std::sync::Arc::ptr_eq(&fetched, &replacement));

        let mut keys = cache.get_keys();
        keys.sort_unstable();
        assert_eq!(keys, vec![1]);

        cache.clear();
        assert!(cache.get_keys().is_empty());
    }

    #[test]
    fn tagged_cache_supports_intrusive_pointer_policy() {
        let clock = ManualClock::new(0);
        let cache = TaggedCache::<
            u32,
            IntrusiveCacheNode,
            _,
            _,
            SharedWeakUnion<IntrusiveCacheNode>,
            SharedIntrusive<IntrusiveCacheNode>,
        >::new("intrusive", 1, Duration::seconds(1), clock);
        let tracker = Arc::new(IntrusiveTracker::new());

        assert!(!cache.insert(1, IntrusiveCacheNode::new(Arc::clone(&tracker), 7)));
        let kept = cache.fetch(&1).expect("value should exist");
        assert_eq!(kept.value, 7);

        cache.clock.advance_seconds(1);
        cache.sweep();
        assert_eq!(cache.get_cache_size(), 0);
        assert_eq!(cache.get_track_size(), 1);
        assert_eq!(
            IntrusiveLifecycle::load(&tracker.lifecycle),
            IntrusiveLifecycle::Alive
        );

        let fetched_again = cache.fetch(&1).expect("weak cache entry should relock");
        assert_eq!(fetched_again.value, 7);
        assert_eq!(cache.get_cache_size(), 1);

        drop(fetched_again);
        drop(kept);

        cache.clock.advance_seconds(1);
        cache.sweep();
        assert_eq!(cache.get_track_size(), 0);
        assert_eq!(
            IntrusiveLifecycle::load(&tracker.lifecycle),
            IntrusiveLifecycle::Deleted
        );

        let standalone = make_shared_intrusive(IntrusiveCacheNode::new(tracker, 9));
        let mut pointer = SharedWeakUnion::from(standalone);
        assert!(pointer.convert_to_weak());
        assert!(pointer.expired() || pointer.lock().value == 9);
    }

    #[test]
    fn primary_cache_lifecycle_refreshes_fetches_and_tracks_metrics() {
        let clock = ManualClock::new(0);
        let cache = TaggedCache::<u32, String, _>::new("primary", 2, Duration::seconds(2), clock);

        let mut canonical = Arc::new(String::from("one"));
        assert!(!cache.canonicalize_replace_client(&1, &mut canonical));

        cache.clock.advance_seconds(1);
        let fetched = cache.fetch(&1).expect("canonical entry should be fetched");
        assert!(Arc::ptr_eq(&canonical, &fetched));

        // At t=2, the t=0 insertion is at the sweep cutoff. The t=1 fetch
        // must have refreshed last_access or the entry would be demoted.
        cache.clock.advance_seconds(1);
        cache.sweep();
        assert_eq!(cache.get_cache_size(), 1);
        assert_eq!(cache.get_track_size(), 1);

        let mut canonical_with = Arc::new(String::from("two"));
        assert!(!cache.canonicalize_replace_client(&2, &mut canonical_with));
        cache.clock.advance_seconds(1);
        let fetched_with = cache
            .fetch_with(&2, || panic!("cached fetch_with must not call its handler"))
            .expect("canonical entry should be fetched without rebuilding");
        assert!(Arc::ptr_eq(&canonical_with, &fetched_with));

        // At t=4, key 2 is at the same expiry boundary. Its cached fetch_with
        // must retain a strong cache entry; key 1 is now old enough to demote.
        cache.clock.advance_seconds(1);
        cache.sweep();
        assert_eq!(cache.get_cache_size(), 1);
        assert_eq!(cache.get_track_size(), 2);

        let mut duplicate = Arc::new(String::from("one"));
        assert!(cache.canonicalize_replace_client(&1, &mut duplicate));
        assert!(Arc::ptr_eq(&duplicate, &fetched));
        assert!(cache.del(&1, true));
        assert_eq!(cache.get_cache_size(), 1);
        assert_eq!(cache.get_track_size(), 2);

        drop(duplicate);
        drop(fetched);
        drop(canonical);
        cache.sweep();
        assert_eq!(cache.get_cache_size(), 1);
        assert_eq!(cache.get_track_size(), 1);

        drop(fetched_with);
        drop(canonical_with);
        cache.clock.advance_seconds(2);
        cache.sweep();
        assert_eq!(cache.get_cache_size(), 0);
        assert_eq!(cache.get_track_size(), 0);

        let snapshot = cache.metrics_snapshot();
        assert_eq!(snapshot.hits(), 2);
        assert_eq!(snapshot.misses(), 0);
        assert_eq!(snapshot.hit_rate(), 100);
        assert_eq!(cache.get_hit_rate(), 100.0);
        assert_eq!(cache.rate(), 1.0);
    }

    #[test]
    fn touch_and_collect_metrics_match_cpp_stats_role() {
        let clock = ManualClock::new(0);
        let metrics = Arc::new(RecordingMetrics::default());
        let cache = TaggedCache::<u32, String, _>::with_instrumentation(
            "metrics",
            1,
            Duration::seconds(1),
            clock,
            crate::hardened_hash::HardenedHashBuilder::default(),
            metrics.clone(),
            Arc::new(RecordingLogger::default()),
        );

        assert!(!cache.insert(1, String::from("one")));
        assert!(cache.touch_if_exists(&1));
        assert!(!cache.touch_if_exists(&2));
        let _ = cache.fetch(&1);
        let _ = cache.fetch(&3);

        let snapshot = cache.metrics_snapshot();
        assert_eq!(snapshot.size(), 1);
        assert_eq!(snapshot.track_size(), 1);
        assert_eq!(snapshot.hits(), 2);
        assert_eq!(snapshot.misses(), 2);
        assert_eq!(snapshot.hit_rate(), 50);

        cache.collect_metrics();
        let observed = metrics
            .snapshots
            .lock()
            .expect("metrics mutex must not be poisoned");
        assert_eq!(observed.len(), 1);
        assert_eq!(observed[0].0, "metrics");
        assert_eq!(observed[0].1, snapshot);
    }

    #[test]
    fn sweep_emits_growth_and_partition_logs() {
        let clock = ManualClock::new(0);
        let logger = Arc::new(RecordingLogger::default());
        let cache = TaggedCache::<u32, String, _>::with_instrumentation(
            "logs",
            1,
            Duration::seconds(3),
            clock,
            crate::hardened_hash::HardenedHashBuilder::default(),
            Arc::new(RecordingMetrics::default()),
            logger.clone(),
        );

        assert!(!cache.insert(1, String::from("one")));
        cache.clock.advance_seconds(1);
        assert!(!cache.insert(2, String::from("two")));
        cache.clock.advance_seconds(1);
        assert!(!cache.insert(3, String::from("three")));
        cache.clock.advance_seconds(1);
        cache.sweep();

        let traces = logger
            .traces
            .lock()
            .expect("trace mutex must not be poisoned");
        let debugs = logger
            .debugs
            .lock()
            .expect("debug mutex must not be poisoned");
        assert!(traces.iter().any(|line| line.contains("is growing fast")));
        assert!(
            debugs
                .iter()
                .any(|line| line.contains("TaggedCache sweep lock hold duration"))
        );
    }

    #[test]
    fn canonicalize_with_can_choose_cached_or_new_pointer() {
        let clock = ManualClock::new(0);
        let cache = TaggedCache::<u32, String, _>::new("test", 1, Duration::seconds(1), clock);

        let first = Arc::new(String::from("one"));
        assert!(!cache.canonicalize_replace_cache(&1, &first));

        let mut second = Arc::new(String::from("one"));
        let saw_cached = cache.canonicalize_with(&1, &mut second, |cached| {
            let cached = cached.expect("cached entry should be visible to the decision callback");
            Arc::ptr_eq(&cached, &first)
        });
        assert!(saw_cached);
        assert!(!Arc::ptr_eq(&second, &first));

        let fetched = cache.fetch(&1).expect("replacement should stay cached");
        assert!(Arc::ptr_eq(&fetched, &second));

        let mut third = Arc::new(String::from("one"));
        let reused = cache.canonicalize_with(&1, &mut third, |_| false);
        assert!(reused);
        assert!(Arc::ptr_eq(&third, &second));
    }

    #[test]
    fn sweep_drops_removed_values_after_releasing_the_cache_lock() {
        struct DropProbe {
            on_drop: Box<dyn Fn() + Send + Sync>,
        }

        impl Drop for DropProbe {
            fn drop(&mut self) {
                (self.on_drop)();
            }
        }

        type DropProbeState = super::TaggedCacheState<
            u32,
            DropProbe,
            crate::shared_weak_cache_pointer::SharedWeakCachePointer<DropProbe>,
            Arc<DropProbe>,
            crate::hardened_hash::HardenedHashBuilder,
        >;

        let clock = ManualClock::new(0);
        let cache = Box::pin(TaggedCache::<u32, DropProbe, _>::new(
            "test",
            1,
            Duration::seconds(1),
            clock,
        ));
        let lock_was_available = Arc::new(AtomicBool::new(false));
        let mutex_addr: usize =
            cache.as_ref().get_ref().peek_mutex() as *const RecursiveMutex<DropProbeState> as usize;

        let probe = DropProbe {
            on_drop: Box::new({
                let lock_was_available = Arc::clone(&lock_was_available);
                move || {
                    let lock_result = unsafe {
                        (&*(mutex_addr as *const RecursiveMutex<DropProbeState>))
                            .try_lock()
                            .is_ok()
                    };
                    lock_was_available.store(lock_result, Ordering::SeqCst);
                }
            }),
        };

        assert!(!cache.insert(1, probe));
        cache.clock.advance_seconds(1);
        cache.sweep();

        assert_eq!(cache.get_track_size(), 0);
        assert!(lock_was_available.load(Ordering::SeqCst));
    }

    #[test]
    fn sweep_drops_removed_values_before_duration_logging() {
        struct DropProbe {
            dropped: Arc<AtomicBool>,
        }

        impl Drop for DropProbe {
            fn drop(&mut self) {
                self.dropped.store(true, Ordering::SeqCst);
            }
        }

        let dropped = Arc::new(AtomicBool::new(false));
        let logger = Arc::new(DropOrderingLogger {
            dropped: Arc::clone(&dropped),
        });
        let cache = TaggedCache::<u32, DropProbe, _>::with_instrumentation(
            "test",
            1,
            Duration::seconds(1),
            ManualClock::new(0),
            crate::hardened_hash::HardenedHashBuilder::default(),
            Arc::new(RecordingMetrics::default()),
            logger,
        );

        assert!(!cache.insert(
            1,
            DropProbe {
                dropped: Arc::clone(&dropped),
            }
        ));
        cache.clock.advance_seconds(1);
        cache.sweep();

        assert!(dropped.load(Ordering::SeqCst));
        assert_eq!(cache.get_track_size(), 0);
    }
}
