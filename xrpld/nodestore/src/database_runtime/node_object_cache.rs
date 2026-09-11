use crate::{NodeObject, NodeObjectType};
use basics::base_uint::Uint256;
use basics::basic_config::{Section, get};
use moka::{policy::EvictionPolicy, sync::Cache};
use protocol::JsonValue;
use std::collections::BTreeMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

/// Target occupancy for the always-on encoded NodeObject working set. The
/// weighted byte budget bounds Moka admission and eviction policy; Moka's
/// concurrent maintenance is intentionally not an instantaneous process-RSS
/// limit. This value derives the default capacity when the operator has not
/// supplied one.
const DEFAULT_TARGET_NODES: u64 = 1_000_000;
const NODE_OBJECT_CACHE_EVICTION_POLICY: &str = "lru";
const NODE_OBJECT_CACHE_DISABLED_POLICY: &str = "disabled";
const DEFAULT_EXPECTED_NODE_BYTES: u64 = 512;
const DEFAULT_MAX_ENTRY_BYTES: usize = 1_048_576;
/// Moka policy and concurrent map bookkeeping not represented by the key or
/// NodeObject allocation. Keep this intentionally conservative.
const ENTRY_METADATA_BYTES: usize = 128;
const ENTRY_FIXED_BYTES: usize = NodeObject::KEY_BYTES
    + std::mem::size_of::<NodeObject>()
    + std::mem::size_of::<Arc<NodeObject>>()
    + ENTRY_METADATA_BYTES;
/// Default idle timeout in seconds — entries not accessed for this duration
/// are evicted. Matches rippled's `cache_age` for medium node_size (90s).
const DEFAULT_CACHE_IDLE_SECONDS: u64 = 90;
/// Default hard TTL in seconds — entries are evicted after this duration
/// regardless of access, ensuring post-rotation stale data is flushed.
const DEFAULT_CACHE_TTL_SECONDS: u64 = 0;

/// Conservative byte weight for an encoded NodeObject cache entry. It includes
/// Moka's key, the Arc handle and NodeObject allocation, payload bytes, and a
/// fixed metadata allowance. Moka accepts `u32` weights, so saturate rather
/// than allowing an oversized accounting conversion to undercount an entry.
fn node_object_cache_entry_weight(_key: &Uint256, object: &Arc<NodeObject>) -> u32 {
    let bytes = ENTRY_FIXED_BYTES.saturating_add(object.data().len());
    u32::try_from(bytes).unwrap_or(u32::MAX)
}

#[derive(Debug)]
enum CacheLoadError {
    NotFound,
    /// The cache was invalidated while the durable loader was running. The
    /// caller must retry through the current store state instead of allowing a
    /// pre-rotation result to repopulate the cache.
    Stale,
    Invalid(Arc<NodeObject>),
    Oversized(Arc<NodeObject>),
}

/// Selects whether a runtime owns the bounded Moka NodeObject cache. Disabled
/// is a true no-cache mode, not a zero-capacity Moka cache.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NodeObjectCacheMode {
    Enabled,
    Disabled,
}

enum CacheStorage {
    Enabled(Cache<Uint256, Arc<NodeObject>>),
    Disabled,
}

#[cfg(test)]
mod tests {
    use super::{
        ENTRY_FIXED_BYTES, NodeObjectCache, NodeObjectCacheMode, node_object_cache_entry_weight,
    };
    use crate::{NodeObject, NodeObjectType};
    use basics::base_uint::Uint256;
    use basics::basic_config::Section;
    use protocol::JsonValue;
    use std::collections::BTreeMap;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn node_object_cache_reports_lru_eviction_policy() {
        let cache = NodeObjectCache::from_config(&Section::new("node_db")).expect("cache");
        let mut counts = BTreeMap::new();
        cache.add_counts_json(&mut counts);
        assert_eq!(
            counts.get("node_object_cache_eviction_policy"),
            Some(&JsonValue::String("lru".to_owned()))
        );
    }

    #[test]
    fn rippled_cache_size_and_age_control_entry_capacity_and_minutes() {
        let mut config = Section::new("node_db");
        config.set("cache_size", "4194304");
        config.set("cache_age", "120");
        config.set("cache_ttl_seconds", "0");

        let cache = NodeObjectCache::from_config(&config).expect("large node cache");

        assert_eq!(cache.capacity_entries, 4_194_304);
        assert_eq!(
            cache.capacity_bytes,
            4_194_304 * (512 + ENTRY_FIXED_BYTES as u64)
        );
        assert_eq!(cache.idle_seconds, 7_200);
        assert_eq!(cache.ttl_seconds, 0);
    }

    #[test]
    fn explicit_node_object_settings_override_legacy_settings() {
        let mut config = Section::new("node_db");
        config.set("cache_size", "8");
        config.set("cache_age", "2");
        config.set("node_object_cache_target_nodes", "16");
        config.set("cache_idle_seconds", "30");

        let cache = NodeObjectCache::from_config(&config).expect("explicit node cache");

        assert_eq!(cache.capacity_entries, 16);
        assert_eq!(cache.idle_seconds, 30);
    }

    #[test]
    fn rejects_max_entry_size_that_cannot_fit_moka_weight() {
        let mut config = Section::new("node_db");
        config.set("cache_max_entry_bytes", &usize::MAX.to_string());
        let error = match NodeObjectCache::from_config(&config) {
            Ok(_) => panic!("oversized weight must fail"),
            Err(error) => error,
        };
        assert!(error.contains("Invalid cache_max_entry_bytes"));
    }

    #[test]
    fn moka_admission_and_metrics_use_conservative_byte_weights() {
        let mut config = Section::new("node_db");
        config.set("node_object_cache_capacity_bytes", "4096");
        let cache = NodeObjectCache::from_config(&config).expect("cache");
        let hash = Uint256::from_array([0xC1; 32]);
        let object = Arc::new(NodeObject::new(
            NodeObjectType::AccountNode,
            vec![7; 96],
            hash,
        ));
        let expected_weight = u64::from(node_object_cache_entry_weight(&hash, &object));

        cache.promote(Arc::clone(&object));
        cache.run_pending_tasks();

        assert_eq!(cache.weighted_size(), expected_weight);
        assert!(expected_weight > object.data().len() as u64);
        assert!(cache.weighted_size() <= cache.capacity_bytes);
    }

    #[test]
    fn invalidation_during_loader_does_not_repopulate_cache() {
        let cache = NodeObjectCache::from_config(&Section::new("node_db")).expect("cache");
        let hash = Uint256::from_array([0xD1; 32]);
        let object = Arc::new(NodeObject::new(NodeObjectType::AccountNode, vec![1], hash));

        let first = cache.get_or_load(hash, || {
            cache.invalidate_all();
            Some(Arc::clone(&object))
        });
        assert!(first.is_none(), "stale loader result must not be cached");

        let second = cache
            .get_or_load(hash, || Some(Arc::clone(&object)))
            .expect("fresh generation must load the object");
        assert_eq!(second.hash(), object.hash());
    }

    #[test]
    fn disabled_mode_preserves_invalid_and_dummy_fetch_semantics() {
        let cache = NodeObjectCache::new(NodeObjectCacheMode::Disabled, &Section::new("node_db"))
            .expect("disabled cache");
        let hash = Uint256::from_array([0xD3; 32]);
        let invalid = Arc::new(NodeObject::new(
            NodeObjectType::AccountNode,
            vec![1],
            Uint256::from_array([0xD4; 32]),
        ));
        let dummy = Arc::new(NodeObject::new(NodeObjectType::Dummy, vec![], hash));

        assert_eq!(
            cache
                .get_or_load(hash, || Some(Arc::clone(&invalid)))
                .expect("invalid object is returned to preserve cache behavior")
                .hash(),
            invalid.hash()
        );
        assert!(
            cache
                .get_or_load(hash, || Some(Arc::clone(&dummy)))
                .is_none(),
            "dummy objects must not be exposed as cache hits"
        );
    }

    #[test]
    fn disabled_mode_never_retains_promotions_and_invokes_each_loader() {
        let cache = NodeObjectCache::new(NodeObjectCacheMode::Disabled, &Section::new("node_db"))
            .expect("disabled cache");
        let hash = Uint256::from_array([0xD2; 32]);
        let object = Arc::new(NodeObject::new(NodeObjectType::AccountNode, vec![1], hash));
        let loads = AtomicUsize::new(0);

        cache.promote(Arc::clone(&object));
        for _ in 0..2 {
            assert_eq!(
                cache
                    .get_or_load(hash, || {
                        loads.fetch_add(1, Ordering::Relaxed);
                        Some(Arc::clone(&object))
                    })
                    .expect("loader object")
                    .hash(),
                &hash
            );
        }

        let mut counts = BTreeMap::new();
        cache.add_counts_json(&mut counts);
        assert_eq!(loads.load(Ordering::Relaxed), 2);
        assert_eq!(
            counts.get("node_object_cache_eviction_policy"),
            Some(&JsonValue::String("disabled".to_owned()))
        );
        for key in [
            "node_object_cache_capacity_entries",
            "node_object_cache_capacity_bytes",
            "node_object_cache_weighted_capacity_bytes",
            "node_object_cache_weighted_size_bytes",
            "node_object_cache_entries",
            "node_object_cache_hits",
            "node_object_cache_promotions",
        ] {
            assert_eq!(
                counts.get(key),
                Some(&JsonValue::String("0".to_owned())),
                "{key}"
            );
        }
        assert_eq!(
            counts.get("node_object_cache_misses"),
            Some(&JsonValue::String("2".to_owned()))
        );
        assert_eq!(
            counts.get("node_object_cache_durable_loads"),
            Some(&JsonValue::String("2".to_owned()))
        );
    }
}

/// A bounded, concurrent cache of immutable encoded NodeObjects.
///
/// The enabled variant owns Moka and applies weighted LRU admission. The
/// disabled variant deliberately owns no Moka allocation or retained object.
/// Both variants retain counters and a generation fence so database rotation
/// has one uniform synchronization contract.
pub(crate) struct NodeObjectCache {
    storage: CacheStorage,
    max_entry_bytes: usize,
    capacity_entries: u64,
    idle_seconds: u64,
    ttl_seconds: u64,
    /// Moka's byte-weighted admission capacity. `capacity_entries` remains a
    /// compatibility planning counter rather than a second eviction limit.
    capacity_bytes: u64,
    hits: AtomicU64,
    misses: AtomicU64,
    durable_loads: AtomicU64,
    promotions: AtomicU64,
    rejected: AtomicU64,
    oversized: AtomicU64,
    invalidations: AtomicU64,
    /// Advances before every bulk invalidation. A Moka initializer records the
    /// generation it started in and refuses to insert if a rotation fence has
    /// begun while the durable read was in progress.
    generation: AtomicU64,
}

impl NodeObjectCache {
    pub(crate) fn new(mode: NodeObjectCacheMode, config: &Section) -> Result<Self, String> {
        match mode {
            NodeObjectCacheMode::Enabled => Self::from_config(config),
            NodeObjectCacheMode::Disabled => Ok(Self::disabled()),
        }
    }

    pub(crate) fn from_config(config: &Section) -> Result<Self, String> {
        let cache_size = config
            .get::<i64>("cache_size")
            .map_err(|_| "Invalid cache_size".to_owned())?
            .map(|value| u64::try_from(value).map_err(|_| "Invalid cache_size".to_owned()))
            .transpose()?;
        let cache_age = config
            .get::<i64>("cache_age")
            .map_err(|_| "Invalid cache_age".to_owned())?
            .map(|value| u64::try_from(value).map_err(|_| "Invalid cache_age".to_owned()))
            .transpose()?;
        let target_nodes = if config.exists("node_object_cache_target_nodes") {
            get(
                config,
                "node_object_cache_target_nodes",
                DEFAULT_TARGET_NODES,
            )
        } else if let Some(cache_size) = cache_size {
            cache_size
        } else {
            DEFAULT_TARGET_NODES
        };
        let expected_node_bytes = get(
            config,
            "node_object_cache_expected_node_bytes",
            DEFAULT_EXPECTED_NODE_BYTES,
        );
        // Operator can set capacity directly in MB (preferred), or fall back
        // to legacy target_nodes × expected_node_bytes calculation.
        let configured_capacity_mb: u64 = get(config, "cache_capacity_mb", 0);
        let configured_capacity = get(config, "node_object_cache_capacity_bytes", 0u64);
        let max_entry_bytes = get(config, "cache_max_entry_bytes", DEFAULT_MAX_ENTRY_BYTES);
        let idle_seconds: u64 = if config.exists("cache_idle_seconds") {
            get(config, "cache_idle_seconds", DEFAULT_CACHE_IDLE_SECONDS)
        } else if let Some(cache_age) = cache_age {
            cache_age.saturating_mul(60)
        } else {
            DEFAULT_CACHE_IDLE_SECONDS
        };
        let ttl_seconds: u64 = get(config, "cache_ttl_seconds", DEFAULT_CACHE_TTL_SECONDS);

        let max_weighted_payload = (u32::MAX as usize).saturating_sub(ENTRY_FIXED_BYTES);
        if max_entry_bytes == 0 || max_entry_bytes > max_weighted_payload {
            return Err(format!(
                "Invalid cache_max_entry_bytes: must be in 1..={max_weighted_payload}"
            ));
        }

        let expected_entry_bytes = expected_node_bytes
            .checked_add(ENTRY_FIXED_BYTES as u64)
            .ok_or_else(|| "NodeObject cache entry weight overflows u64".to_owned())?;
        let capacity_bytes = if configured_capacity_mb > 0 {
            configured_capacity_mb
                .checked_mul(1_048_576)
                .ok_or_else(|| "NodeObject cache capacity overflows u64".to_owned())?
        } else if configured_capacity > 0 {
            configured_capacity
        } else {
            target_nodes
                .checked_mul(expected_entry_bytes)
                .ok_or_else(|| "NodeObject cache capacity overflows u64".to_owned())?
        };
        let entry_capacity = if configured_capacity_mb > 0 || configured_capacity > 0 {
            capacity_bytes / expected_entry_bytes.max(1)
        } else {
            target_nodes
        };

        // This immutable NodeObject workload is a streaming durable-read cache
        // with strong recency characteristics, so retain weighted eviction but
        // use LRU rather than TinyLFU admission. During a full-state scan,
        // Moka's asynchronous maintenance counters can transiently overshoot
        // while the full-state scan processes tens of millions of promotions. TinyLFU's
        // weighted sketch formula multiplies those live counters; the result can
        // clamp to 2^30 u64 slots and permanently allocate an 8 GiB frequency
        // sketch even after eviction returns the cache to its byte capacity.
        let mut builder = Cache::builder()
            .name("node-object-cache")
            .max_capacity(capacity_bytes)
            .weigher(node_object_cache_entry_weight)
            .eviction_policy(EvictionPolicy::lru());

        if idle_seconds > 0 {
            builder = builder.time_to_idle(std::time::Duration::from_secs(idle_seconds));
        }
        if ttl_seconds > 0 {
            builder = builder.time_to_live(std::time::Duration::from_secs(ttl_seconds));
        }

        Ok(Self {
            storage: CacheStorage::Enabled(builder.build()),
            max_entry_bytes,
            capacity_entries: entry_capacity,
            idle_seconds,
            ttl_seconds,
            capacity_bytes,
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            durable_loads: AtomicU64::new(0),
            promotions: AtomicU64::new(0),
            rejected: AtomicU64::new(0),
            oversized: AtomicU64::new(0),
            invalidations: AtomicU64::new(0),
            generation: AtomicU64::new(0),
        })
    }

    fn disabled() -> Self {
        Self {
            storage: CacheStorage::Disabled,
            max_entry_bytes: 0,
            capacity_entries: 0,
            idle_seconds: 0,
            ttl_seconds: 0,
            capacity_bytes: 0,
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            durable_loads: AtomicU64::new(0),
            promotions: AtomicU64::new(0),
            rejected: AtomicU64::new(0),
            oversized: AtomicU64::new(0),
            invalidations: AtomicU64::new(0),
            generation: AtomicU64::new(0),
        }
    }

    /// Returns a validated cached value or performs one Moka-coalesced durable
    /// load. `None` is represented as an error and is therefore never cached.
    /// Disabled mode performs the durable load on every call and does not
    /// retain either the result or a negative entry.
    pub(crate) fn get_or_load<F>(&self, hash: Uint256, load: F) -> Option<Arc<NodeObject>>
    where
        F: FnOnce() -> Option<Arc<NodeObject>>,
    {
        let generation = self.generation();
        match &self.storage {
            CacheStorage::Enabled(cache) => {
                if let Some(object) = cache.get(&hash) {
                    if object.hash() == &hash {
                        self.hits.fetch_add(1, Ordering::Relaxed);
                        return (object.object_type() != NodeObjectType::Dummy).then_some(object);
                    }
                    self.rejected.fetch_add(1, Ordering::Relaxed);
                    cache.invalidate(&hash);
                }

                self.misses.fetch_add(1, Ordering::Relaxed);
                let result = cache.try_get_with(hash, || {
                    self.durable_loads.fetch_add(1, Ordering::Relaxed);
                    let object = load().ok_or(CacheLoadError::NotFound)?;
                    if object.hash() != &hash {
                        return Err(CacheLoadError::Invalid(object));
                    }
                    if object.data().len() > self.max_entry_bytes {
                        return Err(CacheLoadError::Oversized(object));
                    }
                    if self.generation() != generation {
                        return Err(CacheLoadError::Stale);
                    }
                    self.promotions.fetch_add(1, Ordering::Relaxed);
                    Ok(object)
                });

                match result {
                    Ok(object) => (object.object_type() != NodeObjectType::Dummy).then_some(object),
                    Err(error) => match error.as_ref() {
                        CacheLoadError::NotFound => None,
                        CacheLoadError::Stale => None,
                        CacheLoadError::Invalid(object) => {
                            self.rejected.fetch_add(1, Ordering::Relaxed);
                            Some(Arc::clone(object))
                        }
                        CacheLoadError::Oversized(object) => {
                            self.oversized.fetch_add(1, Ordering::Relaxed);
                            Some(Arc::clone(object))
                        }
                    },
                }
            }
            CacheStorage::Disabled => {
                self.misses.fetch_add(1, Ordering::Relaxed);
                self.durable_loads.fetch_add(1, Ordering::Relaxed);
                let object = load()?;
                if object.hash() != &hash {
                    self.rejected.fetch_add(1, Ordering::Relaxed);
                    return Some(object);
                }
                if object.object_type() == NodeObjectType::Dummy {
                    return None;
                }
                Some(object)
            }
        }
    }

    /// Promote a fetch result only when it matches the requested content hash.
    pub(crate) fn promote_for_hash(&self, expected: &Uint256, object: Arc<NodeObject>) {
        if object.hash() != expected {
            self.rejected.fetch_add(1, Ordering::Relaxed);
            return;
        }
        self.promote(object);
    }

    /// Promote only a valid, reasonably sized positive object. Store callers
    /// invoke this after their backend write returns normally.
    pub(crate) fn promote(&self, object: Arc<NodeObject>) {
        let CacheStorage::Enabled(cache) = &self.storage else {
            return;
        };
        if object.data().len() > self.max_entry_bytes {
            self.oversized.fetch_add(1, Ordering::Relaxed);
            return;
        }
        cache.insert(*object.hash(), object);
        self.promotions.fetch_add(1, Ordering::Relaxed);
    }

    pub(crate) fn generation(&self) -> u64 {
        self.generation.load(Ordering::Acquire)
    }

    pub(crate) fn invalidate_all(&self) {
        self.generation.fetch_add(1, Ordering::AcqRel);
        if let CacheStorage::Enabled(cache) = &self.storage {
            cache.invalidate_all();
        }
        self.invalidations.fetch_add(1, Ordering::Relaxed);
    }

    fn is_disabled(&self) -> bool {
        matches!(&self.storage, CacheStorage::Disabled)
    }

    #[cfg(test)]
    fn run_pending_tasks(&self) {
        if let CacheStorage::Enabled(cache) = &self.storage {
            cache.run_pending_tasks();
        }
    }

    #[cfg(test)]
    fn weighted_size(&self) -> u64 {
        match &self.storage {
            CacheStorage::Enabled(cache) => cache.weighted_size(),
            CacheStorage::Disabled => 0,
        }
    }

    pub(crate) fn add_counts_json(&self, obj: &mut BTreeMap<String, JsonValue>) {
        if self.is_disabled() {
            obj.insert(
                "node_object_cache_eviction_policy".to_owned(),
                JsonValue::String(NODE_OBJECT_CACHE_DISABLED_POLICY.to_owned()),
            );
            for key in [
                "node_object_cache_capacity_entries",
                "node_object_cache_idle_seconds",
                "node_object_cache_ttl_seconds",
                "node_object_cache_capacity_bytes",
                "node_object_cache_weighted_capacity_bytes",
                "node_object_cache_weighted_size_bytes",
                "node_object_cache_entries",
                "node_object_cache_hits",
                "node_object_cache_promotions",
            ] {
                obj.insert(key.to_owned(), JsonValue::String("0".to_owned()));
            }
            obj.insert(
                "node_object_cache_capacity_bytes_is_estimate".to_owned(),
                JsonValue::Bool(false),
            );
        } else {
            let CacheStorage::Enabled(cache) = &self.storage else {
                unreachable!("disabled cache returned from enabled branch");
            };
            obj.insert(
                "node_object_cache_eviction_policy".to_owned(),
                JsonValue::String(NODE_OBJECT_CACHE_EVICTION_POLICY.to_owned()),
            );
            obj.insert(
                "node_object_cache_capacity_entries".to_owned(),
                JsonValue::String(self.capacity_entries.to_string()),
            );
            obj.insert(
                "node_object_cache_idle_seconds".to_owned(),
                JsonValue::String(self.idle_seconds.to_string()),
            );
            obj.insert(
                "node_object_cache_ttl_seconds".to_owned(),
                JsonValue::String(self.ttl_seconds.to_string()),
            );
            // Preserve established counters while exposing Moka's actual weighted
            // accounting. These measurements are approximate during concurrent
            // maintenance, as documented by Moka.
            obj.insert(
                "node_object_cache_capacity_bytes".to_owned(),
                JsonValue::String(self.capacity_bytes.to_string()),
            );
            obj.insert(
                "node_object_cache_capacity_bytes_is_estimate".to_owned(),
                JsonValue::Bool(true),
            );
            obj.insert(
                "node_object_cache_weighted_capacity_bytes".to_owned(),
                JsonValue::String(self.capacity_bytes.to_string()),
            );
            obj.insert(
                "node_object_cache_weighted_size_bytes".to_owned(),
                JsonValue::String(cache.weighted_size().to_string()),
            );
            obj.insert(
                "node_object_cache_entries".to_owned(),
                JsonValue::String(cache.entry_count().to_string()),
            );
            obj.insert(
                "node_object_cache_hits".to_owned(),
                JsonValue::String(self.hits.load(Ordering::Relaxed).to_string()),
            );
            obj.insert(
                "node_object_cache_promotions".to_owned(),
                JsonValue::String(self.promotions.load(Ordering::Relaxed).to_string()),
            );
        }
        obj.insert(
            "node_object_cache_misses".to_owned(),
            JsonValue::String(self.misses.load(Ordering::Relaxed).to_string()),
        );
        obj.insert(
            "node_object_cache_durable_loads".to_owned(),
            JsonValue::String(self.durable_loads.load(Ordering::Relaxed).to_string()),
        );
        obj.insert(
            "node_object_cache_rejected".to_owned(),
            JsonValue::String(self.rejected.load(Ordering::Relaxed).to_string()),
        );
        obj.insert(
            "node_object_cache_oversized".to_owned(),
            JsonValue::String(self.oversized.load(Ordering::Relaxed).to_string()),
        );
        obj.insert(
            "node_object_cache_invalidations".to_owned(),
            JsonValue::String(self.invalidations.load(Ordering::Relaxed).to_string()),
        );
    }
}
