//! App-level wrapper around the landed `xrpl/shamap::family` seams.
//!
//! The reference `NodeFamily` owns the shared tree-node cache, full-below cache, and
//! missing-node reporting path. This shell keeps those responsibilities
//! explicit while avoiding a fake full application graph.

use basics::base_uint::Uint256;
use basics::hardened_hash::HardenedHashBuilder;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::{CacheClock, MonotonicClock};
use ledger::Ledger;
use shamap::family::{
    FullBelowCache, FullBelowCacheImpl, MissingNodeReporter, NullFullBelowCache,
    NullMissingNodeReporter, NullNodeFetcher, SHAMapFamily, SHAMapNodeFetcher,
};
use shamap::traversal::TraversalError;
use shamap::tree_node::SHAMapTreeNode;
use shamap::tree_node_cache::TreeNodeCache;
use std::hash::BuildHasher;
use std::sync::Arc;

/// The concrete full-below cache used by the production `NodeFamily` and all
/// inbound SHAMap acquisitions. The NodeFamily retains the owner handle; other
/// runtime users receive only clones of this same `Arc`.
pub type NodeFamilyFullBelowCache = Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>;

///
/// This keeps Rust's shared SHAMap tree cache sizing tied to the same
/// `node_size` profile as reference `TreeCacheSize`, `TreeCacheAge`, and
/// `LedgerFetch`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeSizeResourceProfile {
    pub tree_cache_size: usize,
    pub tree_cache_age_seconds: i64,
    /// rippled SizedItem::SweepInterval — how often doSweep runs (seconds).
    pub sweep_interval_seconds: u64,
    /// rippled SizedItem::LedgerFetch — maximum adjacent ledgers prefetched
    /// by one `LedgerMaster::fetchForHistory` pass.
    pub ledger_fetch_size: u32,
    /// LedgerMaster's retained completed-ledger history. Medium is the rippled
    /// 3.3.0 policy of 64 ledgers for 180 seconds.
    pub ledger_history_cache_size: usize,
    pub ledger_history_cache_age_seconds: i64,
    /// Maximum concurrently live inbound acquisitions. This bounds coordinator
    /// state independently of the three-worker local-scan pool.
    pub acquisition_max_sessions: usize,
    /// rippled kFullBelowTargetSize (constant 524288 in Tuning.h).
    pub full_below_target_size: usize,
    /// rippled kFullBelowExpiration (constant 10 minutes in Tuning.h).
    pub full_below_expiration_seconds: i64,
}

impl NodeSizeResourceProfile {
    pub fn for_node_size(node_size: Option<&str>) -> Self {
        match node_size
            .unwrap_or("medium")
            .trim()
            .to_ascii_lowercase()
            .as_str()
        {
            "tiny" => Self {
                tree_cache_size: 262_144,
                tree_cache_age_seconds: 30,
                sweep_interval_seconds: 10,
                ledger_fetch_size: 2,
                ledger_history_cache_size: 16,
                ledger_history_cache_age_seconds: 60,
                acquisition_max_sessions: 4,
                full_below_target_size: 524_288,
                full_below_expiration_seconds: 600,
            },
            "small" => Self {
                tree_cache_size: 524_288,
                tree_cache_age_seconds: 60,
                sweep_interval_seconds: 30,
                ledger_fetch_size: 3,
                ledger_history_cache_size: 32,
                ledger_history_cache_age_seconds: 120,
                acquisition_max_sessions: 8,
                full_below_target_size: 524_288,
                full_below_expiration_seconds: 600,
            },
            "large" => Self {
                tree_cache_size: 4_194_304,
                tree_cache_age_seconds: 120,
                sweep_interval_seconds: 90,
                ledger_fetch_size: 5,
                ledger_history_cache_size: 128,
                ledger_history_cache_age_seconds: 300,
                acquisition_max_sessions: 32,
                full_below_target_size: 524_288,
                full_below_expiration_seconds: 600,
            },
            "huge" => Self {
                tree_cache_size: 8_388_608,
                tree_cache_age_seconds: 900,
                sweep_interval_seconds: 120,
                ledger_fetch_size: 8,
                ledger_history_cache_size: 256,
                ledger_history_cache_age_seconds: 600,
                acquisition_max_sessions: 64,
                full_below_target_size: 524_288,
                full_below_expiration_seconds: 600,
            },
            _ => Self {
                // medium (default)
                tree_cache_size: 2_097_152,
                tree_cache_age_seconds: 90,
                sweep_interval_seconds: 60,
                ledger_fetch_size: 4,
                ledger_history_cache_size: 64,
                ledger_history_cache_age_seconds: 180,
                acquisition_max_sessions: 16,
                full_below_target_size: 524_288,
                full_below_expiration_seconds: 600,
            },
        }
    }

    /// The LedgerMaster settings selected by this profile. Keeping this
    /// conversion beside the other node-size policy prevents production from
    /// silently falling back to `LedgerMasterConfig::default()`.
    pub fn ledger_master_config(self) -> ledger::LedgerMasterConfig {
        ledger::LedgerMasterConfig {
            history_cache_size: self.ledger_history_cache_size,
            history_cache_age: time::Duration::seconds(self.ledger_history_cache_age_seconds),
            ..ledger::LedgerMasterConfig::default()
        }
    }

    /// Coordinator budget selected by this profile. The packet and byte limits
    /// remain the existing per-session protocol admission limits.
    pub fn acquisition_budget(self) -> acquisition::BudgetState {
        acquisition::BudgetState::new(
            self.acquisition_max_sessions,
            acquisition::AdmissionBudget::default(),
            std::time::Duration::from_secs(3),
        )
    }
}

pub trait NodeFamilyRuntime: Send + Sync {
    fn sweep(&self);
    fn reset(&self);

    /// Returns the production cache owned by this NodeFamily. Test-only and
    /// legacy family implementations that do not own the concrete cache keep
    /// the default `None`; bootstrap refuses to create an independent cache.
    fn owned_full_below_cache(&self) -> Option<NodeFamilyFullBelowCache> {
        None
    }

    fn fetch_cached_node(
        &self,
        hash: SHAMapHash,
        ledger_seq: u32,
    ) -> Option<SharedIntrusive<SHAMapTreeNode>>;
    fn missing_node_acquire_by_seq(&self, seq: u32, hash: Uint256);
    fn missing_node_acquire_by_hash(&self, hash: Uint256, seq: u32);
    fn visit_state_map_hashes(
        &self,
        ledger: &Ledger,
        visit: &mut dyn FnMut(Uint256) -> bool,
    ) -> Result<(), TraversalError>;
    fn visit_state_map_nodes(
        &self,
        ledger: &Ledger,
        visit: &mut dyn FnMut(&SharedIntrusive<SHAMapTreeNode>) -> bool,
    ) -> Result<(), TraversalError>;
}

#[derive(Debug, Clone)]
pub struct NodeFamily<
    C = MonotonicClock,
    S = HardenedHashBuilder,
    FB = NullFullBelowCache,
    F = NullNodeFetcher,
    MR = NullMissingNodeReporter,
    NS = (),
> {
    family: Arc<SHAMapFamily<C, S, FB, F, MR, NS>>,
    /// Present only for the production family whose SHAMapFamily receives this
    /// exact Arc as its full-below cache.
    owned_full_below_cache: Option<NodeFamilyFullBelowCache>,
}

impl<C, S, FB, F, MR, NS> NodeFamily<C, S, FB, F, MR, NS> {
    pub fn new(family: SHAMapFamily<C, S, FB, F, MR, NS>) -> Self {
        Self {
            family: Arc::new(family),
            owned_full_below_cache: None,
        }
    }

    pub fn from_arc(family: Arc<SHAMapFamily<C, S, FB, F, MR, NS>>) -> Self {
        Self {
            family,
            owned_full_below_cache: None,
        }
    }

    pub fn shared_family(&self) -> Arc<SHAMapFamily<C, S, FB, F, MR, NS>> {
        Arc::clone(&self.family)
    }

    pub fn with_full_below_cache<T>(&self, callback: impl FnOnce(&FB) -> T) -> T {
        self.family.with_full_below_cache(callback)
    }

    pub fn with_sync_resources<T>(&self, callback: impl FnOnce(&FB, &F) -> T) -> T {
        self.family.with_sync_resources(callback)
    }

    pub fn cache_lookup(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>>
    where
        C: CacheClock,
        S: BuildHasher + Clone,
    {
        self.family.cache_lookup(hash)
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
        self.family
            .fetch_cached_node_or_acquire_by_seq(hash, ledger_seq)
    }

    pub fn sweep(&self)
    where
        C: CacheClock,
        S: BuildHasher + Clone,
        FB: FullBelowCache,
    {
        self.family.sweep();
    }

    pub fn reset(&self)
    where
        C: CacheClock,
        S: BuildHasher + Clone,
        FB: FullBelowCache,
        MR: MissingNodeReporter,
    {
        self.family.reset();
    }

    pub fn tree_node_cache(&self) -> Arc<TreeNodeCache<C, S>> {
        self.family.tree_node_cache()
    }

    pub fn tree_node_cache_keys(&self) -> Vec<Uint256>
    where
        C: CacheClock,
        S: BuildHasher + Clone,
    {
        self.family.tree_node_cache().get_keys()
    }

    pub fn clear_full_below_cache(&self)
    where
        FB: FullBelowCache,
    {
        self.family.with_full_below_cache(|cache| cache.clear());
    }
}

impl<F, MR> NodeFamily<MonotonicClock, HardenedHashBuilder, NodeFamilyFullBelowCache, F, MR> {
    /// Construct the production family around its one real FullBelow cache.
    /// The same Arc is installed in `SHAMapFamily`, retained by `NodeFamily`,
    /// and later handed to `InboundLedgers` for every acquisition.
    pub fn new_with_owned_full_below_cache(
        tree_node_cache: Arc<TreeNodeCache<MonotonicClock, HardenedHashBuilder>>,
        generation: u32,
        target_size: usize,
        expiration: time::Duration,
        fetcher: F,
        missing_node_reporter: MR,
    ) -> Self {
        let full_below_cache = Arc::new(FullBelowCacheImpl::new_with_expiration(
            generation,
            MonotonicClock::default(),
            HardenedHashBuilder::default(),
            target_size,
            expiration,
        ));
        Self {
            family: Arc::new(SHAMapFamily::new(
                tree_node_cache,
                Arc::clone(&full_below_cache),
                fetcher,
                missing_node_reporter,
            )),
            owned_full_below_cache: Some(full_below_cache),
        }
    }
}

impl<C, S, FB, F, MR, NS> NodeFamilyRuntime for NodeFamily<C, S, FB, F, MR, NS>
where
    C: CacheClock + Send + Sync + 'static,
    S: BuildHasher + Clone + Send + Sync + 'static,
    FB: FullBelowCache + Send + Sync + 'static,
    F: SHAMapNodeFetcher + Send + Sync + 'static,
    MR: MissingNodeReporter + Send + Sync + 'static,
    NS: Send + Sync + 'static,
{
    fn sweep(&self) {
        NodeFamily::sweep(self);
    }

    fn reset(&self) {
        NodeFamily::reset(self);
    }

    fn owned_full_below_cache(&self) -> Option<NodeFamilyFullBelowCache> {
        self.owned_full_below_cache.as_ref().map(Arc::clone)
    }

    fn fetch_cached_node(
        &self,
        hash: SHAMapHash,
        ledger_seq: u32,
    ) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        self.fetch_cached_node_or_acquire_by_seq(hash, ledger_seq)
    }

    fn missing_node_acquire_by_seq(&self, seq: u32, hash: Uint256) {
        self.family.missing_node_acquire_by_seq(seq, hash);
    }

    fn missing_node_acquire_by_hash(&self, hash: Uint256, seq: u32) {
        self.family.missing_node_acquire_by_hash(hash, seq);
    }

    fn visit_state_map_hashes(
        &self,
        ledger: &Ledger,
        visit: &mut dyn FnMut(Uint256) -> bool,
    ) -> Result<(), TraversalError> {
        let family = self.shared_family();
        ledger
            .state_map()
            .visit_nodes_with_family(family.as_ref(), &mut |node| {
                visit(*node.get_hash().as_uint256())
            })
    }

    fn visit_state_map_nodes(
        &self,
        ledger: &Ledger,
        visit: &mut dyn FnMut(&SharedIntrusive<SHAMapTreeNode>) -> bool,
    ) -> Result<(), TraversalError> {
        let family = self.shared_family();
        ledger
            .state_map()
            .visit_nodes_with_family(family.as_ref(), &mut |node| visit(node))
    }
}

#[cfg(test)]
mod tests {
    use super::{NodeFamily, NodeFamilyRuntime, NodeSizeResourceProfile};
    use basics::base_uint::Uint256;
    use basics::hardened_hash::HardenedHashBuilder;
    use basics::tagged_cache::MonotonicClock;
    use shamap::family::{FullBelowCache, MissingNodeReporter, NullNodeFetcher, SHAMapFamily};
    use shamap::tree_node_cache::TreeNodeCache;
    use std::sync::{Arc, Mutex};

    #[derive(Debug, Default)]
    struct RecordingFullBelowCache {
        generation: u32,
        inserted: parking_lot::Mutex<Vec<Uint256>>,
        sweeps: std::sync::atomic::AtomicUsize,
        resets: std::sync::atomic::AtomicUsize,
    }

    impl RecordingFullBelowCache {
        fn new(generation: u32) -> Self {
            Self {
                generation,
                inserted: parking_lot::Mutex::new(Vec::new()),
                sweeps: std::sync::atomic::AtomicUsize::new(0),
                resets: std::sync::atomic::AtomicUsize::new(0),
            }
        }
    }

    impl FullBelowCache for RecordingFullBelowCache {
        fn generation(&self) -> u32 {
            self.generation
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

        fn reset(&self) {
            self.resets
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            self.inserted.lock().clear();
        }
    }

    #[derive(Debug, Default)]
    struct RecordingMissingNodeReporter {
        by_seq: Vec<(u32, Uint256)>,
        by_hash: Vec<(Uint256, u32)>,
        resets: usize,
    }

    #[derive(Debug, Clone)]
    struct SharedReporter(Arc<Mutex<RecordingMissingNodeReporter>>);

    impl MissingNodeReporter for SharedReporter {
        fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
            self.0
                .lock()
                .expect("shared reporter mutex must not be poisoned")
                .by_seq
                .push((ref_num, node_hash));
        }

        fn missing_node_acquire_by_hash(&self, ref_hash: Uint256, ref_num: u32) {
            self.0
                .lock()
                .expect("shared reporter mutex must not be poisoned")
                .by_hash
                .push((ref_hash, ref_num));
        }

        fn reset(&self) {
            self.0
                .lock()
                .expect("shared reporter mutex must not be poisoned")
                .resets += 1;
        }
    }

    #[test]
    fn node_size_resource_profile_sized_items() {
        assert_eq!(
            NodeSizeResourceProfile::for_node_size(Some("tiny")),
            NodeSizeResourceProfile {
                tree_cache_size: 262_144,
                tree_cache_age_seconds: 30,
                sweep_interval_seconds: 10,
                ledger_fetch_size: 2,
                ledger_history_cache_size: 16,
                ledger_history_cache_age_seconds: 60,
                acquisition_max_sessions: 4,
                full_below_target_size: 524_288,
                full_below_expiration_seconds: 600,
            }
        );
        assert_eq!(
            NodeSizeResourceProfile::for_node_size(None),
            NodeSizeResourceProfile {
                tree_cache_size: 2_097_152,
                tree_cache_age_seconds: 90,
                sweep_interval_seconds: 60,
                ledger_fetch_size: 4,
                ledger_history_cache_size: 64,
                ledger_history_cache_age_seconds: 180,
                acquisition_max_sessions: 16,
                full_below_target_size: 524_288,
                full_below_expiration_seconds: 600,
            }
        );
        assert_eq!(
            NodeSizeResourceProfile::for_node_size(Some("huge")),
            NodeSizeResourceProfile {
                tree_cache_size: 8_388_608,
                tree_cache_age_seconds: 900,
                sweep_interval_seconds: 120,
                ledger_fetch_size: 8,
                ledger_history_cache_size: 256,
                ledger_history_cache_age_seconds: 600,
                acquisition_max_sessions: 64,
                full_below_target_size: 524_288,
                full_below_expiration_seconds: 600,
            }
        );
    }

    #[test]
    fn medium_profile_drives_ledger_master_and_acquisition_policy() {
        let profile = NodeSizeResourceProfile::for_node_size(Some("medium"));
        let ledger_master = profile.ledger_master_config();

        assert_eq!(ledger_master.history_cache_size, 64);
        assert_eq!(
            ledger_master.history_cache_age,
            time::Duration::seconds(180)
        );
        assert_eq!(profile.acquisition_budget().max_sessions(), 16);
    }

    #[test]
    fn node_family_wraps_shared_family_and_forwards_cache_seams() {
        let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
        let family = Arc::new(SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "node-family-test",
                8,
                time::Duration::seconds(1),
                MonotonicClock::default(),
            )),
            RecordingFullBelowCache::new(77),
            NullNodeFetcher,
            SharedReporter(Arc::clone(&reporter)),
        ));

        let node_family: NodeFamily<
            MonotonicClock,
            HardenedHashBuilder,
            RecordingFullBelowCache,
            NullNodeFetcher,
            SharedReporter,
        > = NodeFamily::from_arc(Arc::clone(&family));
        assert!(Arc::ptr_eq(&family, &node_family.shared_family()));

        let hash = Uint256::from_array([0x42; 32]);
        node_family.with_full_below_cache(|cache| cache.insert(hash));
        node_family.sweep();
        node_family.reset();

        node_family.missing_node_acquire_by_seq(19, hash);
        node_family.missing_node_acquire_by_hash(hash, 19);

        let cache = node_family.with_full_below_cache(|cache| {
            (
                cache.generation,
                cache.inserted.lock().clone(),
                cache.sweeps.load(std::sync::atomic::Ordering::Relaxed),
                cache.resets.load(std::sync::atomic::Ordering::Relaxed),
            )
        });
        assert_eq!(cache.0, 77);
        assert!(cache.1.is_empty());
        assert_eq!(cache.2, 1);
        assert_eq!(cache.3, 1);

        let reporter = reporter
            .lock()
            .expect("reporter mutex must not be poisoned");
        assert_eq!(reporter.by_seq, vec![(19, hash)]);
        assert_eq!(reporter.by_hash, vec![(hash, 19)]);
        assert_eq!(reporter.resets, 1);
    }
}
