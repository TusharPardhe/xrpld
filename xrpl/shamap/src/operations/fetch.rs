//! Current owner-side `SHAMap` cache/fetch/filter helpers such as
//! `checkFilter` and `fetchNodeNT`.

use crate::family::{MissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher};
use crate::sync::{SHAMapMissingNode, SHAMapType};
use crate::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use basics::blob::Blob;
use basics::intrusive_pointer::SharedIntrusive;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::CacheClock;
use std::hash::BuildHasher;

pub trait SHAMapSyncFilter {
    fn got_node(
        &mut self,
        from_filter: bool,
        node_hash: SHAMapHash,
        ledger_seq: u32,
        node_data: Blob,
        node_type: SHAMapNodeType,
    );

    fn get_node(&mut self, node_hash: SHAMapHash) -> Option<Blob>;

    /// Check if this node should be stored. Called BEFORE serialization
    /// to avoid expensive serialize_with_prefix for duplicates.
    /// Default: always store.
    fn should_store(&mut self, node_hash: SHAMapHash) -> bool {
        let _ = node_hash;
        true
    }
}

#[derive(Debug, Clone)]
pub enum AsyncDescendResult {
    Ready(Option<SharedIntrusive<SHAMapTreeNode>>),
    Pending(SHAMapHash),
}

pub fn check_filter(
    node_hash: SHAMapHash,
    ledger_seq: u32,
    filter: &mut Option<&mut dyn SHAMapSyncFilter>,
) -> Option<SharedIntrusive<SHAMapTreeNode>> {
    let filter = filter.as_deref_mut()?;
    let node_data = filter.get_node(node_hash)?;
    let node = SHAMapTreeNode::make_from_prefix(&node_data, node_hash).ok()?;
    filter.got_node(true, node_hash, ledger_seq, node_data, node.get_type());
    Some(node)
}

pub fn check_filter_with_family<CLOCK, S, FB, F, MR, NS>(
    node_hash: SHAMapHash,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
    filter: &mut Option<&mut dyn SHAMapSyncFilter>,
) -> Option<SharedIntrusive<SHAMapTreeNode>>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
{
    let filter = filter.as_deref_mut()?;
    let node_data = filter.get_node(node_hash)?;
    let mut node = match SHAMapTreeNode::make_from_prefix(&node_data, node_hash) {
        Ok(node) => node,
        Err(err) => {
            family.log_warn(&format!("invalid node/data, hash={node_hash}: {err:?}"));
            return None;
        }
    };
    filter.got_node(true, node_hash, ledger_seq, node_data, node.get_type());
    if backed {
        family.canonicalize(node_hash, &mut node);
    }
    Some(node)
}

pub fn fetch_node_nt_with_family<CLOCK, S, FB, F, MR, NS>(
    hash: SHAMapHash,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
    filter: &mut Option<&mut dyn SHAMapSyncFilter>,
) -> Option<SharedIntrusive<SHAMapTreeNode>>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    if let Some(node) = family.cache_lookup(hash) {
        return Some(node);
    }

    if backed && let Some(node) = family.fetch_cached_node_or_acquire_by_seq(hash, ledger_seq) {
        return Some(node);
    }

    check_filter_with_family(hash, backed, ledger_seq, family, filter)
}

pub fn fetch_node_with_family<CLOCK, S, FB, F, MR, NS>(
    hash: SHAMapHash,
    map_type: SHAMapType,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<SharedIntrusive<SHAMapTreeNode>, SHAMapMissingNode>
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
{
    let mut no_filter = None;
    fetch_node_nt_with_family(hash, backed, ledger_seq, family, &mut no_filter)
        .ok_or_else(|| SHAMapMissingNode::from_hash(map_type, hash))
}

pub fn descend_async_with_family<CLOCK, S, FB, F, MR, NS, REQ>(
    parent: &SharedIntrusive<SHAMapTreeNode>,
    branch: usize,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
    filter: &mut Option<&mut dyn SHAMapSyncFilter>,
    request_async_fetch: &mut REQ,
) -> AsyncDescendResult
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
    REQ: FnMut(SHAMapHash, u32),
{
    descend_async_raw(
        parent,
        branch,
        backed,
        ledger_seq,
        family,
        filter,
        request_async_fetch,
    )
}

/// Descends with a pinned one-word intrusive handle so concurrent cache/tree
/// release cannot invalidate the selected child during this traversal step.
pub fn descend_async_raw<CLOCK, S, FB, F, MR, NS, REQ>(
    parent: &SHAMapTreeNode,
    branch: usize,
    backed: bool,
    ledger_seq: u32,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
    filter: &mut Option<&mut dyn SHAMapSyncFilter>,
    request_async_fetch: &mut REQ,
) -> AsyncDescendResult
where
    CLOCK: CacheClock,
    S: BuildHasher + Clone,
    F: SHAMapNodeFetcher,
    MR: MissingNodeReporter,
    REQ: FnMut(SHAMapHash, u32),
{
    assert!(
        parent.is_inner(),
        "descend_async_with_family requires an inner parent node"
    );

    if let Some(loaded) = parent.get_child(branch) {
        return AsyncDescendResult::Ready(Some(loaded));
    }
    if parent.is_empty_branch(branch) {
        return AsyncDescendResult::Ready(None);
    }

    let hash = parent.get_child_hash(branch);
    if let Some(found) = family.cache_lookup(hash) {
        return AsyncDescendResult::Ready(Some(parent.canonicalize_child(branch, found)));
    }

    // `descendAsync` intentionally checks the filter before scheduling a
    // backed read. This ordering differs from `fetchNodeNT(filter)`.
    if let Some(found) = check_filter_with_family(hash, backed, ledger_seq, family, filter) {
        return AsyncDescendResult::Ready(Some(parent.canonicalize_child(branch, found)));
    }

    if !backed {
        return AsyncDescendResult::Ready(None);
    }

    // Match rippled `descendAsync`: after cache/filter misses, defer exactly
    // one backing-store resolution to the scan completion boundary. Doing a
    // synchronous read here and another during completion probes NuDB twice
    // for the same unresolved child.
    request_async_fetch(hash, ledger_seq);
    AsyncDescendResult::Pending(hash)
}

#[cfg(test)]
mod tests {
    use super::{
        AsyncDescendResult, SHAMapSyncFilter, check_filter_with_family, descend_async_with_family,
        fetch_node_nt_with_family, fetch_node_with_family,
    };
    use crate::family::{
        JournalLevel, MissingNodeReporter, NullFullBelowCache, NullNodeFetcher, SHAMapFamily,
        SHAMapJournal,
    };
    use crate::item::SHAMapItem;
    use crate::sync::{SHAMapMissingNode, SHAMapType};
    use crate::tree_node::{SHAMapNodeType, SHAMapTreeNode};
    use crate::tree_node_cache::TreeNodeCache;
    use basics::base_uint::Uint256;
    use basics::blob::Blob;
    use basics::intrusive_pointer::SharedIntrusive;
    use basics::sha_map_hash::SHAMapHash;
    use basics::tagged_cache::ManualClock;
    use std::sync::{Arc, Mutex};
    use time::Duration;

    fn sample_uint256(fill: u8) -> Uint256 {
        Uint256::from_array([fill; 32])
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

    #[derive(Default)]
    struct RecordingFilter {
        node_blob: Option<Blob>,
        got: Vec<(bool, SHAMapHash, u32, SHAMapNodeType)>,
    }

    impl SHAMapSyncFilter for RecordingFilter {
        fn got_node(
            &mut self,
            from_filter: bool,
            node_hash: SHAMapHash,
            ledger_seq: u32,
            _node_data: Blob,
            node_type: SHAMapNodeType,
        ) {
            self.got
                .push((from_filter, node_hash, ledger_seq, node_type));
        }

        fn get_node(&mut self, _node_hash: SHAMapHash) -> Option<Blob> {
            self.node_blob.take()
        }
    }

    #[derive(Debug, Clone)]
    struct FixedFetcher(Option<SharedIntrusive<SHAMapTreeNode>>);

    impl crate::family::SHAMapNodeFetcher for FixedFetcher {
        fn fetch_node(&self, _hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
            self.0.clone()
        }
    }

    #[derive(Debug, Default)]
    struct RecordingJournal {
        entries: Mutex<Vec<(JournalLevel, String)>>,
    }

    impl RecordingJournal {
        fn entries(&self) -> Vec<(JournalLevel, String)> {
            self.entries
                .lock()
                .expect("journal entries mutex must not be poisoned")
                .clone()
        }
    }

    impl SHAMapJournal for RecordingJournal {
        fn log(&self, level: JournalLevel, message: &str) {
            self.entries
                .lock()
                .expect("journal entries mutex must not be poisoned")
                .push((level, message.to_owned()));
        }
    }

    #[test]
    fn filter_hits_are_canonicalized_through_family_when_backed() {
        let cache = Arc::new(TreeNodeCache::new(
            "fetch-filter",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        ));
        let canonical = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(0x11), vec![1; 12]),
            0,
        );
        let mut cached = canonical.clone();
        assert!(!cache.canonicalize_replace_client(canonical.get_hash().as_uint256(), &mut cached));

        let filter_blob = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            canonical
                .peek_item()
                .expect("canonical leaf should carry an item"),
            0,
            canonical.get_hash(),
        )
        .serialize_with_prefix()
        .expect("prefix serialization should succeed");

        let family = SHAMapFamily::new(
            cache,
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            RecordingMissingNodeReporter::default(),
        );
        let mut filter = RecordingFilter {
            node_blob: Some(filter_blob),
            got: Vec::new(),
        };
        let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);

        let resolved =
            check_filter_with_family(canonical.get_hash(), true, 55, &family, &mut filter_ref)
                .expect("filter should provide a node");

        assert!(std::ptr::eq(&*resolved, &*canonical));
        assert_eq!(
            filter.got,
            vec![(true, canonical.get_hash(), 55, SHAMapNodeType::AccountState)]
        );
    }

    #[test]
    fn invalid_filter_nodes_log_a_warning_through_the_family_journal() {
        let hash = SHAMapHash::new(sample_uint256(0x33));
        let journal = Arc::new(RecordingJournal::default());
        let family = SHAMapFamily::new_with_journal(
            Arc::new(TreeNodeCache::new(
                "fetch-filter-invalid",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            RecordingMissingNodeReporter::default(),
            journal.clone(),
        );
        let mut filter = RecordingFilter {
            node_blob: Some(vec![0x00, 0xAB, 0xCD]),
            got: Vec::new(),
        };
        let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);

        let resolved = check_filter_with_family(hash, true, 90, &family, &mut filter_ref);

        assert!(resolved.is_none());
        assert!(filter.got.is_empty());
        assert_eq!(journal.entries().len(), 1);
        assert_eq!(journal.entries()[0].0, JournalLevel::Warn);
        assert!(journal.entries()[0].1.contains("invalid node/data"));
    }

    #[test]
    fn fetch_node_nt_with_family_reports_backed_miss_before_filter_fallback() {
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

        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(0x22), vec![2; 12]),
            0,
        );
        let leaf_blob = leaf
            .serialize_with_prefix()
            .expect("prefix serialization should succeed");

        let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "fetch-nt",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            SharedReporter(reporter.clone()),
        );
        let mut filter = RecordingFilter {
            node_blob: Some(leaf_blob),
            got: Vec::new(),
        };
        let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);

        let resolved =
            fetch_node_nt_with_family(leaf.get_hash(), true, 66, &family, &mut filter_ref)
                .expect("filter should provide a fallback node");

        assert_eq!(resolved.get_hash(), leaf.get_hash());
        assert_eq!(
            filter.got,
            vec![(true, leaf.get_hash(), 66, SHAMapNodeType::AccountState)]
        );
        let reporter = reporter
            .lock()
            .expect("shared reporter mutex must not be poisoned");
        assert_eq!(
            *reporter
                .by_seq
                .lock()
                .expect("recording reporter by-seq mutex must not be poisoned"),
            vec![(66, *leaf.get_hash().as_uint256())]
        );
    }

    #[test]
    fn fetch_node_with_family_returns_backed_nodes_without_missing_error() {
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

        let leaf = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(0x33), vec![3; 12]),
            0,
        );
        let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "fetch-throw-hit",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            FixedFetcher(Some(leaf.clone())),
            SharedReporter(reporter.clone()),
        );

        let resolved =
            fetch_node_with_family(leaf.get_hash(), SHAMapType::State, true, 77, &family)
                .expect("backed fetch should resolve the requested node");

        assert_eq!(resolved.get_hash(), leaf.get_hash());
        let reporter = reporter
            .lock()
            .expect("shared reporter mutex must not be poisoned");
        assert!(
            reporter
                .by_seq
                .lock()
                .expect("recording reporter by-seq mutex must not be poisoned")
                .is_empty()
        );
    }

    #[test]
    fn fetch_node_with_family_returns_missing_node_error_for_unresolved_hashes() {
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

        let missing_hash = SHAMapHash::new(sample_uint256(0x44));
        let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "fetch-throw-miss",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            SharedReporter(reporter.clone()),
        );

        let error =
            fetch_node_with_family(missing_hash, SHAMapType::Transaction, true, 88, &family)
                .expect_err("missing backed fetch should return a SHAMapMissingNode");

        assert_eq!(
            error,
            SHAMapMissingNode::from_hash(SHAMapType::Transaction, missing_hash)
        );
        let reporter = reporter
            .lock()
            .expect("shared reporter mutex must not be poisoned");
        assert_eq!(
            *reporter
                .by_seq
                .lock()
                .expect("recording reporter by-seq mutex must not be poisoned"),
            vec![(88, *missing_hash.as_uint256())]
        );
    }

    #[test]
    fn async_descend_reuses_loaded_child_without_queueing() {
        let child = SHAMapTreeNode::new_leaf_with_hash(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(0x51), vec![5; 12]),
            0,
            SHAMapHash::new(sample_uint256(0x61)),
        );
        let parent = SHAMapTreeNode::new_inner(1);
        parent.set_child_hash(3, child.get_hash());
        parent.share_child(3, &child);
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "async-descend-loaded",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            RecordingMissingNodeReporter::default(),
        );
        let mut no_filter = None;
        let mut async_requests = Vec::new();

        let resolved = descend_async_with_family(
            &parent,
            3,
            true,
            91,
            &family,
            &mut no_filter,
            &mut |hash, ledger_seq| async_requests.push((hash, ledger_seq)),
        );

        match resolved {
            AsyncDescendResult::Ready(Some(node)) => assert!(std::ptr::eq(&*node, &*child)),
            _ => panic!("loaded child should resolve immediately"),
        }
        assert!(async_requests.is_empty());
    }

    #[test]
    fn async_descend_checks_filter_before_queueing_backed_fetches() {
        let child = SHAMapTreeNode::new_leaf(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(sample_uint256(0x52), vec![6; 12]),
            0,
        );
        let child_blob = child
            .serialize_with_prefix()
            .expect("prefix serialization should succeed");
        let parent = SHAMapTreeNode::new_inner(1);
        parent.set_child_hash(4, child.get_hash());
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "async-descend-filter",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            RecordingMissingNodeReporter::default(),
        );
        let mut filter = RecordingFilter {
            node_blob: Some(child_blob),
            got: Vec::new(),
        };
        let mut filter_ref: Option<&mut dyn SHAMapSyncFilter> = Some(&mut filter);
        let mut async_requests = Vec::new();

        let resolved = descend_async_with_family(
            &parent,
            4,
            true,
            92,
            &family,
            &mut filter_ref,
            &mut |hash, ledger_seq| async_requests.push((hash, ledger_seq)),
        );

        let attached = match resolved {
            AsyncDescendResult::Ready(Some(node)) => node,
            _ => panic!("filter hit should resolve immediately"),
        };
        assert_eq!(attached.get_hash(), child.get_hash());
        assert!(parent.get_child(4).is_some());
        assert!(async_requests.is_empty());
        assert_eq!(
            filter.got,
            vec![(true, child.get_hash(), 92, SHAMapNodeType::AccountState)]
        );
    }

    #[test]
    fn async_descend_queues_backed_fetches_after_cache_and_filter_miss() {
        let missing_hash = SHAMapHash::new(sample_uint256(0x53));
        let parent = SHAMapTreeNode::new_inner(1);
        parent.set_child_hash(5, missing_hash);
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "async-descend-pending",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            RecordingMissingNodeReporter::default(),
        );
        let mut no_filter = None;
        let mut async_requests = Vec::new();

        let resolved = descend_async_with_family(
            &parent,
            5,
            true,
            93,
            &family,
            &mut no_filter,
            &mut |hash, ledger_seq| async_requests.push((hash, ledger_seq)),
        );

        match resolved {
            AsyncDescendResult::Pending(hash) => assert_eq!(hash, missing_hash),
            _ => panic!("backed miss should queue an async fetch"),
        }
        assert_eq!(async_requests, vec![(missing_hash, 93)]);
        assert!(parent.get_child(5).is_none());
    }

    #[test]
    fn async_descend_returns_missing_immediately_when_unbacked() {
        let missing_hash = SHAMapHash::new(sample_uint256(0x54));
        let parent = SHAMapTreeNode::new_inner(1);
        parent.set_child_hash(6, missing_hash);
        let family = SHAMapFamily::new(
            Arc::new(TreeNodeCache::new(
                "async-descend-unbacked",
                8,
                Duration::seconds(1),
                ManualClock::new(0),
            )),
            NullFullBelowCache::new(0),
            NullNodeFetcher,
            RecordingMissingNodeReporter::default(),
        );
        let mut no_filter = None;
        let mut async_requests = Vec::new();

        let resolved = descend_async_with_family(
            &parent,
            6,
            false,
            94,
            &family,
            &mut no_filter,
            &mut |hash, ledger_seq| async_requests.push((hash, ledger_seq)),
        );

        match resolved {
            AsyncDescendResult::Ready(None) => {}
            _ => panic!("unbacked miss should not queue an async fetch"),
        }
        assert!(async_requests.is_empty());
    }
}
