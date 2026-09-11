use basics::base_uint::Uint256;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{
    Ledger, LedgerConfig, LedgerHeader, LedgerHistory, LedgerHistoryFillStopReason,
    LedgerHistorySyncState, LedgerInfoProvider, NullLedgerJournal, calculate_ledger_hash, fix_gaps,
};
use protocol::JsonValue;
use shamap::family::{
    NullFullBelowCache, NullMissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher,
};
use shamap::item::SHAMapItem;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use shamap::tree_node_cache::TreeNodeCache;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use time::Duration;

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

fn state_leaf(fill: u8) -> SharedIntrusive<SHAMapTreeNode> {
    SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            Uint256::from_array([fill; 32]),
            vec![
                fill, fill, fill, fill, fill, fill, fill, fill, fill, fill, fill, fill,
            ],
        ),
        0,
    )
}

#[derive(Debug, Default)]
struct RecordingFetcher {
    nodes: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
}

impl SHAMapNodeFetcher for RecordingFetcher {
    fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        self.nodes.get(&hash).cloned()
    }
}

#[derive(Debug, Default)]
struct RecordingProvider {
    by_index: HashMap<u32, LedgerHeader>,
    by_hash: HashMap<SHAMapHash, LedgerHeader>,
    newest: Option<LedgerHeader>,
}

impl LedgerInfoProvider for RecordingProvider {
    fn get_ledger_info_by_index(&self, ledger_index: u32) -> Option<LedgerHeader> {
        self.by_index.get(&ledger_index).copied()
    }

    fn get_ledger_info_by_hash(&self, ledger_hash: SHAMapHash) -> Option<LedgerHeader> {
        self.by_hash.get(&ledger_hash).copied()
    }

    fn get_newest_ledger_info(&self) -> Option<LedgerHeader> {
        self.newest
    }
}

fn family_with_nodes(
    label: &'static str,
    nodes: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
) -> SHAMapFamily<
    ManualClock,
    basics::hardened_hash::HardenedHashBuilder,
    NullFullBelowCache,
    RecordingFetcher,
    NullMissingNodeReporter,
> {
    SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            label,
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        RecordingFetcher { nodes },
        NullMissingNodeReporter,
    )
}

fn immutable_ledger(seq: u32, fill: u8) -> Arc<Ledger> {
    let root = state_leaf(fill);
    let header = LedgerHeader {
        seq,
        account_hash: root.get_hash(),
        parent_hash: sample_hash(fill.wrapping_add(1)),
        close_time: seq + 10,
        close_time_resolution: 30,
        ..LedgerHeader::default()
    };
    let mut ledger = Ledger::from_maps(
        header,
        SyncTree::from_root_with_type(root, SHAMapType::State, true, seq, SyncState::Modifying),
        SyncTree::new_with_type(SHAMapType::Transaction, true, seq),
    );
    ledger.set_immutable(true);
    Arc::new(ledger)
}

#[derive(Default)]
struct RangePresence {
    present: HashSet<u32>,
}

impl ledger::LedgerPresence for RangePresence {
    fn have_ledger(&self, ledger_index: u32) -> bool {
        self.present.contains(&ledger_index)
    }
}

#[derive(Default)]
struct HashPairs {
    pairs: BTreeMap<u32, ledger::LedgerHashPair>,
}

impl ledger::LedgerHashPairProvider for HashPairs {
    fn get_hashes_by_index(
        &self,
        min_seq: u32,
        max_seq: u32,
    ) -> Vec<(u32, ledger::LedgerHashPair)> {
        self.pairs
            .range(min_seq..=max_seq)
            .map(|(seq, pair)| (*seq, *pair))
            .collect()
    }
}

#[derive(Default)]
struct ObjectPresence {
    present: HashSet<(SHAMapHash, u32)>,
}

impl ledger::LedgerObjectPresence for ObjectPresence {
    fn has_ledger_object(&self, ledger_hash: SHAMapHash, ledger_seq: u32) -> bool {
        self.present.contains(&(ledger_hash, ledger_seq))
    }
}

#[derive(Default)]
struct NeverStop;

impl ledger::Stopper for NeverStop {
    fn is_stopping(&self) -> bool {
        false
    }
}

#[test]
fn ledger_history_insert_and_hash_index_core_match_cpp_shape() {
    let history = LedgerHistory::new(32, Duration::seconds(60), ManualClock::new(0));
    let ledger = immutable_ledger(10, 0x11);

    assert!(!history.insert(ledger.clone(), true));
    assert!(history.insert(ledger.clone(), true));
    assert_eq!(history.get_ledger_hash(10), ledger.header().hash);
    assert!(history.get_cache_hit_rate() >= 0.0);
}

#[test]
fn ledger_history_insert_checks_the_live_state_map_hash() {
    let history = LedgerHistory::new(32, Duration::seconds(60), ManualClock::new(0));
    let seq = 12;
    let mut header = LedgerHeader {
        seq,
        account_hash: sample_hash(0x99),
        parent_hash: sample_hash(0x9A),
        close_time: 22,
        close_time_resolution: 30,
        ..LedgerHeader::default()
    };
    header.hash = calculate_ledger_hash(&header);
    let mut ledger = Ledger::from_maps(
        header,
        SyncTree::new_with_type(SHAMapType::State, true, seq),
        SyncTree::new_with_type(SHAMapType::Transaction, true, seq),
    );
    ledger.set_immutable(true);

    let result = catch_unwind(AssertUnwindSafe(|| history.insert(Arc::new(ledger), true)));
    assert!(
        result.is_err() || matches!(result, Ok(false)),
        "C++ parity requires a nonzero state-map hash"
    );
}

#[test]
fn ledger_history_tracks_built_and_validated_match_and_mismatch_state() {
    let history = LedgerHistory::new(32, Duration::seconds(60), ManualClock::new(0));
    let built = immutable_ledger(20, 0x51);
    let validated_same = immutable_ledger(20, 0x51);

    history.built_ledger(
        built.clone(),
        Uint256::from_array([0xAA; 32]),
        JsonValue::from("consensus"),
    );
    history.validated_ledger(validated_same, Some(Uint256::from_array([0xAA; 32])));

    let entry = history
        .consensus_entry(20)
        .expect("consensus entry should be tracked");
    assert_eq!(entry.built, Some(built.header().hash));
    assert_eq!(entry.validated, Some(built.header().hash));
    assert_eq!(history.mismatch_count(), 0);

    let different = immutable_ledger(21, 0x61);
    let built_other = immutable_ledger(21, 0x62);
    history.built_ledger(
        built_other.clone(),
        Uint256::from_array([0xBB; 32]),
        JsonValue::from("mismatch"),
    );
    history.validated_ledger(different.clone(), Some(Uint256::from_array([0xCC; 32])));

    assert_eq!(history.mismatch_count(), 1);
    let mismatch = history
        .mismatches()
        .pop()
        .expect("mismatch should be recorded");
    assert_eq!(mismatch.seq, 21);
    assert_eq!(mismatch.built, built_other.header().hash);
    assert_eq!(mismatch.validated, different.header().hash);
}

#[test]
fn ledger_history_get_by_hash_hits_cache_before_provider() {
    let history = LedgerHistory::new(32, Duration::seconds(60), ManualClock::new(0));
    let ledger = immutable_ledger(11, 0x21);
    let provider = RecordingProvider::default();
    let family = family_with_nodes("history-hash-hit", HashMap::new());

    history.insert(ledger.clone(), true);
    let fetched = history
        .get_ledger_by_hash(
            ledger.header().hash,
            &NullLedgerJournal,
            &LedgerConfig::default(),
            &family,
            &provider,
        )
        .expect("cached fetch should not error")
        .expect("cached ledger should be present");

    assert_eq!(fetched.header().hash, ledger.header().hash);
}

#[test]
fn ledger_history_get_by_hash_loads_and_backfills_cache() {
    let history = LedgerHistory::new(32, Duration::seconds(60), ManualClock::new(0));
    let leaf = state_leaf(0x31);
    let mut header = LedgerHeader {
        seq: 12,
        account_hash: leaf.get_hash(),
        parent_hash: sample_hash(0x32),
        close_time: 44,
        close_time_resolution: 30,
        ..LedgerHeader::default()
    };
    header.hash = calculate_ledger_hash(&header);
    let provider = RecordingProvider {
        by_index: HashMap::from([(12, header)]),
        by_hash: HashMap::from([(header.hash, header)]),
        newest: Some(header),
    };
    let family = family_with_nodes(
        "history-hash-load",
        HashMap::from([(leaf.get_hash(), leaf.clone())]),
    );

    let fetched = history
        .get_ledger_by_hash(
            header.hash,
            &NullLedgerJournal,
            &LedgerConfig::default(),
            &family,
            &provider,
        )
        .expect("provider-backed hash load should not error")
        .expect("provider-backed hash load should return a ledger");

    assert_eq!(fetched.header().hash, header.hash);
    assert_eq!(fetched.header().seq, 12);
    assert_eq!(history.get_ledger_hash(12), SHAMapHash::default());

    let fetched_again = history
        .get_ledger_by_hash(
            header.hash,
            &NullLedgerJournal,
            &LedgerConfig::default(),
            &family,
            &provider,
        )
        .expect("cached second fetch should not error")
        .expect("cached second fetch should return a ledger");
    assert_eq!(fetched_again.header().hash, header.hash);
}

#[test]
fn ledger_history_get_by_seq_loads_and_tracks_index() {
    let history = LedgerHistory::new(32, Duration::seconds(60), ManualClock::new(0));
    let leaf = state_leaf(0x41);
    let mut header = LedgerHeader {
        seq: 13,
        account_hash: leaf.get_hash(),
        parent_hash: sample_hash(0x42),
        close_time: 55,
        close_time_resolution: 30,
        ..LedgerHeader::default()
    };
    header.hash = calculate_ledger_hash(&header);
    let provider = RecordingProvider {
        by_index: HashMap::from([(13, header)]),
        by_hash: HashMap::from([(header.hash, header)]),
        newest: Some(header),
    };
    let family = family_with_nodes(
        "history-seq-load",
        HashMap::from([(leaf.get_hash(), leaf.clone())]),
    );

    let fetched = history
        .get_ledger_by_seq(
            13,
            &NullLedgerJournal,
            &LedgerConfig::default(),
            &family,
            &provider,
        )
        .expect("provider-backed seq load should not error")
        .expect("provider-backed seq load should return a ledger");

    assert_eq!(fetched.header().seq, 13);
    assert_eq!(history.get_ledger_hash(13), header.hash);
}

#[test]
fn ledger_history_get_by_seq_reuses_cached_canonical_arc() {
    let history = LedgerHistory::new(32, Duration::seconds(60), ManualClock::new(0));
    let cached = immutable_ledger(14, 0x51);
    let leaf = state_leaf(0x51);
    let provider = RecordingProvider {
        by_index: HashMap::from([(14, cached.header())]),
        by_hash: HashMap::from([(cached.header().hash, cached.header())]),
        newest: Some(cached.header()),
    };
    let family = family_with_nodes(
        "history-seq-canonical",
        HashMap::from([(leaf.get_hash(), leaf)]),
    );

    assert!(!history.insert(cached.clone(), false));

    let fetched = history
        .get_ledger_by_seq(
            14,
            &NullLedgerJournal,
            &LedgerConfig::default(),
            &family,
            &provider,
        )
        .expect("provider-backed seq load should not error")
        .expect("provider-backed seq load should return a ledger");

    assert!(Arc::ptr_eq(&fetched, &cached));
}

#[test]
fn ledger_history_fix_index_and_clear_prior_match_cpp_shape() {
    let history = LedgerHistory::new(32, Duration::seconds(60), ManualClock::new(0));
    let ledger_a = immutable_ledger(20, 0x51);
    let ledger_b = immutable_ledger(21, 0x61);
    let provider = RecordingProvider::default();
    let family = family_with_nodes("history-clear", HashMap::new());

    history.insert(ledger_a.clone(), true);
    history.insert(ledger_b.clone(), true);

    assert!(!history.fix_index(20, ledger_b.header().hash));
    assert_eq!(history.get_ledger_hash(20), ledger_b.header().hash);
    assert!(history.fix_index(20, ledger_b.header().hash));

    history
        .clear_ledger_cache_prior(
            21,
            &NullLedgerJournal,
            &LedgerConfig::default(),
            &family,
            &provider,
        )
        .expect("clear prior should not error");

    let old = history
        .get_ledger_by_hash(
            ledger_a.header().hash,
            &NullLedgerJournal,
            &LedgerConfig::default(),
            &family,
            &provider,
        )
        .expect("cache lookup should not error");
    assert!(old.is_none());
    let current = history
        .get_ledger_by_hash(
            ledger_b.header().hash,
            &NullLedgerJournal,
            &LedgerConfig::default(),
            &family,
            &provider,
        )
        .expect("cache lookup should not error")
        .expect("newer ledger should remain cached");
    assert_eq!(current.header().seq, 21);
}

#[test]
fn ledger_history_fix_gaps_backfills_ranges_and_clears_fill_flag() {
    let mut state = LedgerHistorySyncState::<LedgerHeader> {
        fetch_state: ledger::FetchForHistoryState {
            fill_in_progress: 12,
            ..Default::default()
        },
        ..Default::default()
    };
    let ledger = LedgerHeader {
        seq: 12,
        parent_hash: sample_hash(11),
        ..LedgerHeader::default()
    };

    let plan = fix_gaps(
        &mut state,
        &ledger,
        &RangePresence {
            present: HashSet::from([9]),
        },
        &HashPairs {
            pairs: BTreeMap::from([
                (
                    11,
                    ledger::LedgerHashPair {
                        ledger_hash: sample_hash(11),
                        parent_hash: sample_hash(10),
                    },
                ),
                (
                    10,
                    ledger::LedgerHashPair {
                        ledger_hash: sample_hash(10),
                        parent_hash: sample_hash(9),
                    },
                ),
                (
                    9,
                    ledger::LedgerHashPair {
                        ledger_hash: sample_hash(9),
                        parent_hash: sample_hash(8),
                    },
                ),
            ]),
        },
        &ObjectPresence {
            present: HashSet::from([(sample_hash(9), 9)]),
        },
        &NeverStop,
    );

    assert_eq!(
        plan.stop_reason,
        LedgerHistoryFillStopReason::AlreadyHaveLedger { seq: 9 }
    );
    assert!(state.complete_ledgers.contains(10));
    assert!(state.complete_ledgers.contains(12));
    assert_eq!(state.fetch_state.fill_in_progress, 0);
}
