use basics::base_uint::Uint256;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{
    Fees, Ledger, LedgerConfig, LedgerHeader, LedgerInfoProvider, LedgerJournal,
    XRP_LEDGER_EARLIEST_FEES, amendments_key, calculate_ledger_hash, fees_key,
};
use parking_lot::Mutex;
use protocol::{FeatureSet, encode_amendments_entry, encode_fee_settings_entry, feature_xrp_fees};
use shamap::family::{MissingNodeReporter, NullFullBelowCache, SHAMapFamily, SHAMapNodeFetcher};
use shamap::item::SHAMapItem;
use shamap::mutation::MutableTree;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use shamap::tree_node_cache::TreeNodeCache;
use std::collections::HashMap;
use std::sync::Arc;
use time::Duration;

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

fn sample_uint256(fill: u8) -> Uint256 {
    Uint256::from_array([fill; 32])
}

fn sample_ledger_config(features: impl IntoIterator<Item = Uint256>) -> LedgerConfig {
    LedgerConfig::new(
        Fees {
            base: 10,
            reserve: 20,
            increment: 30,
        },
        FeatureSet::new(features),
    )
}

fn build_state_map_with_items(
    items: &[(Uint256, Vec<u8>)],
    backed: bool,
    ledger_seq: u32,
) -> SyncTree {
    let mut tree = MutableTree::new(1);
    for (key, payload) in items {
        tree.add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(*key, payload.clone()),
        )
        .expect("state map item insertion should succeed");
    }

    SyncTree::from_root_with_type(
        tree.root(),
        SHAMapType::State,
        backed,
        ledger_seq,
        SyncState::Immutable,
    )
}

#[derive(Debug, Default)]
struct RecordingFetcher {
    expected: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
    fetches: Mutex<Vec<SHAMapHash>>,
}

impl SHAMapNodeFetcher for RecordingFetcher {
    fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        self.fetches.lock().push(hash);
        self.expected.get(&hash).cloned()
    }
}

#[derive(Debug, Default)]
struct RecordingMissingNodeReporter {
    by_seq: Vec<(u32, Uint256)>,
}

#[derive(Debug)]
struct SharedReporter(Arc<Mutex<RecordingMissingNodeReporter>>);

impl MissingNodeReporter for SharedReporter {
    fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
        self.0.lock().by_seq.push((ref_num, node_hash));
    }

    fn missing_node_acquire_by_hash(&self, _ref_hash: Uint256, _ref_num: u32) {}
}

#[derive(Debug, Default)]
struct RecordingLedgerJournal {
    infos: Mutex<Vec<String>>,
    warns: Mutex<Vec<String>>,
}

impl RecordingLedgerJournal {
    fn infos(&self) -> Vec<String> {
        self.infos.lock().clone()
    }

    fn warns(&self) -> Vec<String> {
        self.warns.lock().clone()
    }
}

impl LedgerJournal for RecordingLedgerJournal {
    fn info(&self, message: &str) {
        self.infos.lock().push(message.to_owned());
    }

    fn warn(&self, message: &str) {
        self.warns.lock().push(message.to_owned());
    }
}

#[derive(Debug, Default)]
struct RecordingLedgerInfoProvider {
    by_index: HashMap<u32, LedgerHeader>,
    by_hash: HashMap<SHAMapHash, LedgerHeader>,
}

impl LedgerInfoProvider for RecordingLedgerInfoProvider {
    fn get_ledger_info_by_index(&self, ledger_index: u32) -> Option<LedgerHeader> {
        self.by_index.get(&ledger_index).copied()
    }

    fn get_ledger_info_by_hash(&self, ledger_hash: SHAMapHash) -> Option<LedgerHeader> {
        self.by_hash.get(&ledger_hash).copied()
    }

    fn get_newest_ledger_info(&self) -> Option<LedgerHeader> {
        self.by_index
            .values()
            .max_by_key(|header| header.seq)
            .copied()
    }
}

#[test]
fn get_latest_ledger_with_provider_and_config_returns_none_and_zeroes_for_missing_header() {
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-get-latest-miss",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher::default(),
        SharedReporter(Arc::new(
            Mutex::new(RecordingMissingNodeReporter::default()),
        )),
    );

    let (ledger, seq, hash) = Ledger::get_latest_ledger_with_provider_and_config(
        &RecordingLedgerJournal::default(),
        &sample_ledger_config([]),
        &family,
        &RecordingLedgerInfoProvider::default(),
    )
    .expect("latest-ledger wrapper should not fail for a miss");

    assert!(ledger.is_none());
    assert_eq!(seq, 0);
    assert!(hash.is_zero());
}

#[test]
fn get_latest_ledger_with_provider_and_config_returns_loaded_ledger_and_original_header_identity() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xB7), vec![0x33; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees(), sample_uint256(0xB8)]),
            ),
            (fees_key(), encode_fee_settings_entry(13, 23, 33, false)),
        ],
        true,
        812,
    );
    let state_root = state_map.root();
    let mut expected = HashMap::new();
    expected.insert(tx_root.get_hash(), tx_root.clone());
    expected.insert(state_root.get_hash(), state_root.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-get-latest-hit",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher {
            expected,
            fetches: Mutex::new(Vec::new()),
        },
        SharedReporter(Arc::new(
            Mutex::new(RecordingMissingNodeReporter::default()),
        )),
    );
    let journal = RecordingLedgerJournal::default();
    let config = sample_ledger_config([sample_uint256(0xB9), feature_xrp_fees()]);
    let header = LedgerHeader {
        seq: 812,
        hash: sample_hash(0xBA),
        drops: 70,
        parent_hash: sample_hash(0xBB),
        tx_hash: tx_root.get_hash(),
        account_hash: state_root.get_hash(),
        parent_close_time: 12,
        close_time: 13,
        close_time_resolution: 30,
        close_flags: 0,
        ..LedgerHeader::default()
    };
    let provider = RecordingLedgerInfoProvider {
        by_index: HashMap::from([(812, header)]),
        by_hash: HashMap::new(),
    };

    let (ledger, seq, hash) =
        Ledger::get_latest_ledger_with_provider_and_config(&journal, &config, &family, &provider)
            .expect("latest-ledger wrapper should decode");

    let ledger = ledger.expect("provider hit should attempt a load");
    assert_eq!(seq, 812);
    assert_eq!(hash, header.hash);
    assert_eq!(ledger.header().seq, 812);
    assert_eq!(ledger.header().hash, header.hash);
    assert!(ledger.rules().enabled(&sample_uint256(0xB9)));
    assert!(ledger.rules().enabled(&sample_uint256(0xB8)));
}

#[test]
fn get_latest_ledger_with_provider_and_config_preserves_seq_and_hash_when_load_fails() {
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-get-latest-load-fail",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher::default(),
        SharedReporter(reporter),
    );
    let journal = RecordingLedgerJournal::default();
    let header = LedgerHeader {
        seq: 813,
        hash: sample_hash(0xBC),
        drops: 71,
        parent_hash: sample_hash(0xBD),
        tx_hash: sample_hash(0xBE),
        account_hash: sample_hash(0xBF),
        parent_close_time: 14,
        close_time: 15,
        close_time_resolution: 30,
        close_flags: 0,
        ..LedgerHeader::default()
    };
    let provider = RecordingLedgerInfoProvider {
        by_index: HashMap::from([(813, header)]),
        by_hash: HashMap::new(),
    };

    let (ledger, seq, hash) = Ledger::get_latest_ledger_with_provider_and_config(
        &journal,
        &sample_ledger_config([feature_xrp_fees()]),
        &family,
        &provider,
    )
    .expect("latest-ledger wrapper should preserve decode errors only");

    assert!(ledger.is_none());
    assert_eq!(seq, 813);
    assert_eq!(hash, header.hash);
}

#[test]
fn ledger_finish_load_by_index_or_hash_rehashes_logs_and_marks_full() {
    let preset = sample_uint256(0x99);
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x9A), vec![0xCD; 20]),
        0,
    );
    let mut state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees(), sample_uint256(0x9B)]),
            ),
            (fees_key(), encode_fee_settings_entry(41, 52, 63, false)),
        ],
        true,
        XRP_LEDGER_EARLIEST_FEES,
    );
    let expected_state_hash = state_map.hash();
    let tx_map = SyncTree::from_root_with_type(
        tx_root.clone(),
        SHAMapType::Transaction,
        true,
        XRP_LEDGER_EARLIEST_FEES,
        SyncState::Immutable,
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: XRP_LEDGER_EARLIEST_FEES,
            drops: 90,
            parent_hash: sample_hash(0x9C),
            parent_close_time: 22,
            close_time: 33,
            close_time_resolution: 30,
            ..LedgerHeader::default()
        },
        state_map,
        tx_map,
    );
    let journal = RecordingLedgerJournal::default();

    ledger.set_rules(ledger::Rules::new([preset]));
    ledger.apply_default_fees(Fees {
        base: 10,
        reserve: 20,
        increment: 30,
    });
    ledger
        .finish_load_by_index_or_hash(&journal)
        .expect("finish-load helper should finalize a loaded ledger");

    assert!(ledger.is_immutable());
    assert!(ledger.state_map().is_full());
    assert!(ledger.tx_map().is_full());
    assert_eq!(ledger.header().account_hash, expected_state_hash);
    assert_eq!(ledger.header().tx_hash, tx_root.get_hash());
    assert_eq!(
        ledger.header().hash,
        calculate_ledger_hash(&ledger.header())
    );
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 41,
            reserve: 52,
            increment: 63,
        }
    );
    assert!(ledger.rules().enabled(&preset));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&sample_uint256(0x9B)));
    assert_eq!(
        journal.infos(),
        vec![format!("Loaded ledger: {}", ledger.header().hash)]
    );
    assert!(journal.warns().is_empty());
}

#[test]
fn ledger_fetching_state_root_does_not_mark_map_full_before_walkledger() {
    let root = SHAMapTreeNode::new_inner(0);
    root.update_hash();

    let mut ledger = Ledger::new(
        LedgerHeader {
            seq: XRP_LEDGER_EARLIEST_FEES,
            account_hash: root.get_hash(),
            ..LedgerHeader::default()
        },
        true,
    );
    let expected_root = root.clone();
    ledger.set_node_fetcher(Arc::new(move |hash| {
        (hash == expected_root.get_hash()).then_some(expected_root.clone())
    }));

    ledger.try_load_state_root_from_fetcher(root.get_hash());

    assert_eq!(ledger.state_map().root().get_hash(), root.get_hash());
    assert!(
        !ledger.state_map().is_full(),
        "C++ fetchRoot loads the root, but full_ is only set by completed acquisition/load paths"
    );
}

#[test]
fn ledger_finish_load_by_index_or_hash_skips_fee_assert_before_earliest_fees() {
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: XRP_LEDGER_EARLIEST_FEES - 1,
            close_time_resolution: 30,
            ..LedgerHeader::default()
        },
        build_state_map_with_items(&[], true, XRP_LEDGER_EARLIEST_FEES - 1),
        SyncTree::new_with_type(SHAMapType::Transaction, true, XRP_LEDGER_EARLIEST_FEES - 1),
    );
    let journal = RecordingLedgerJournal::default();

    ledger
        .finish_load_by_index_or_hash(&journal)
        .expect("pre-fee ledgers should skip the fee-entry assertion");

    assert!(ledger.is_immutable());
    assert!(ledger.state_map().is_full());
    assert!(ledger.tx_map().is_full());
    assert_eq!(
        journal.infos(),
        vec![format!("Loaded ledger: {}", ledger.header().hash)]
    );
}

#[test]
#[should_panic(expected = "xrpl::finishLoadByIndexOrHash : valid ledger fees")]
fn ledger_finish_load_by_index_or_hash_panics_without_fees_at_or_after_fee_epoch() {
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: XRP_LEDGER_EARLIEST_FEES,
            close_time_resolution: 30,
            ..LedgerHeader::default()
        },
        build_state_map_with_items(
            &[(
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees()]),
            )],
            true,
            XRP_LEDGER_EARLIEST_FEES,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, true, XRP_LEDGER_EARLIEST_FEES),
    );

    let _ = ledger.finish_load_by_index_or_hash(&RecordingLedgerJournal::default());
}
