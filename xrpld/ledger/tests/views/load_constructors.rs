use basics::base_uint::Uint256;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{
    Fees, Ledger, LedgerConfig, LedgerHeader, LedgerInfoProvider, LedgerJournal, amendments_key,
    calculate_ledger_hash, fees_key,
};
use parking_lot::Mutex;
use protocol::{FeatureSet, encode_amendments_entry, encode_fee_settings_entry, feature_xrp_fees};
use shamap::family::{MissingNodeReporter, NullFullBelowCache, SHAMapFamily, SHAMapNodeFetcher};
use shamap::item::SHAMapItem;
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
    let mut tree = shamap::mutation::MutableTree::new(1);
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
    by_hash: Vec<(Uint256, u32)>,
}

#[derive(Debug)]
struct SharedReporter(Arc<Mutex<RecordingMissingNodeReporter>>);

impl MissingNodeReporter for SharedReporter {
    fn missing_node_acquire_by_seq(&self, ref_num: u32, node_hash: Uint256) {
        self.0.lock().by_seq.push((ref_num, node_hash));
    }

    fn missing_node_acquire_by_hash(&self, ref_hash: Uint256, ref_num: u32) {
        self.0.lock().by_hash.push((ref_hash, ref_num));
    }
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
fn load_immutable_with_family_fetches_roots_in_and_marks_immutable() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x61), vec![0xAA; 20]),
        0,
    );
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x62), vec![0xBB; 20]),
        0,
    );
    let mut expected = HashMap::new();
    expected.insert(tx_root.get_hash(), tx_root.clone());
    expected.insert(state_root.get_hash(), state_root.clone());

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-success",
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

    let (ledger, loaded) = Ledger::load_immutable_with_family(
        LedgerHeader {
            seq: 800,
            hash: sample_hash(0x8F),
            tx_hash: tx_root.get_hash(),
            account_hash: state_root.get_hash(),
            ..LedgerHeader::default()
        },
        false,
        &journal,
        &family,
    );

    assert!(loaded);
    assert!(ledger.is_immutable());
    assert_eq!(ledger.tx_map().state(), SyncState::Immutable);
    assert_eq!(ledger.state_map().state(), SyncState::Immutable);
    assert_eq!(ledger.tx_map().root().get_hash(), tx_root.get_hash());
    assert_eq!(ledger.state_map().root().get_hash(), state_root.get_hash());
    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![tx_root.get_hash(), state_root.get_hash()]
        );
    });
    assert!(journal.infos().is_empty());
    assert!(journal.warns().is_empty());
}

#[test]
fn load_immutable_with_family_warns_and_acquires_by_hash_only_after_failed_load() {
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-miss",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher::default(),
        SharedReporter(reporter.clone()),
    );
    let journal = RecordingLedgerJournal::default();
    let tx_hash = sample_hash(0x91);
    let account_hash = sample_hash(0x92);
    let header = LedgerHeader {
        seq: 801,
        drops: 40,
        parent_hash: sample_hash(0x93),
        tx_hash,
        account_hash,
        parent_close_time: 22,
        close_time: 33,
        close_time_resolution: 44,
        close_flags: 55,
        ..LedgerHeader::default()
    };
    let expected_header_hash = calculate_ledger_hash(&header);

    let (ledger, loaded) = Ledger::load_immutable_with_family(header, true, &journal, &family);

    assert!(!loaded);
    assert!(ledger.is_immutable());
    assert_eq!(ledger.tx_map().state(), SyncState::Immutable);
    assert_eq!(ledger.state_map().state(), SyncState::Immutable);
    assert_eq!(ledger.header().hash, expected_header_hash);
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![tx_hash, account_hash])
    });
    assert_eq!(
        journal.warns(),
        vec![
            "Don't have transaction root for ledger801".to_owned(),
            "Don't have state data root for ledger801".to_owned(),
        ]
    );
    let reporter = reporter.lock();
    assert_eq!(reporter.by_seq, Vec::<(u32, Uint256)>::new());
    assert_eq!(
        reporter.by_hash,
        vec![(*expected_header_hash.as_uint256(), 801)]
    );
}

#[test]
fn load_immutable_with_family_and_setup_decodes_loaded_state_entries_ctor() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x94), vec![0xAB; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees(), sample_uint256(0x95)]),
            ),
            (fees_key(), encode_fee_settings_entry(44, 55, 66, true)),
        ],
        true,
        802,
    );
    let expected_digest = state_map
        .peek_item_with_hash(amendments_key(), &mut |_| None)
        .expect("amendments lookup should succeed")
        .expect("amendments entry should exist")
        .1;
    let state_root = state_map.root();
    let mut expected = HashMap::new();
    expected.insert(tx_root.get_hash(), tx_root.clone());
    expected.insert(state_root.get_hash(), state_root.clone());

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-setup-success",
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

    let (ledger, loaded) = Ledger::load_immutable_with_family_and_setup(
        LedgerHeader {
            seq: 802,
            tx_hash: tx_root.get_hash(),
            account_hash: state_root.get_hash(),
            ..LedgerHeader::default()
        },
        false,
        &journal,
        Fees {
            base: 1,
            reserve: 2,
            increment: 3,
        },
        &feature_xrp_fees(),
        &family,
    )
    .expect("setup-aware immutable load should decode");

    assert!(loaded);
    assert!(ledger.is_immutable());
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 44,
            reserve: 55,
            increment: 66,
        }
    );
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&sample_uint256(0x95)));
    assert_eq!(ledger.rules().digest(), Some(*expected_digest.as_uint256()));
    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![tx_root.get_hash(), state_root.get_hash()]
        );
    });
    assert!(journal.infos().is_empty());
    assert!(journal.warns().is_empty());
}

#[test]
fn load_immutable_with_family_and_config_seeds_rules_and_fees_from_config() {
    let preset = sample_uint256(0x96);
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x97), vec![0xAB; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees(), sample_uint256(0x98)]),
            ),
            (fees_key(), encode_fee_settings_entry(11, 22, 33, false)),
        ],
        true,
        803,
    );
    let expected_digest = state_map
        .peek_item_with_hash(amendments_key(), &mut |_| None)
        .expect("amendments lookup should succeed")
        .expect("amendments entry should exist")
        .1;
    let state_root = state_map.root();
    let mut expected = HashMap::new();
    expected.insert(tx_root.get_hash(), tx_root.clone());
    expected.insert(state_root.get_hash(), state_root.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-config-success",
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
    let config = sample_ledger_config([preset, feature_xrp_fees()]);

    let (ledger, loaded) = Ledger::load_immutable_with_family_and_config(
        LedgerHeader {
            seq: 803,
            tx_hash: tx_root.get_hash(),
            account_hash: state_root.get_hash(),
            ..LedgerHeader::default()
        },
        false,
        &journal,
        &config,
        &family,
    )
    .expect("config-backed immutable load should decode");

    assert!(loaded);
    assert!(ledger.is_immutable());
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 11,
            reserve: 22,
            increment: 33,
        }
    );
    assert!(ledger.rules().enabled(&preset));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&sample_uint256(0x98)));
    assert_eq!(ledger.rules().digest(), Some(*expected_digest.as_uint256()));
    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![tx_root.get_hash(), state_root.get_hash()]
        );
    });
    assert!(journal.warns().is_empty());
}

#[test]
fn load_immutable_with_family_and_config_or_none_returns_some_for_complete_loads() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xA0), vec![0xAA; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees(), sample_uint256(0xA1)]),
            ),
            (fees_key(), encode_fee_settings_entry(12, 23, 34, false)),
        ],
        true,
        805,
    );
    let state_root = state_map.root();
    let mut expected = HashMap::new();
    expected.insert(tx_root.get_hash(), tx_root.clone());
    expected.insert(state_root.get_hash(), state_root.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-option-some",
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
    let config = sample_ledger_config([sample_uint256(0xA2), feature_xrp_fees()]);

    let ledger = Ledger::load_immutable_with_family_and_config_or_none(
        LedgerHeader {
            seq: 805,
            tx_hash: tx_root.get_hash(),
            account_hash: state_root.get_hash(),
            ..LedgerHeader::default()
        },
        false,
        &journal,
        &config,
        &family,
    )
    .expect("option load wrapper should decode")
    .expect("complete load should return Some");

    assert!(ledger.is_immutable());
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 12,
            reserve: 23,
            increment: 34,
        }
    );
    assert!(ledger.rules().enabled(&sample_uint256(0xA2)));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&sample_uint256(0xA1)));
}

#[test]
fn load_immutable_with_family_and_config_or_none_returns_none_for_failed_loads() {
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-option-none",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher::default(),
        SharedReporter(reporter.clone()),
    );
    let journal = RecordingLedgerJournal::default();
    let config = sample_ledger_config([feature_xrp_fees()]);
    let header = LedgerHeader {
        seq: 806,
        drops: 40,
        parent_hash: sample_hash(0xA3),
        tx_hash: sample_hash(0xA4),
        account_hash: sample_hash(0xA5),
        parent_close_time: 22,
        close_time: 33,
        close_time_resolution: 44,
        close_flags: 55,
        ..LedgerHeader::default()
    };
    let expected_header_hash = calculate_ledger_hash(&header);

    let ledger = Ledger::load_immutable_with_family_and_config_or_none(
        header, true, &journal, &config, &family,
    )
    .expect("option load wrapper should preserve decode errors only");

    assert!(ledger.is_none());
    let reporter = reporter.lock();
    assert_eq!(
        reporter.by_hash,
        vec![(*expected_header_hash.as_uint256(), 806)]
    );
}

#[test]
fn load_finished_with_family_and_config_or_none_returns_full_ledger() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xA6), vec![0xFE; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees(), sample_uint256(0xA7)]),
            ),
            (fees_key(), encode_fee_settings_entry(14, 25, 36, false)),
        ],
        true,
        807,
    );
    let state_root = state_map.root();
    let mut expected = HashMap::new();
    expected.insert(tx_root.get_hash(), tx_root.clone());
    expected.insert(state_root.get_hash(), state_root.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-finished-some",
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
    let config = sample_ledger_config([sample_uint256(0xA8), feature_xrp_fees()]);
    let header = LedgerHeader {
        seq: 807,
        drops: 88,
        parent_hash: sample_hash(0xA9),
        tx_hash: tx_root.get_hash(),
        account_hash: state_root.get_hash(),
        parent_close_time: 22,
        close_time: 33,
        close_time_resolution: 44,
        close_flags: 55,
        ..LedgerHeader::default()
    };
    let expected_hash = calculate_ledger_hash(&header);

    let ledger = Ledger::load_finished_with_family_and_config_or_none(
        header, false, &journal, &config, &family,
    )
    .expect("finished load wrapper should decode")
    .expect("complete load should return Some");

    assert!(ledger.is_immutable());
    assert!(ledger.state_map().is_full());
    assert!(ledger.tx_map().is_full());
    assert_eq!(ledger.header().hash, expected_hash);
    assert_eq!(
        journal.infos(),
        vec![format!("Loaded ledger: {}", ledger.header().hash)]
    );
    assert!(ledger.rules().enabled(&sample_uint256(0xA8)));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&sample_uint256(0xA7)));
}

#[test]
fn load_finished_by_hash_with_family_and_config_or_none_matches_requested_hash() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xAA), vec![0xDD; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees()]),
            ),
            (fees_key(), encode_fee_settings_entry(9, 8, 7, false)),
        ],
        true,
        808,
    );
    let state_root = state_map.root();
    let mut expected = HashMap::new();
    expected.insert(tx_root.get_hash(), tx_root.clone());
    expected.insert(state_root.get_hash(), state_root.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-by-hash-match",
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
    let config = sample_ledger_config([feature_xrp_fees()]);
    let header = LedgerHeader {
        seq: 808,
        drops: 77,
        hash: sample_hash(0xAB),
        parent_hash: sample_hash(0xAC),
        tx_hash: tx_root.get_hash(),
        account_hash: state_root.get_hash(),
        parent_close_time: 2,
        close_time: 3,
        close_time_resolution: 30,
        close_flags: 1,
        ..LedgerHeader::default()
    };
    let expected_hash = calculate_ledger_hash(&LedgerHeader {
        hash: SHAMapHash::default(),
        ..header
    });

    let ledger = Ledger::load_finished_by_hash_with_family_and_config_or_none(
        expected_hash,
        header,
        false,
        &journal,
        &config,
        &family,
    )
    .expect("by-hash finished wrapper should decode")
    .expect("matching hash should keep the loaded ledger");

    assert_eq!(ledger.header().hash, expected_hash);
}

#[test]
#[should_panic(expected = "xrpl::loadByHash : ledger hash match if loaded")]
fn load_finished_by_hash_with_family_and_config_or_none_panics_on_hash_mismatch() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xAD), vec![0xCC; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees()]),
            ),
            (fees_key(), encode_fee_settings_entry(5, 6, 7, false)),
        ],
        true,
        809,
    );
    let state_root = state_map.root();
    let mut expected = HashMap::new();
    expected.insert(tx_root.get_hash(), tx_root.clone());
    expected.insert(state_root.get_hash(), state_root.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-by-hash-mismatch",
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
    let config = sample_ledger_config([feature_xrp_fees()]);

    let _ = Ledger::load_finished_by_hash_with_family_and_config_or_none(
        sample_hash(0xAE),
        LedgerHeader {
            seq: 809,
            drops: 66,
            parent_hash: sample_hash(0xAF),
            tx_hash: tx_root.get_hash(),
            account_hash: state_root.get_hash(),
            parent_close_time: 4,
            close_time: 5,
            close_time_resolution: 30,
            close_flags: 0,
            ..LedgerHeader::default()
        },
        false,
        &journal,
        &config,
        &family,
    );
}

#[test]
fn load_by_index_with_provider_and_config_or_none_returns_finished_ledger() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xB0), vec![0x11; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees(), sample_uint256(0xB1)]),
            ),
            (fees_key(), encode_fee_settings_entry(21, 31, 41, false)),
        ],
        true,
        810,
    );
    let state_root = state_map.root();
    let mut expected = HashMap::new();
    expected.insert(tx_root.get_hash(), tx_root.clone());
    expected.insert(state_root.get_hash(), state_root.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-by-index-provider",
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
    let config = sample_ledger_config([sample_uint256(0xB2), feature_xrp_fees()]);
    let header = LedgerHeader {
        seq: 810,
        drops: 55,
        parent_hash: sample_hash(0xB3),
        tx_hash: tx_root.get_hash(),
        account_hash: state_root.get_hash(),
        parent_close_time: 9,
        close_time: 10,
        close_time_resolution: 30,
        close_flags: 0,
        ..LedgerHeader::default()
    };
    let provider = RecordingLedgerInfoProvider {
        by_index: HashMap::from([(810, header)]),
        by_hash: HashMap::new(),
    };

    let ledger = Ledger::load_by_index_with_provider_and_config_or_none(
        810, false, &journal, &config, &family, &provider,
    )
    .expect("index-provider wrapper should decode")
    .expect("provider hit should load a ledger");

    assert!(ledger.is_immutable());
    assert!(ledger.state_map().is_full());
    assert!(ledger.tx_map().is_full());
    assert!(ledger.rules().enabled(&sample_uint256(0xB2)));
    assert!(ledger.rules().enabled(&sample_uint256(0xB1)));
}

#[test]
fn load_by_index_with_provider_and_config_or_none_returns_none_for_missing_header() {
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-by-index-provider-miss",
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

    let ledger = Ledger::load_by_index_with_provider_and_config_or_none(
        999,
        false,
        &RecordingLedgerJournal::default(),
        &sample_ledger_config([]),
        &family,
        &RecordingLedgerInfoProvider::default(),
    )
    .expect("index-provider wrapper should not fail for a miss");

    assert!(ledger.is_none());
}

#[test]
fn load_by_hash_with_provider_and_config_or_none_returns_finished_ledger() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xB4), vec![0x22; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees()]),
            ),
            (fees_key(), encode_fee_settings_entry(4, 5, 6, false)),
        ],
        true,
        811,
    );
    let state_root = state_map.root();
    let mut expected = HashMap::new();
    expected.insert(tx_root.get_hash(), tx_root.clone());
    expected.insert(state_root.get_hash(), state_root.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-by-hash-provider",
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
    let config = sample_ledger_config([feature_xrp_fees()]);
    let header = LedgerHeader {
        seq: 811,
        drops: 44,
        parent_hash: sample_hash(0xB5),
        tx_hash: tx_root.get_hash(),
        account_hash: state_root.get_hash(),
        parent_close_time: 7,
        close_time: 8,
        close_time_resolution: 30,
        close_flags: 0,
        ..LedgerHeader::default()
    };
    let expected_hash = calculate_ledger_hash(&header);
    let provider = RecordingLedgerInfoProvider {
        by_index: HashMap::new(),
        by_hash: HashMap::from([(expected_hash, header)]),
    };

    let ledger = Ledger::load_by_hash_with_provider_and_config_or_none(
        expected_hash,
        false,
        &journal,
        &config,
        &family,
        &provider,
    )
    .expect("hash-provider wrapper should decode")
    .expect("provider hit should load a ledger");

    assert_eq!(ledger.header().hash, expected_hash);
    assert!(ledger.is_immutable());
    assert!(ledger.state_map().is_full());
    assert!(ledger.tx_map().is_full());
}

#[test]
fn load_by_hash_with_provider_and_config_or_none_returns_none_for_missing_header() {
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-by-hash-provider-miss",
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

    let ledger = Ledger::load_by_hash_with_provider_and_config_or_none(
        sample_hash(0xB6),
        false,
        &RecordingLedgerJournal::default(),
        &sample_ledger_config([]),
        &family,
        &RecordingLedgerInfoProvider::default(),
    )
    .expect("hash-provider wrapper should not fail for a miss");

    assert!(ledger.is_none());
}
