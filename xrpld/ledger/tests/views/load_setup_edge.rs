use basics::base_uint::Uint256;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{
    Fees, Ledger, LedgerHeader, LedgerJournal, amendments_key, calculate_ledger_hash,
    encode_fee_settings_entry, fees_key,
};
use parking_lot::Mutex;
use protocol::{LedgerEntryType, STAmount, STLedgerEntry, feature_xrp_fees, get_field_by_symbol};
use shamap::family::{MissingNodeReporter, NullFullBelowCache, SHAMapFamily, SHAMapNodeFetcher};
use shamap::item::SHAMapItem;
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use shamap::tree_node_cache::TreeNodeCache;
use std::collections::HashMap;
use std::sync::Arc;
use time::Duration;

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

fn typed_amendments_entry_bytes(amendments: &[Uint256]) -> Vec<u8> {
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::Amendments, amendments_key());
    entry.set_field_h256(
        get_field_by_symbol("sfPreviousTxnID"),
        Uint256::from_array([0xB1; 32]),
    );
    entry.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 907);
    entry.set_field_v256(
        get_field_by_symbol("sfAmendments"),
        protocol::STVector256::from_values(
            get_field_by_symbol("sfAmendments"),
            amendments.to_vec(),
        ),
    );
    entry.get_serializer().data().to_vec()
}

fn typed_xrp_fee_settings_entry_bytes(base: u64, reserve: u64, increment: u64) -> Vec<u8> {
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::FeeSettings, fees_key());
    entry.set_field_h256(
        get_field_by_symbol("sfPreviousTxnID"),
        Uint256::from_array([0xB2; 32]),
    );
    entry.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 908);
    entry.set_field_amount(
        get_field_by_symbol("sfBaseFeeDrops"),
        STAmount::new_native(base, false),
    );
    entry.set_field_amount(
        get_field_by_symbol("sfReserveBaseDrops"),
        STAmount::new_native(reserve, false),
    );
    entry.set_field_amount(
        get_field_by_symbol("sfReserveIncrementDrops"),
        STAmount::new_native(increment, false),
    );
    entry.get_serializer().data().to_vec()
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

#[test]
fn ledger_load_immutable_with_family_and_setup_marks_failed_setup_ctor() {
    let missing_amendments_hash = sample_hash(0x96);
    let fee_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            fees_key(),
            encode_fee_settings_entry(
                Fees {
                    base: 10,
                    reserve: 20,
                    increment: 30,
                },
                false,
            ),
        ),
        0,
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(
        usize::from(amendments_key().data()[0] >> 4),
        missing_amendments_hash,
    );
    root.set_child_hash(usize::from(fees_key().data()[0] >> 4), fee_leaf.get_hash());
    root.share_child(usize::from(fees_key().data()[0] >> 4), &fee_leaf);
    root.update_hash_deep();

    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let mut expected = HashMap::new();
    expected.insert(root.get_hash(), root.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-setup-missing-node",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher {
            expected,
            fetches: Mutex::new(Vec::new()),
        },
        SharedReporter(reporter.clone()),
    );
    let journal = RecordingLedgerJournal::default();
    let header = LedgerHeader {
        seq: 803,
        drops: 40,
        parent_hash: sample_hash(0x97),
        account_hash: root.get_hash(),
        parent_close_time: 22,
        close_time: 33,
        close_time_resolution: 44,
        close_flags: 55,
        ..LedgerHeader::default()
    };
    let expected_header_hash = calculate_ledger_hash(&header);

    let (ledger, loaded) = Ledger::load_immutable_with_family_and_setup(
        header,
        true,
        &journal,
        Fees {
            base: 1,
            reserve: 2,
            increment: 3,
        },
        &feature_xrp_fees(),
        &family,
    )
    .expect("setup-aware immutable load should keep bool failure semantics");

    assert!(!loaded);
    assert!(ledger.is_immutable());
    assert_eq!(ledger.header().hash, expected_header_hash);
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 10,
            reserve: 20,
            increment: 30,
        }
    );
    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![root.get_hash(), missing_amendments_hash]
        );
    });
    assert!(journal.warns().is_empty());
    let reporter = reporter.lock();
    assert_eq!(reporter.by_seq, Vec::<(u32, Uint256)>::new());
    assert_eq!(
        reporter.by_hash,
        vec![(*expected_header_hash.as_uint256(), 803)]
    );
}

#[test]
fn ledger_load_immutable_with_family_and_setup_decodes_typed_singleton_payloads() {
    let amendment_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            amendments_key(),
            typed_amendments_entry_bytes(&[feature_xrp_fees(), Uint256::from_array([0xB3; 32])]),
        ),
        0,
    );
    let fee_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(fees_key(), typed_xrp_fee_settings_entry_bytes(44, 55, 66)),
        0,
    );
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(
        usize::from(amendments_key().data()[0] >> 4),
        amendment_leaf.get_hash(),
    );
    root.set_child_hash(usize::from(fees_key().data()[0] >> 4), fee_leaf.get_hash());
    root.update_hash_deep();

    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let mut expected = HashMap::new();
    expected.insert(root.get_hash(), root.clone());
    expected.insert(amendment_leaf.get_hash(), amendment_leaf.clone());
    expected.insert(fee_leaf.get_hash(), fee_leaf.clone());
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-load-setup-typed-singletons",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher {
            expected,
            fetches: Mutex::new(Vec::new()),
        },
        SharedReporter(reporter.clone()),
    );
    let journal = RecordingLedgerJournal::default();
    let header = LedgerHeader {
        seq: 804,
        drops: 40,
        parent_hash: sample_hash(0xB4),
        account_hash: root.get_hash(),
        parent_close_time: 22,
        close_time: 33,
        close_time_resolution: 44,
        close_flags: 55,
        ..LedgerHeader::default()
    };

    let (ledger, loaded) = Ledger::load_immutable_with_family_and_setup(
        header,
        true,
        &journal,
        Fees {
            base: 1,
            reserve: 2,
            increment: 3,
        },
        &feature_xrp_fees(),
        &family,
    )
    .expect("typed singleton setup should decode");

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
    assert!(ledger.rules().enabled(&Uint256::from_array([0xB3; 32])));
    family.with_fetcher(|fetcher| {
        let fetches = fetcher.fetches.lock();
        assert_eq!(fetches.first(), Some(&root.get_hash()));
        assert_eq!(fetches.len(), 3);
        assert!(fetches.contains(&amendment_leaf.get_hash()));
        assert!(fetches.contains(&fee_leaf.get_hash()));
    });
    assert!(journal.warns().is_empty());
    let reporter = reporter.lock();
    assert!(reporter.by_seq.is_empty());
    assert!(reporter.by_hash.is_empty());
}
