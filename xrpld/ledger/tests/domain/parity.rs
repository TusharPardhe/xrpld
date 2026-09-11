use basics::base_uint::{Uint160, Uint256};
use basics::chrono::NetClockTimePoint;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{
    AmendmentsEntry, AmountField, FeeSettingsFields, Fees, INITIAL_XRP_DROPS,
    LEDGER_GENESIS_TIME_RESOLUTION, Ledger, LedgerConfig, LedgerHeader, LedgerInfoProvider,
    LedgerJournal, LedgerSetupEntries, Rules, SLCF_NO_CONSENSUS_TIME, SetupLookup,
    XRP_LEDGER_EARLIEST_FEES, amendments_key, build_genesis_master_account_root_item,
    build_genesis_setup_items, build_genesis_state_items, calculate_ledger_hash, fees_key,
    get_enabled_amendments, get_majority_amendments, get_next_ledger_time_resolution,
    is_flag_ledger, is_voting_ledger, round_close_time,
};
use parking_lot::Mutex;
use protocol::{
    ConstructorAccountRootEntry, ConstructorAmendmentsEntry, ConstructorFeeSettingsEntry,
    DecodedDisabledValidator, DecodedNegativeUnlEntry, FeatureSet, Keylet, LedgerEntryType,
    STArray, STLedgerEntry, STObject, STVector256, decode_constructor_account_root_entry,
    decode_constructor_amendments_entry, decode_constructor_fee_settings_entry,
    decode_ledger_hashes_entry, encode_amendments_entry, feature_xrp_fees, genesis_public_key,
    get_field_by_symbol, negative_unl_keylet, skip_keylet, skip_keylet_for_ledger,
};
use shamap::family::{MissingNodeReporter, NullFullBelowCache, SHAMapFamily, SHAMapNodeFetcher};
use shamap::item::SHAMapItem;
use shamap::mutation::MutableTree;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use shamap::tree_node_cache::TreeNodeCache;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
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

const OBJECT_END: u8 = 0xE1;
const ARRAY_END: u8 = 0xF1;

fn encode_field_id(field_type: u8, field_name: u8) -> Vec<u8> {
    if field_type < 16 && field_name < 16 {
        vec![(field_type << 4) | field_name]
    } else if field_type < 16 {
        vec![field_type << 4, field_name]
    } else if field_name < 16 {
        vec![field_name, field_type]
    } else {
        vec![0, field_type, field_name]
    }
}

fn encode_u16_field(field_name: u8, value: u16) -> Vec<u8> {
    let mut bytes = encode_field_id(1, field_name);
    bytes.extend_from_slice(&value.to_be_bytes());
    bytes
}

fn encode_u32_field(field_name: u8, value: u32) -> Vec<u8> {
    let mut bytes = encode_field_id(2, field_name);
    bytes.extend_from_slice(&value.to_be_bytes());
    bytes
}

fn encode_u256_field(field_name: u8, value: basics::base_uint::Uint256) -> Vec<u8> {
    let mut bytes = encode_field_id(5, field_name);
    bytes.extend_from_slice(value.data());
    bytes
}

fn encode_u64_field(field_name: u8, value: u64) -> Vec<u8> {
    let mut bytes = encode_field_id(3, field_name);
    bytes.extend_from_slice(&value.to_be_bytes());
    bytes
}

fn encode_uint256_field(field_name: u8, value: Uint256) -> Vec<u8> {
    let mut bytes = encode_field_id(5, field_name);
    bytes.extend_from_slice(value.data());
    bytes
}

fn encode_vector256_field(field_name: u8, values: &[Uint256]) -> Vec<u8> {
    let mut bytes = encode_field_id(19, field_name);
    let payload_len = values.len() * Uint256::BYTES;
    bytes.push(u8::try_from(payload_len).expect("small vector256 payload must fit in one byte"));
    for value in values {
        bytes.extend_from_slice(value.data());
    }
    bytes
}

fn encode_native_amount_field(field_name: u8, value: u64) -> Vec<u8> {
    let mut bytes = encode_field_id(6, field_name);
    bytes.extend_from_slice(&(value | 0x4000_0000_0000_0000).to_be_bytes());
    bytes
}

fn encode_account_field(field_name: u8, value: Uint160) -> Vec<u8> {
    let mut bytes = encode_field_id(8, field_name);
    bytes.push(
        u8::try_from(Uint160::BYTES).expect("account ids should fit in one-byte VL prefixes"),
    );
    bytes.extend_from_slice(value.data());
    bytes
}

fn encode_negative_native_amount_field(field_name: u8, value: u64) -> Vec<u8> {
    let mut bytes = encode_field_id(6, field_name);
    bytes.extend_from_slice(&value.to_be_bytes());
    bytes
}

fn amendments_entry_bytes(amendments: &[Uint256], include_majorities: bool) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&encode_u16_field(1, 0x0066));
    bytes.extend_from_slice(&encode_vector256_field(3, amendments));
    if include_majorities {
        bytes.extend_from_slice(&encode_field_id(15, 16));
        bytes.extend_from_slice(&encode_field_id(14, 18));
        bytes.extend_from_slice(&encode_uint256_field(19, sample_uint256(0xA6)));
        bytes.extend_from_slice(&encode_u32_field(7, 999));
        bytes.push(ARRAY_END);
    }
    bytes
}

fn negative_unl_entry_bytes(
    disabled_validators: &[(Vec<u8>, u32)],
    validator_to_disable: Option<Vec<u8>>,
    validator_to_re_enable: Option<Vec<u8>>,
) -> Vec<u8> {
    let sf_disabled_validator = get_field_by_symbol("sfDisabledValidator");
    let sf_disabled_validators = get_field_by_symbol("sfDisabledValidators");
    let sf_first_ledger_sequence = get_field_by_symbol("sfFirstLedgerSequence");
    let sf_public_key = get_field_by_symbol("sfPublicKey");
    let sf_validator_to_disable = get_field_by_symbol("sfValidatorToDisable");
    let sf_validator_to_re_enable = get_field_by_symbol("sfValidatorToReEnable");

    let mut entry = STLedgerEntry::new(negative_unl_keylet());
    if !disabled_validators.is_empty() {
        let mut array = STArray::new(sf_disabled_validators);
        for (public_key, first_ledger_sequence) in disabled_validators {
            let mut validator = STObject::make_inner_object(sf_disabled_validator);
            validator.set_field_vl(sf_public_key, public_key);
            validator.set_field_u32(sf_first_ledger_sequence, *first_ledger_sequence);
            array.push_back(validator);
        }
        entry.set_field_array(sf_disabled_validators, array);
    }
    if let Some(validator_to_disable) = validator_to_disable {
        entry.set_field_vl(sf_validator_to_disable, &validator_to_disable);
    }
    if let Some(validator_to_re_enable) = validator_to_re_enable {
        entry.set_field_vl(sf_validator_to_re_enable, &validator_to_re_enable);
    }

    entry.get_serializer().data().to_vec()
}

fn decode_negative_unl_from_ledger(ledger: &Ledger) -> Option<DecodedNegativeUnlEntry> {
    let sf_disabled_validators = get_field_by_symbol("sfDisabledValidators");
    let sf_first_ledger_sequence = get_field_by_symbol("sfFirstLedgerSequence");
    let sf_public_key = get_field_by_symbol("sfPublicKey");
    let sf_validator_to_disable = get_field_by_symbol("sfValidatorToDisable");
    let sf_validator_to_re_enable = get_field_by_symbol("sfValidatorToReEnable");

    let sle = ledger
        .read(negative_unl_keylet())
        .expect("NegativeUNL lookup should succeed")?;
    let disabled_validators = if sle.is_field_present(sf_disabled_validators) {
        sle.get_field_array(sf_disabled_validators)
            .iter()
            .map(|validator| DecodedDisabledValidator {
                public_key: validator.get_field_vl(sf_public_key),
                first_ledger_sequence: validator.get_field_u32(sf_first_ledger_sequence),
            })
            .collect()
    } else {
        Vec::new()
    };

    Some(DecodedNegativeUnlEntry {
        disabled_validators,
        validator_to_disable: sle
            .is_field_present(sf_validator_to_disable)
            .then(|| sle.get_field_vl(sf_validator_to_disable)),
        validator_to_re_enable: sle
            .is_field_present(sf_validator_to_re_enable)
            .then(|| sle.get_field_vl(sf_validator_to_re_enable)),
        previous_txn_id: None,
        previous_txn_lgr_seq: None,
    })
}

fn fee_settings_entry_bytes(
    legacy: Option<(u64, u32, u32)>,
    xrp: Option<(Vec<u8>, Vec<u8>, Vec<u8>)>,
) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&encode_u16_field(1, 0x0073));
    bytes.extend_from_slice(&encode_u32_field(2, 0)); // Flags
    if let Some((base, reserve, increment)) = legacy {
        bytes.extend_from_slice(&encode_u32_field(30, 256));
        bytes.extend_from_slice(&encode_u32_field(31, reserve));
        bytes.extend_from_slice(&encode_u32_field(32, increment));
        bytes.extend_from_slice(&encode_u64_field(5, base));
    }
    if let Some((base, reserve, increment)) = xrp {
        bytes.extend_from_slice(&base);
        bytes.extend_from_slice(&reserve);
        bytes.extend_from_slice(&increment);
    }
    bytes
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

fn typed_amendments_entry_bytes(amendments: &[Uint256]) -> Vec<u8> {
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::Amendments, amendments_key());
    entry.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), sample_uint256(0xD4));
    entry.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 1107);
    entry.set_field_v256(
        get_field_by_symbol("sfAmendments"),
        STVector256::from_values(get_field_by_symbol("sfAmendments"), amendments.to_vec()),
    );
    entry.get_serializer().data().to_vec()
}

fn typed_legacy_fee_settings_entry_bytes(base: u64, reserve: u32, increment: u32) -> Vec<u8> {
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::FeeSettings, fees_key());
    entry.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), sample_uint256(0xD5));
    entry.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 1108);
    entry.set_field_u64(get_field_by_symbol("sfBaseFee"), base);
    entry.set_field_u32(get_field_by_symbol("sfReferenceFeeUnits"), 256);
    entry.set_field_u32(get_field_by_symbol("sfReserveBase"), reserve);
    entry.set_field_u32(get_field_by_symbol("sfReserveIncrement"), increment);
    entry.get_serializer().data().to_vec()
}

#[test]
fn ledger_owner_read_exists_digest_and_peek_match_cpp_for_typed_sles() {
    let amendment = sample_uint256(0xD7);
    let state_map = build_state_map_with_items(
        &[(amendments_key(), typed_amendments_entry_bytes(&[amendment]))],
        false,
        1201,
    );
    let ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 1201,
            ..LedgerHeader::default()
        },
        state_map,
        SyncTree::new_with_type(SHAMapType::Transaction, false, 1201),
    );
    let expected_digest = ledger
        .state_map()
        .peek_item_with_hash(amendments_key(), &mut |_| None)
        .expect("typed amendments lookup should succeed")
        .expect("typed amendments entry should exist")
        .1;

    assert!(
        ledger
            .exists_keylet(Keylet::new(LedgerEntryType::FeeSettings, amendments_key()))
            .expect("exists_keylet should follow raw key presence")
    );
    assert!(
        ledger
            .exists(amendments_key())
            .expect("exists should follow raw key presence")
    );
    assert_eq!(
        ledger
            .digest(amendments_key())
            .expect("digest lookup should succeed"),
        Some(*expected_digest.as_uint256())
    );

    let read = ledger
        .read(Keylet::new(LedgerEntryType::Amendments, amendments_key()))
        .expect("typed owner read should not traverse missing nodes")
        .expect("typed amendments payload should deserialize");
    assert_eq!(read.get_type(), LedgerEntryType::Amendments);
    assert_eq!(
        read.get_field_v256(get_field_by_symbol("sfAmendments"))
            .value(),
        &[amendment]
    );

    let peek = ledger
        .peek(Keylet::new(LedgerEntryType::Amendments, amendments_key()))
        .expect("typed owner peek should not traverse missing nodes")
        .expect("typed amendments payload should deserialize");
    assert_eq!(peek, read);

    assert!(
        ledger
            .read(Keylet::new(LedgerEntryType::FeeSettings, amendments_key()))
            .expect("typed owner read should succeed for wrong-type probes")
            .is_none()
    );
    assert_eq!(
        ledger
            .digest(sample_uint256(0xD8))
            .expect("missing digest lookup should succeed"),
        None
    );
}

#[test]
fn ledger_owner_read_rejects_constructor_style_singletons_even_when_present() {
    let state_map = build_state_map_with_items(
        &[(
            amendments_key(),
            amendments_entry_bytes(&[sample_uint256(0xD9)], false),
        )],
        false,
        1202,
    );
    let ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 1202,
            ..LedgerHeader::default()
        },
        state_map,
        SyncTree::new_with_type(SHAMapType::Transaction, false, 1202),
    );

    assert!(
        ledger
            .exists_keylet(Keylet::new(LedgerEntryType::Amendments, amendments_key()))
            .expect("constructor payload still occupies the key")
    );
    assert!(
        ledger
            .digest(amendments_key())
            .expect("constructor payload still has a hash")
            .is_some()
    );
    assert!(
        ledger
            .read(Keylet::new(LedgerEntryType::Amendments, amendments_key()))
            .expect("constructor payload read should not throw")
            .is_some(),
        "C++ inserts defaults for missing required fields during deserialization"
    );
}

#[test]
fn ledger_succ_upper_bound_and_last_limit() {
    let low = sample_uint256(0xE1);
    let mid = sample_uint256(0xE2);
    let high = sample_uint256(0xE3);
    let state_map = build_state_map_with_items(
        &[
            (low, vec![0x01; 12]),
            (mid, vec![0x02; 12]),
            (high, vec![0x03; 12]),
        ],
        false,
        1203,
    );
    let ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 1203,
            ..LedgerHeader::default()
        },
        state_map,
        SyncTree::new_with_type(SHAMapType::Transaction, false, 1203),
    );

    assert_eq!(
        ledger
            .succ(sample_uint256(0x00), None)
            .expect("succ before first should succeed"),
        Some(low)
    );
    assert_eq!(
        ledger
            .succ(low, None)
            .expect("succ from first should succeed"),
        Some(mid)
    );
    assert_eq!(
        ledger
            .succ(mid, Some(high))
            .expect("succ with last guard should succeed"),
        None
    );
    assert_eq!(
        ledger
            .succ(mid, Some(sample_uint256(0xFF)))
            .expect("succ with later last bound should succeed"),
        Some(high)
    );
    assert_eq!(
        ledger.succ(high, None).expect("succ at end should succeed"),
        None
    );
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
fn ledger_new_matches_narrow_cpp_map_roles() {
    let ledger = Ledger::new(
        LedgerHeader {
            seq: 500,
            ..LedgerHeader::default()
        },
        true,
    );

    assert_eq!(ledger.state_map().map_type(), SHAMapType::State);
    assert_eq!(ledger.tx_map().map_type(), SHAMapType::Transaction);
}

#[test]
fn ledger_from_previous_matches_current_cpp_follow_ledger_header_and_snapshot_roles() {
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x31), vec![0x61; 20]),
        0,
    );
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x32), vec![0x62; 20]),
        0,
    );
    let previous = Ledger::from_maps(
        LedgerHeader {
            seq: 900,
            hash: sample_hash(0x21),
            drops: 55,
            close_time: 120,
            close_time_resolution: 30,
            close_flags: 0,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_root.clone(),
            SHAMapType::State,
            true,
            900,
            SyncState::Immutable,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            900,
            SyncState::Immutable,
        ),
    );
    previous.state_map().set_full();
    previous.tx_map().set_full();

    let next = Ledger::from_previous(&previous, 777);

    assert!(!next.is_immutable());
    assert_eq!(next.header().seq, 901);
    assert_eq!(next.header().parent_close_time, 120);
    assert_eq!(
        next.header().hash,
        SHAMapHash::new(sample_uint256(0x21).next())
    );
    assert_eq!(next.header().parent_hash, sample_hash(0x21));
    assert_eq!(next.header().drops, 55);
    assert_eq!(next.header().close_time_resolution, 30);
    assert_eq!(next.header().close_time, 150);
    assert_eq!(next.header().tx_hash, SHAMapHash::default());
    assert_eq!(next.header().account_hash, SHAMapHash::default());
    assert_eq!(next.state_map().map_type(), SHAMapType::State);
    assert_eq!(next.state_map().state(), SyncState::Modifying);
    assert!(!next.state_map().is_full());
    assert_eq!(next.state_map().root().get_hash(), state_root.get_hash());
    assert_eq!(next.tx_map().map_type(), SHAMapType::Transaction);
    assert_eq!(next.tx_map().state(), SyncState::Modifying);
    assert!(!next.tx_map().is_full());
    assert!(next.tx_map().root().is_empty());
}

#[test]
fn ledger_from_previous_rounds_supplied_close_time_when_previous_close_time_is_zero() {
    let previous = Ledger::new(
        LedgerHeader {
            seq: 7,
            hash: sample_hash(0x41),
            close_time: 0,
            close_time_resolution: 30,
            close_flags: 0,
            ..LedgerHeader::default()
        },
        true,
    );

    let next = Ledger::from_previous(&previous, 31);

    assert_eq!(next.header().seq, 8);
    assert_eq!(next.header().parent_close_time, 0);
    assert_eq!(next.header().close_time_resolution, 20);
    assert_eq!(next.header().close_time, 40);
}

#[test]
fn ledger_timing_helpers_match_current_cpp_examples() {
    assert_eq!(get_next_ledger_time_resolution(30, true, 8), 20);
    assert_eq!(get_next_ledger_time_resolution(20, true, 16), 10);
    assert_eq!(get_next_ledger_time_resolution(10, true, 24), 10);
    assert_eq!(get_next_ledger_time_resolution(30, false, 1), 60);
    assert_eq!(get_next_ledger_time_resolution(60, false, 2), 90);
    assert_eq!(get_next_ledger_time_resolution(120, false, 3), 120);

    assert_eq!(round_close_time(0, 30), 0);
    assert_eq!(round_close_time(29, 60), 0);
    assert_eq!(round_close_time(30, 1), 30);
    assert_eq!(round_close_time(31, 60), 60);
    assert_eq!(round_close_time(30, 60), 60);
    assert_eq!(round_close_time(59, 60), 60);
    assert_eq!(round_close_time(60, 60), 60);
    assert_eq!(round_close_time(61, 60), 60);
}

#[test]
fn ledger_walk_ledger_serial_matches_current_cpp_root_fetch_and_logging_roles() {
    let account_hash = sample_hash(0xA1);
    let tx_hash = sample_hash(0xB2);
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-walk-serial",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher::default(),
        SharedReporter(reporter.clone()),
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 600,
            tx_hash,
            account_hash,
            ..LedgerHeader::default()
        },
        SyncTree::new_with_type(SHAMapType::State, true, 11),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 22),
    );
    let journal = RecordingLedgerJournal::default();

    ledger.set_full();

    assert!(!ledger.walk_ledger_with_family(&journal, false, &family));
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![account_hash, tx_hash])
    });
    assert_eq!(
        reporter.lock().by_seq,
        vec![
            (600, *account_hash.as_uint256()),
            (600, *tx_hash.as_uint256())
        ]
    );
    assert_eq!(
        journal.infos(),
        vec![
            format!(
                "1 missing account node(s)First: Missing Node: State Tree: hash {account_hash}"
            ),
            format!(
                "1 missing transaction node(s)First: Missing Node: Transaction Tree: hash {tx_hash}"
            ),
        ]
    );
}

#[test]
fn ledger_walk_ledger_parallel_returns_state_walk_result_and_skips_tx_tree() {
    let state_missing_hash = sample_hash(0xC1);
    let tx_hash = sample_hash(0xD2);
    let state_inner = SHAMapTreeNode::new_inner(1);
    state_inner.set_child_hash(7, state_missing_hash);
    state_inner.update_hash();

    let state_root = SHAMapTreeNode::new_inner(1);
    state_root.set_child_hash(2, state_inner.get_hash());
    state_root.share_child(2, &state_inner);
    state_root.update_hash_deep();

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-walk-parallel",
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
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 700,
            tx_hash,
            account_hash: state_root.get_hash(),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            700,
            SyncState::Modifying,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 700),
    );
    let journal = RecordingLedgerJournal::default();

    // With the corrected parallel path, a genuinely missing descendant that
    // the fetcher cannot resolve causes the walk to correctly report incomplete.
    assert!(!ledger.walk_ledger_with_family(&journal, true, &family));
    family.with_fetcher(|fetcher| {
        assert_eq!(
            fetcher.fetches.lock().clone(),
            vec![state_missing_hash, tx_hash]
        )
    });
}

#[test]
fn ledger_walk_ledger_serial_checks_tx_tree_after_missing_account_root() {
    let account_hash = sample_hash(0xE1);
    let tx_root_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x44), vec![0x55; 16]),
        0,
    );
    let tx_hash = tx_root_leaf.get_hash();
    let mut expected = HashMap::new();
    expected.insert(tx_hash, tx_root_leaf.clone());

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-walk-after-account-miss",
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
    let mut ledger = Ledger::new(
        LedgerHeader {
            seq: 701,
            tx_hash,
            account_hash,
            ..LedgerHeader::default()
        },
        true,
    );
    let journal = RecordingLedgerJournal::default();

    assert!(!ledger.walk_ledger_with_family(&journal, false, &family));
    family.with_fetcher(|fetcher| {
        assert_eq!(fetcher.fetches.lock().clone(), vec![account_hash, tx_hash])
    });
    assert_eq!(
        journal.infos(),
        vec![format!(
            "1 missing account node(s)First: Missing Node: State Tree: hash {account_hash}"
        )]
    );
}

#[test]
fn ledger_set_immutable_with_rehash_pulls_map_hashes_into_header_and_hashes_ledger() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x71), vec![0x11; 20]),
        0,
    );
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x72), vec![0x22; 20]),
        0,
    );
    let tx_hash = tx_root.get_hash();
    let account_hash = state_root.get_hash();
    let mut expected_header = LedgerHeader {
        seq: 802,
        drops: 50,
        tx_hash,
        account_hash,
        parent_hash: sample_hash(0x73),
        parent_close_time: 60,
        close_time: 61,
        close_time_resolution: 62,
        close_flags: 63,
        ..LedgerHeader::default()
    };
    let expected_hash = calculate_ledger_hash(&expected_header);

    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 802,
            drops: 50,
            parent_hash: sample_hash(0x73),
            parent_close_time: 60,
            close_time: 61,
            close_time_resolution: 62,
            close_flags: 63,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            802,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            802,
            SyncState::Modifying,
        ),
    );

    ledger.set_immutable(true);

    assert!(ledger.is_immutable());
    assert_eq!(ledger.tx_map().state(), SyncState::Immutable);
    assert_eq!(ledger.state_map().state(), SyncState::Immutable);
    expected_header.hash = expected_hash;
    assert_eq!(ledger.header(), expected_header);
}

#[test]
fn ledger_set_immutable_without_rehash_keeps_existing_header_hashes() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x81), vec![0x33; 20]),
        0,
    );
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x82), vec![0x44; 20]),
        0,
    );
    let original = LedgerHeader {
        seq: 803,
        hash: sample_hash(0x84),
        tx_hash: sample_hash(0x85),
        account_hash: sample_hash(0x86),
        ..LedgerHeader::default()
    };
    let mut ledger = Ledger::from_maps(
        original,
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            803,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            803,
            SyncState::Modifying,
        ),
    );

    ledger.set_immutable(false);

    assert!(ledger.is_immutable());
    assert_eq!(ledger.tx_map().state(), SyncState::Immutable);
    assert_eq!(ledger.state_map().state(), SyncState::Immutable);
    assert_eq!(ledger.header(), original);
}

#[test]
fn ledger_set_immutable_and_setup_from_state_map_runs_setup_after_finalization() {
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0x88)], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(
                    None,
                    Some((
                        encode_native_amount_field(22, 44),
                        encode_native_amount_field(23, 55),
                        encode_native_amount_field(24, 66),
                    )),
                ),
            ),
        ],
        false,
        803,
    );
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x89), vec![0x45; 20]),
        0,
    );
    let expected_digest = state_map
        .peek_item_with_hash(amendments_key(), &mut |_| None)
        .expect("amendments lookup should succeed")
        .expect("amendments entry should exist")
        .1;
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 803,
            parent_hash: sample_hash(0x8A),
            ..LedgerHeader::default()
        },
        state_map,
        SyncTree::from_root_with_type(
            tx_root.clone(),
            SHAMapType::Transaction,
            false,
            803,
            SyncState::Modifying,
        ),
    );
    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });

    let ok = ledger
        .set_immutable_and_setup_from_state_map(true, &feature_xrp_fees())
        .expect("setup after finalization should decode");

    assert!(ok);
    assert!(ledger.is_immutable());
    assert_eq!(ledger.tx_map().state(), SyncState::Immutable);
    assert_eq!(ledger.state_map().state(), SyncState::Immutable);
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 44,
            reserve: 55,
            increment: 66,
        }
    );
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&sample_uint256(0x88)));
    assert_eq!(ledger.rules().digest(), Some(*expected_digest.as_uint256()));
}

#[test]
fn ledger_set_immutable_and_setup_from_config_reseeds_presets_and_applies_defaults() {
    let preset = sample_uint256(0x8B);
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                typed_amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0x8C)]),
            ),
            (
                fees_key(),
                typed_legacy_fee_settings_entry_bytes(44, 55, 66),
            ),
        ],
        false,
        804,
    );
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x8D), vec![0x45; 20]),
        0,
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 804,
            parent_hash: sample_hash(0x8E),
            ..LedgerHeader::default()
        },
        state_map,
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            false,
            804,
            SyncState::Modifying,
        ),
    );
    let config = sample_ledger_config([preset, feature_xrp_fees()]);

    let ok = ledger
        .set_immutable_and_setup_from_config(true, &config)
        .expect("config-backed finalization setup should decode");

    assert!(ok);
    assert!(ledger.is_immutable());
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 44,
            reserve: 55,
            increment: 66
        }
    );
    assert!(ledger.rules().enabled(&preset));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&sample_uint256(0x8C)));
}

#[test]
fn ledger_set_accepted_with_correct_close_time_updates_header_and_finalizes() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x91), vec![0x51; 20]),
        0,
    );
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x92), vec![0x52; 20]),
        0,
    );
    let tx_hash = tx_root.get_hash();
    let account_hash = state_root.get_hash();
    let mut expected_header = LedgerHeader {
        seq: 804,
        drops: 75,
        parent_hash: sample_hash(0x93),
        tx_hash,
        account_hash,
        parent_close_time: 22,
        close_time: 123,
        close_time_resolution: 20,
        close_flags: 0,
        ..LedgerHeader::default()
    };
    expected_header.hash = calculate_ledger_hash(&expected_header);

    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 804,
            drops: 75,
            parent_hash: sample_hash(0x93),
            parent_close_time: 22,
            close_time: 44,
            close_time_resolution: 30,
            close_flags: SLCF_NO_CONSENSUS_TIME,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            804,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            804,
            SyncState::Modifying,
        ),
    );

    ledger.set_accepted(123, 20, true);

    assert!(ledger.is_immutable());
    assert_eq!(ledger.tx_map().state(), SyncState::Immutable);
    assert_eq!(ledger.state_map().state(), SyncState::Immutable);
    assert_eq!(ledger.header(), expected_header);
}

#[test]
fn ledger_set_accepted_and_setup_from_config_preserves_finalized_close_fields() {
    let preset = sample_uint256(0xA8);
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                typed_amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0xA9)]),
            ),
            (
                fees_key(),
                typed_legacy_fee_settings_entry_bytes(10, 20, 30),
            ),
        ],
        false,
        806,
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 806,
            drops: 80,
            parent_hash: sample_hash(0xAA),
            ..LedgerHeader::default()
        },
        state_map,
        SyncTree::new_with_type(SHAMapType::Transaction, false, 806),
    );
    let config = sample_ledger_config([preset, feature_xrp_fees()]);

    let ok = ledger
        .set_accepted_and_setup_from_config(321, 60, false, &config)
        .expect("config-backed accepted setup should decode");

    assert!(ok);
    assert!(ledger.is_immutable());
    assert_eq!(ledger.header().close_time, 321);
    assert_eq!(ledger.header().close_time_resolution, 60);
    assert_eq!(ledger.header().close_flags, SLCF_NO_CONSENSUS_TIME);
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 10,
            reserve: 20,
            increment: 30
        }
    );
    assert!(ledger.rules().enabled(&preset));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&sample_uint256(0xA9)));
}

#[test]
fn ledger_set_accepted_and_setup_from_state_map_preserves_bool_setup_outcome() {
    let missing_amendments_hash = sample_hash(0xA4);
    let fee_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            fees_key(),
            fee_settings_entry_bytes(Some((10, 20, 30)), None),
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

    let original_rules = Rules::from_ledger(
        [feature_xrp_fees()],
        sample_uint256(0xA5),
        [sample_uint256(0xA6)],
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 805,
            drops: 80,
            parent_hash: sample_hash(0xA7),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(root, SHAMapType::State, false, 805, SyncState::Modifying),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 805),
    );
    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });
    ledger.set_rules(original_rules.clone());

    let ok = ledger
        .set_accepted_and_setup_from_state_map(321, 60, false, &feature_xrp_fees())
        .expect("setup after acceptance should preserve bool failure semantics");

    assert!(!ok);
    assert!(ledger.is_immutable());
    assert_eq!(ledger.header().close_time, 321);
    assert_eq!(ledger.header().close_time_resolution, 60);
    assert_eq!(ledger.header().close_flags, SLCF_NO_CONSENSUS_TIME);
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 10,
            reserve: 20,
            increment: 30,
        }
    );
    assert_eq!(ledger.rules(), &original_rules);
}

#[test]
fn ledger_set_accepted_with_incorrect_close_time_sets_no_consensus_flag() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xA1), vec![0x61; 20]),
        0,
    );
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0xA2), vec![0x62; 20]),
        0,
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 805,
            drops: 80,
            parent_hash: sample_hash(0xA3),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_root.clone(),
            SHAMapType::State,
            true,
            805,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_root.clone(),
            SHAMapType::Transaction,
            true,
            805,
            SyncState::Modifying,
        ),
    );

    ledger.set_accepted(321, 60, false);

    assert!(ledger.is_immutable());
    assert_eq!(ledger.header().close_time, 321);
    assert_eq!(ledger.header().close_time_resolution, 60);
    assert_eq!(ledger.header().close_flags, SLCF_NO_CONSENSUS_TIME);
    assert_eq!(ledger.header().tx_hash, tx_root.get_hash());
    assert_eq!(ledger.header().account_hash, state_root.get_hash());
}

#[test]
fn ledger_set_validated_flips_only_the_validated_flag() {
    let original = LedgerHeader {
        seq: 806,
        hash: sample_hash(0xB1),
        parent_hash: sample_hash(0xB2),
        tx_hash: sample_hash(0xB3),
        account_hash: sample_hash(0xB4),
        drops: 90,
        parent_close_time: 10,
        close_time: 20,
        validated: false,
        accepted: false,
        close_time_resolution: 30,
        close_flags: SLCF_NO_CONSENSUS_TIME,
    };
    let mut ledger = Ledger::new(original, true);

    ledger.set_validated();

    assert!(ledger.header().validated);
    assert!(!ledger.header().accepted);
    assert_eq!(ledger.header().seq, original.seq);
    assert_eq!(ledger.header().hash, original.hash);
    assert_eq!(ledger.header().parent_hash, original.parent_hash);
    assert_eq!(ledger.header().tx_hash, original.tx_hash);
    assert_eq!(ledger.header().account_hash, original.account_hash);
    assert_eq!(ledger.header().drops, original.drops);
    assert_eq!(
        ledger.header().parent_close_time,
        original.parent_close_time
    );
    assert_eq!(ledger.header().close_time, original.close_time);
    assert_eq!(
        ledger.header().close_time_resolution,
        original.close_time_resolution
    );
    assert_eq!(ledger.header().close_flags, original.close_flags);
}

#[test]
fn ledger_from_header_hashes_matches_current_cpp_known_hash_constructor_role() {
    let input = LedgerHeader {
        seq: 807,
        hash: sample_hash(0xC0),
        parent_hash: sample_hash(0xC1),
        tx_hash: sample_hash(0xC2),
        account_hash: sample_hash(0xC3),
        drops: 91,
        parent_close_time: 14,
        close_time: 28,
        validated: true,
        accepted: true,
        close_time_resolution: 30,
        close_flags: SLCF_NO_CONSENSUS_TIME,
    };
    let mut expected = input;
    expected.hash = calculate_ledger_hash(&expected);

    let ledger = Ledger::from_header_hashes(input);

    assert!(ledger.is_immutable());
    assert_eq!(ledger.header(), expected);
    assert_eq!(ledger.tx_map().map_type(), SHAMapType::Transaction);
    assert_eq!(ledger.tx_map().state(), SyncState::Synching);
    assert_eq!(ledger.state_map().map_type(), SHAMapType::State);
    assert_eq!(ledger.state_map().state(), SyncState::Synching);
    assert!(ledger.tx_map().root().is_inner());
    assert!(ledger.tx_map().root().is_empty());
    assert!(ledger.state_map().root().is_inner());
    assert!(ledger.state_map().root().is_empty());
}

#[test]
fn ledger_from_header_hashes_with_config_seeds_preset_rules() {
    let preset = sample_uint256(0xC4);
    let config = sample_ledger_config([preset, feature_xrp_fees()]);
    let original = LedgerHeader {
        seq: 809,
        parent_hash: sample_hash(0xC5),
        tx_hash: sample_hash(0xC6),
        account_hash: sample_hash(0xC7),
        ..LedgerHeader::default()
    };
    let mut expected = original;
    expected.hash = calculate_ledger_hash(&expected);

    let ledger = Ledger::from_header_hashes_with_config(original, &config);

    assert!(ledger.is_immutable());
    assert_eq!(ledger.header(), expected);
    assert!(ledger.rules().enabled(&preset));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert_eq!(ledger.rules().digest(), None);
    assert_eq!(ledger.tx_map().state(), SyncState::Synching);
    assert_eq!(ledger.state_map().state(), SyncState::Synching);
}

#[test]
fn ledger_from_ledger_seq_and_close_time_matches_narrow_constructor_prefix() {
    let ledger = Ledger::from_ledger_seq_and_close_time(810, 456, true);

    assert!(!ledger.is_immutable());
    assert_eq!(ledger.header().seq, 810);
    assert_eq!(ledger.header().close_time, 456);
    assert_eq!(
        ledger.header().close_time_resolution,
        ledger::LEDGER_DEFAULT_TIME_RESOLUTION
    );
    assert_eq!(ledger.header().hash, SHAMapHash::default());
    assert_eq!(ledger.header().tx_hash, SHAMapHash::default());
    assert_eq!(ledger.header().account_hash, SHAMapHash::default());
    assert!(!ledger.header().validated);
    assert!(!ledger.header().accepted);
    assert_eq!(ledger.tx_map().map_type(), SHAMapType::Transaction);
    assert_eq!(ledger.tx_map().state(), SyncState::Modifying);
    assert_eq!(ledger.state_map().map_type(), SHAMapType::State);
    assert_eq!(ledger.state_map().state(), SyncState::Modifying);
}

#[test]
fn ledger_from_ledger_seq_and_close_time_with_setup_applies_defaults_and_presets() {
    let preset = sample_uint256(0x49);
    let ledger = Ledger::from_ledger_seq_and_close_time_with_setup(
        811,
        789,
        true,
        Fees {
            base: 10,
            reserve: 20,
            increment: 30,
        },
        [preset, feature_xrp_fees()],
        &feature_xrp_fees(),
    )
    .expect("empty constructor setup path should not fail");

    assert!(!ledger.is_immutable());
    assert_eq!(ledger.header().seq, 811);
    assert_eq!(ledger.header().close_time, 789);
    assert_eq!(
        ledger.header().close_time_resolution,
        ledger::LEDGER_DEFAULT_TIME_RESOLUTION
    );
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 10,
            reserve: 20,
            increment: 30,
        }
    );
    assert!(ledger.rules().enabled(&preset));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert_eq!(ledger.rules().digest(), None);
    assert_eq!(ledger.tx_map().state(), SyncState::Modifying);
    assert_eq!(ledger.state_map().state(), SyncState::Modifying);
}

#[test]
fn ledger_from_ledger_seq_and_close_time_with_config_uses_real_config_surface() {
    let preset = sample_uint256(0x4A);
    let config = sample_ledger_config([preset, feature_xrp_fees()]);

    let ledger = Ledger::from_ledger_seq_and_close_time_with_config(812, 790, true, &config)
        .expect("config-backed constructor setup path should not fail");

    assert!(!ledger.is_immutable());
    assert_eq!(ledger.header().seq, 812);
    assert_eq!(ledger.header().close_time, 790);
    assert_eq!(ledger.fees(), config.fees);
    assert!(ledger.rules().enabled(&preset));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert_eq!(ledger.rules().digest(), None);
}

#[test]
fn ledger_set_ledger_info_replaces_header_without_touching_owner_state() {
    let original = LedgerHeader {
        seq: 808,
        hash: sample_hash(0xD1),
        tx_hash: sample_hash(0xD2),
        account_hash: sample_hash(0xD3),
        validated: true,
        ..LedgerHeader::default()
    };
    let replacement = LedgerHeader {
        seq: 809,
        hash: sample_hash(0xE1),
        parent_hash: sample_hash(0xE2),
        tx_hash: sample_hash(0xE3),
        account_hash: sample_hash(0xE4),
        drops: 101,
        parent_close_time: 11,
        close_time: 22,
        validated: false,
        accepted: true,
        close_time_resolution: 30,
        close_flags: SLCF_NO_CONSENSUS_TIME,
    };
    let mut ledger = Ledger::from_header_hashes(original);
    let tx_state = ledger.tx_map().state();
    let state_state = ledger.state_map().state();
    let tx_root_hash = ledger.tx_map().root().get_hash();
    let state_root_hash = ledger.state_map().root().get_hash();

    ledger.set_ledger_info(replacement);

    assert_eq!(ledger.header(), replacement);
    assert!(ledger.is_immutable());
    assert_eq!(ledger.tx_map().state(), tx_state);
    assert_eq!(ledger.state_map().state(), state_state);
    assert_eq!(ledger.tx_map().root().get_hash(), tx_root_hash);
    assert_eq!(ledger.state_map().root().get_hash(), state_root_hash);
}

#[test]
fn ledger_load_immutable_with_family_fetches_roots_in_and_marks_immutable() {
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
fn ledger_load_immutable_with_family_warns_and_acquires_by_hash_only_after_failed_load() {
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
fn ledger_load_immutable_with_family_and_setup_decodes_loaded_state_entries_ctor() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x94), vec![0xAB; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0x95)], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(
                    None,
                    Some((
                        encode_native_amount_field(22, 44),
                        encode_native_amount_field(23, 55),
                        encode_native_amount_field(24, 66),
                    )),
                ),
            ),
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
fn ledger_load_immutable_with_family_and_config_seeds_rules_and_fees_from_config() {
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
                amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0x98)], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(Some((11, 22, 33)), None),
            ),
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
fn ledger_load_immutable_with_family_and_config_or_none_returns_some_for_complete_loads() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xA0), vec![0xAA; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0xA1)], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(Some((12, 23, 34)), None),
            ),
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
fn ledger_load_immutable_with_family_and_config_or_none_returns_none_for_failed_loads() {
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
fn ledger_load_finished_with_family_and_config_or_none_returns_full_ledger() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xA6), vec![0xFE; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0xA7)], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(Some((14, 25, 36)), None),
            ),
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
fn ledger_load_finished_by_hash_with_family_and_config_or_none_matches_requested_hash() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xAA), vec![0xDD; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees()], false),
            ),
            (fees_key(), fee_settings_entry_bytes(Some((9, 8, 7)), None)),
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
fn ledger_load_finished_by_hash_with_family_and_config_or_none_panics_on_hash_mismatch() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xAD), vec![0xCC; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees()], false),
            ),
            (fees_key(), fee_settings_entry_bytes(Some((5, 6, 7)), None)),
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
fn ledger_load_by_index_with_provider_and_config_or_none_returns_finished_ledger() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xB0), vec![0x11; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0xB1)], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(Some((21, 31, 41)), None),
            ),
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
fn ledger_load_by_index_with_provider_and_config_or_none_returns_none_for_missing_header() {
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
fn ledger_load_by_hash_with_provider_and_config_or_none_returns_finished_ledger() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0xB4), vec![0x22; 20]),
        0,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees()], false),
            ),
            (fees_key(), fee_settings_entry_bytes(Some((4, 5, 6)), None)),
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
fn ledger_load_by_hash_with_provider_and_config_or_none_returns_none_for_missing_header() {
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
                amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0xB8)], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(Some((13, 23, 33)), None),
            ),
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
        SharedReporter(reporter.clone()),
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
                amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0x9B)], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(Some((41, 52, 63)), None),
            ),
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

    ledger.set_rules(Rules::new([preset]));
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
                amendments_entry_bytes(&[feature_xrp_fees()], false),
            )],
            true,
            XRP_LEDGER_EARLIEST_FEES,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, true, XRP_LEDGER_EARLIEST_FEES),
    );

    let _ = ledger.finish_load_by_index_or_hash(&RecordingLedgerJournal::default());
}

#[test]
fn ledger_load_immutable_with_family_and_setup_marks_failed_setup_ctor() {
    let missing_amendments_hash = sample_hash(0x96);
    let fee_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            fees_key(),
            fee_settings_entry_bytes(Some((10, 20, 30)), None),
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
fn calculate_ledger_hash_matches_current_cpp_byte_layout() {
    let header = LedgerHeader {
        seq: 1,
        drops: 2,
        parent_hash: sample_hash(0x03),
        tx_hash: sample_hash(0x04),
        account_hash: sample_hash(0x05),
        parent_close_time: 6,
        close_time: 7,
        close_time_resolution: 8,
        close_flags: 9,
        ..LedgerHeader::default()
    };
    let expected = SHAMapHash::new(
        Uint256::from_hex("3F2077849F231F9782E9FB33A9E2F1876E9A825163DF3136AE1FEA150FC2CE77")
            .expect("expected hash should parse"),
    );

    assert_eq!(calculate_ledger_hash(&header), expected);
}

#[test]
fn ledger_from_previous_uses_close_flags_to_expand_resolution_after_non_consensus_close() {
    let previous = Ledger::new(
        LedgerHeader {
            seq: 15,
            hash: sample_hash(0x51),
            close_time: 200,
            close_time_resolution: 20,
            close_flags: SLCF_NO_CONSENSUS_TIME,
            ..LedgerHeader::default()
        },
        true,
    );

    let next = Ledger::from_previous(&previous, 999);

    assert_eq!(next.header().seq, 16);
    assert_eq!(next.header().close_time_resolution, 30);
    assert_eq!(next.header().close_time, 230);
}

#[test]
fn ledger_set_total_drops_replaces_only_the_total_xrp_field() {
    let mut ledger = Ledger::new(
        LedgerHeader {
            seq: 901,
            drops: 12,
            hash: sample_hash(0x61),
            parent_hash: sample_hash(0x62),
            ..LedgerHeader::default()
        },
        true,
    );

    ledger.set_total_drops(777);

    assert_eq!(ledger.header().drops, 777);
    assert_eq!(ledger.header().seq, 901);
    assert_eq!(ledger.header().hash, sample_hash(0x61));
    assert_eq!(ledger.header().parent_hash, sample_hash(0x62));
}

#[test]
fn ledger_assert_sensible_accepts_matching_header_and_owner_hashes() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x62), vec![0x17; 20]),
        0,
    );
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x63), vec![0x27; 20]),
        0,
    );
    let mut header = LedgerHeader {
        seq: 902,
        drops: 101,
        tx_hash: tx_root.get_hash(),
        account_hash: state_root.get_hash(),
        parent_hash: sample_hash(0x64),
        parent_close_time: 11,
        close_time: 22,
        close_time_resolution: 30,
        close_flags: 0,
        ..LedgerHeader::default()
    };
    header.hash = calculate_ledger_hash(&header);

    let mut ledger = Ledger::from_maps(
        header,
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            902,
            SyncState::Immutable,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            902,
            SyncState::Immutable,
        ),
    );

    assert!(ledger.assert_sensible());
}

#[test]
#[should_panic(expected = "ledger is not sensible")]
fn ledger_assert_sensible_panics_for_mismatched_account_hash_unreachable_path() {
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(sample_uint256(0x72), vec![0x18; 20]),
        0,
    );
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(sample_uint256(0x73), vec![0x28; 20]),
        0,
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 903,
            drops: 102,
            hash: sample_hash(0x74),
            tx_hash: tx_root.get_hash(),
            account_hash: sample_hash(0x75),
            parent_hash: sample_hash(0x76),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            true,
            903,
            SyncState::Immutable,
        ),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            true,
            903,
            SyncState::Immutable,
        ),
    );

    let _ = ledger.assert_sensible();
}

#[test]
fn ledger_apply_default_fees_matches_current_cpp_zero_fill_behavior() {
    let mut ledger = Ledger::new(
        LedgerHeader {
            seq: 1001,
            ..LedgerHeader::default()
        },
        true,
    );

    ledger.apply_default_fees(Fees {
        base: 10,
        reserve: 200_000,
        increment: 50_000,
    });

    assert_eq!(
        ledger.fees(),
        Fees {
            base: 10,
            reserve: 200_000,
            increment: 50_000,
        }
    );
}

#[test]
fn ledger_from_previous_carries_fees_and_rules_forward() {
    let preset = sample_uint256(0x81);
    let amendment = sample_uint256(0x82);
    let mut previous = Ledger::new(
        LedgerHeader {
            seq: 1002,
            hash: sample_hash(0x83),
            close_time: 100,
            close_time_resolution: 30,
            ..LedgerHeader::default()
        },
        true,
    );
    previous.set_fees(Fees {
        base: 11,
        reserve: 22,
        increment: 33,
    });
    previous.set_rules(Rules::from_ledger(
        [preset],
        sample_uint256(0x84),
        [amendment],
    ));

    let next = Ledger::from_previous(&previous, 140);

    assert_eq!(next.fees(), previous.fees());
    assert_eq!(next.rules(), previous.rules());
    assert!(next.rules().enabled(&preset));
    assert!(next.rules().enabled(&amendment));
}

#[test]
fn ledger_setup_with_entries_resets_rules_to_presets_when_amendments_object_is_missing() {
    let preset = sample_uint256(0x91);
    let amendment = sample_uint256(0x92);
    let mut ledger = Ledger::new(LedgerHeader::default(), true);
    ledger.set_rules(Rules::from_ledger(
        [preset],
        sample_uint256(0x93),
        [amendment],
    ));

    let ok = ledger.setup_with_entries(&LedgerSetupEntries::default(), &feature_xrp_fees());

    assert!(ok);
    assert!(ledger.rules().enabled(&preset));
    assert!(!ledger.rules().enabled(&amendment));
    assert_eq!(ledger.rules().digest(), None);
}

#[test]
fn ledger_setup_with_entries_preserves_prior_rules_when_amendment_lookup_hits_missing_node() {
    let amendment = sample_uint256(0xA1);
    let original_rules =
        Rules::from_ledger([feature_xrp_fees()], sample_uint256(0xA2), [amendment]);
    let mut ledger = Ledger::new(LedgerHeader::default(), true);
    ledger.set_rules(original_rules.clone());

    let ok = ledger.setup_with_entries(
        &LedgerSetupEntries {
            amendments: SetupLookup::MissingNode,
            fees: SetupLookup::MissingObject,
        },
        &feature_xrp_fees(),
    );

    assert!(!ok);
    assert_eq!(ledger.rules(), &original_rules);
}

#[test]
fn ledger_setup_with_entries_accepts_legacy_fee_fields_when_xrp_fees_is_disabled() {
    let mut ledger = Ledger::new(LedgerHeader::default(), true);
    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });

    let ok = ledger.setup_with_entries(
        &LedgerSetupEntries {
            amendments: SetupLookup::MissingObject,
            fees: SetupLookup::Present(FeeSettingsFields {
                base_fee: Some(10),
                reserve_base: Some(20),
                reserve_increment: Some(30),
                ..FeeSettingsFields::default()
            }),
        },
        &feature_xrp_fees(),
    );

    assert!(ok);
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 10,
            reserve: 20,
            increment: 30,
        }
    );
}

#[test]
fn ledger_setup_with_entries_accepts_xrp_amount_fee_fields_when_feature_is_enabled() {
    let mut ledger = Ledger::new(LedgerHeader::default(), true);
    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });
    ledger.set_rules(Rules::from_ledger(
        [],
        sample_uint256(0xB1),
        [feature_xrp_fees()],
    ));

    let ok = ledger.setup_with_entries(
        &LedgerSetupEntries {
            amendments: SetupLookup::Present(AmendmentsEntry {
                digest: sample_uint256(0xB2),
                amendments: vec![feature_xrp_fees()],
            }),
            fees: SetupLookup::Present(FeeSettingsFields {
                base_fee_drops: Some(AmountField {
                    drops: 44,
                    native: true,
                    negative: false,
                }),
                reserve_base_drops: Some(AmountField {
                    drops: 55,
                    native: true,
                    negative: false,
                }),
                reserve_increment_drops: Some(AmountField {
                    drops: 66,
                    native: true,
                    negative: false,
                }),
                ..FeeSettingsFields::default()
            }),
        },
        &feature_xrp_fees(),
    );

    assert!(ok);
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 44,
            reserve: 55,
            increment: 66,
        }
    );
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert_eq!(ledger.rules().digest(), Some(sample_uint256(0xB2)));
}

#[test]
fn ledger_setup_with_entries_rejects_mixed_old_and_new_fee_formats() {
    let mut ledger = Ledger::new(LedgerHeader::default(), true);
    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });
    ledger.set_rules(Rules::from_ledger(
        [],
        sample_uint256(0xC1),
        [feature_xrp_fees()],
    ));

    let ok = ledger.setup_with_entries(
        &LedgerSetupEntries {
            amendments: SetupLookup::Present(AmendmentsEntry {
                digest: sample_uint256(0xC2),
                amendments: vec![feature_xrp_fees()],
            }),
            fees: SetupLookup::Present(FeeSettingsFields {
                base_fee: Some(10),
                reserve_base_drops: Some(AmountField {
                    drops: 55,
                    native: true,
                    negative: false,
                }),
                ..FeeSettingsFields::default()
            }),
        },
        &feature_xrp_fees(),
    );

    assert!(!ok);
}

#[test]
fn ledger_setup_with_entries_rejects_new_fee_fields_before_xrp_fees_amendment() {
    let mut ledger = Ledger::new(LedgerHeader::default(), true);
    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });

    let ok = ledger.setup_with_entries(
        &LedgerSetupEntries {
            amendments: SetupLookup::MissingObject,
            fees: SetupLookup::Present(FeeSettingsFields {
                base_fee_drops: Some(AmountField {
                    drops: 44,
                    native: true,
                    negative: false,
                }),
                ..FeeSettingsFields::default()
            }),
        },
        &feature_xrp_fees(),
    );

    assert!(!ok);
}

#[test]
fn ledger_setup_with_entries_rejects_non_native_xrp_amount_fields() {
    let mut ledger = Ledger::new(LedgerHeader::default(), true);
    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });
    ledger.set_rules(Rules::from_ledger(
        [],
        sample_uint256(0xD1),
        [feature_xrp_fees()],
    ));

    let ok = ledger.setup_with_entries(
        &LedgerSetupEntries {
            amendments: SetupLookup::Present(AmendmentsEntry {
                digest: sample_uint256(0xD2),
                amendments: vec![feature_xrp_fees()],
            }),
            fees: SetupLookup::Present(FeeSettingsFields {
                base_fee_drops: Some(AmountField {
                    drops: 44,
                    native: false,
                    negative: false,
                }),
                ..FeeSettingsFields::default()
            }),
        },
        &feature_xrp_fees(),
    );

    assert!(!ok);
}

#[test]
fn ledger_setup_from_state_map_decodes_amendments_and_legacy_fee_fields() {
    let preset = sample_uint256(0xC8);
    let amendments = vec![feature_xrp_fees(), sample_uint256(0xC9)];
    let state_map = build_state_map_with_items(
        &[
            (amendments_key(), typed_amendments_entry_bytes(&amendments)),
            (
                fees_key(),
                typed_legacy_fee_settings_entry_bytes(10, 20, 30),
            ),
        ],
        false,
        1101,
    );
    let tx_map = SyncTree::new_with_type(SHAMapType::Transaction, false, 1101);
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 1101,
            ..LedgerHeader::default()
        },
        state_map,
        tx_map,
    );
    let expected_digest = ledger
        .state_map()
        .peek_item_with_hash(amendments_key(), &mut |_| None)
        .expect("amendments lookup should succeed")
        .expect("amendments entry should exist")
        .1;

    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });
    ledger.set_rules(Rules::new([preset]));

    let ok = ledger
        .setup_from_state_map(&feature_xrp_fees())
        .expect("state-map setup should decode");

    assert!(ok);
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 10,
            reserve: 20,
            increment: 30,
        }
    );
    assert!(ledger.rules().enabled(&preset));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&sample_uint256(0xC9)));
    assert_eq!(ledger.rules().digest(), Some(*expected_digest.as_uint256()));
}

#[test]
fn ledger_setup_with_entries_rejects_mixed_legacy_and_xrp_fee_formats() {
    let preset = sample_uint256(0xC7);
    let mut ledger = Ledger::new(
        LedgerHeader {
            seq: 1101,
            ..LedgerHeader::default()
        },
        false,
    );
    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });
    ledger.set_rules(Rules::new([preset]));

    let ok = ledger.setup_with_entries(
        &LedgerSetupEntries {
            amendments: SetupLookup::Present(AmendmentsEntry {
                digest: sample_uint256(0xC8),
                amendments: vec![feature_xrp_fees()],
            }),
            fees: SetupLookup::Present(FeeSettingsFields {
                base_fee: Some(10),
                reserve_base: Some(20),
                reserve_increment: Some(30),
                base_fee_drops: Some(AmountField {
                    drops: 44,
                    native: true,
                    negative: false,
                }),
                ..FeeSettingsFields::default()
            }),
        },
        &feature_xrp_fees(),
    );

    assert!(!ok);
    assert!(ledger.rules().enabled(&preset));
}

#[test]
fn ledger_setup_from_state_map_with_config_reseeds_presets_before_decode() {
    let preset = sample_uint256(0xCA);
    let amendment = sample_uint256(0xCB);
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees(), amendment], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(Some((10, 20, 30)), None),
            ),
        ],
        false,
        1105,
    );
    let tx_map = SyncTree::new_with_type(SHAMapType::Transaction, false, 1105);
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 1105,
            ..LedgerHeader::default()
        },
        state_map,
        tx_map,
    );
    let config = sample_ledger_config([preset, feature_xrp_fees()]);

    let ok = ledger
        .setup_from_state_map_with_config(&config)
        .expect("config-backed setup should decode");

    assert!(ok);
    assert_eq!(ledger.fees(), config.fees);
    assert!(ledger.rules().enabled(&preset));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&amendment));
}

#[test]
fn ledger_setup_from_state_map_with_config_and_family_decodes_family_backed_xrp_fee_fields() {
    let preset = sample_uint256(0xCC);
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-setup-config-family",
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
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0xCD)], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(
                    None,
                    Some((
                        encode_native_amount_field(22, 44),
                        encode_native_amount_field(23, 55),
                        encode_native_amount_field(24, 66),
                    )),
                ),
            ),
        ],
        true,
        1106,
    );
    let tx_map = SyncTree::new_with_type(SHAMapType::Transaction, false, 1106);
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 1106,
            ..LedgerHeader::default()
        },
        state_map,
        tx_map,
    );
    let config = sample_ledger_config([preset, feature_xrp_fees()]);

    let ok = ledger
        .setup_from_state_map_with_config_and_family(&config, &family)
        .expect("family-backed config setup should decode");

    assert!(ok);
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 44,
            reserve: 55,
            increment: 66,
        }
    );
    assert!(ledger.rules().enabled(&preset));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&sample_uint256(0xCD)));
}

#[test]
fn ledger_setup_from_state_map_with_family_decodes_xrp_fee_fields() {
    let reporter = Arc::new(Mutex::new(RecordingMissingNodeReporter::default()));
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-setup-family",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher::default(),
        SharedReporter(reporter),
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees()], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(
                    None,
                    Some((
                        encode_native_amount_field(22, 44),
                        encode_native_amount_field(23, 55),
                        encode_native_amount_field(24, 66),
                    )),
                ),
            ),
        ],
        true,
        1102,
    );
    let tx_map = SyncTree::new_with_type(SHAMapType::Transaction, false, 1102);
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 1102,
            ..LedgerHeader::default()
        },
        state_map,
        tx_map,
    );
    let expected_digest = ledger
        .state_map()
        .peek_item_with_hash_and_family(amendments_key(), &family)
        .expect("family-backed amendments lookup should succeed")
        .expect("amendments entry should exist")
        .1;

    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });

    let ok = ledger
        .setup_from_state_map_with_family(&feature_xrp_fees(), &family)
        .expect("family-backed state-map setup should decode");

    assert!(ok);
    assert_eq!(
        ledger.fees(),
        Fees {
            base: 44,
            reserve: 55,
            increment: 66,
        }
    );
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert_eq!(ledger.rules().digest(), Some(*expected_digest.as_uint256()));
}

#[test]
fn ledger_setup_from_state_map_with_family_returns_false_for_missing_amendment_node() {
    let missing_amendments_hash = sample_hash(0xD8);
    let fee_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(
            fees_key(),
            fee_settings_entry_bytes(Some((10, 20, 30)), None),
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
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-setup-missing-node",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher::default(),
        SharedReporter(reporter),
    );
    let state_map =
        SyncTree::from_root_with_type(root, SHAMapType::State, true, 1103, SyncState::Immutable);
    let tx_map = SyncTree::new_with_type(SHAMapType::Transaction, false, 1103);
    let original_rules = Rules::from_ledger(
        [feature_xrp_fees()],
        sample_uint256(0xD9),
        [sample_uint256(0xDA)],
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 1103,
            ..LedgerHeader::default()
        },
        state_map,
        tx_map,
    );
    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });
    ledger.set_rules(original_rules.clone());

    let ok = ledger
        .setup_from_state_map_with_family(&feature_xrp_fees(), &family)
        .expect("missing-node setup should still return a bool outcome");

    assert!(!ok);
    assert_eq!(ledger.rules(), &original_rules);
}

#[test]
fn ledger_setup_from_state_map_rejects_negative_native_xrp_fee_amounts_in_narrowed_port() {
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                amendments_entry_bytes(&[feature_xrp_fees()], false),
            ),
            (
                fees_key(),
                fee_settings_entry_bytes(
                    None,
                    Some((
                        encode_negative_native_amount_field(22, 44),
                        encode_native_amount_field(23, 55),
                        encode_native_amount_field(24, 66),
                    )),
                ),
            ),
        ],
        false,
        1104,
    );
    let tx_map = SyncTree::new_with_type(SHAMapType::Transaction, false, 1104);
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 1104,
            ..LedgerHeader::default()
        },
        state_map,
        tx_map,
    );
    ledger.apply_default_fees(Fees {
        base: 1,
        reserve: 2,
        increment: 3,
    });

    let ok = ledger
        .setup_from_state_map(&feature_xrp_fees())
        .expect("negative native amount should decode through the narrowed port");

    assert!(!ok);
}

#[test]
fn build_genesis_setup_items_uses_legacy_fee_object_without_xrp_fees_amendment() {
    let amendment = sample_uint256(0xD1);
    let config = sample_ledger_config([sample_uint256(0xD2)]);
    let mut expected_fee_bytes = Vec::new();
    expected_fee_bytes.extend_from_slice(&encode_u16_field(1, 0x0073));
    expected_fee_bytes.extend_from_slice(&encode_u32_field(2, 0)); // Flags
    expected_fee_bytes.extend_from_slice(&encode_u32_field(30, 10));
    expected_fee_bytes.extend_from_slice(&encode_u32_field(31, 20));
    expected_fee_bytes.extend_from_slice(&encode_u32_field(32, 30));
    expected_fee_bytes.extend_from_slice(&encode_u64_field(5, 10));

    let items = build_genesis_setup_items(&config, [amendment]);

    assert_eq!(items.len(), 2);
    assert_eq!(items[0].0, amendments_key());
    assert_eq!(items[0].1, encode_amendments_entry(&[amendment]));
    assert_eq!(items[1], (fees_key(), expected_fee_bytes));
}

#[test]
fn build_genesis_setup_items_uses_xrp_fee_object_when_amendment_enables_it() {
    let config = sample_ledger_config([sample_uint256(0xD3)]);

    let items = build_genesis_setup_items(&config, [feature_xrp_fees()]);

    assert_eq!(items.len(), 2);
    assert_eq!(items[0].0, amendments_key());
    assert_eq!(items[0].1, encode_amendments_entry(&[feature_xrp_fees()]));
    assert_eq!(
        items[1],
        (
            fees_key(),
            fee_settings_entry_bytes(
                None,
                Some((
                    encode_native_amount_field(22, 10),
                    encode_native_amount_field(23, 20),
                    encode_native_amount_field(24, 30),
                )),
            )
        )
    );
}

#[test]
fn build_genesis_setup_items_omits_amendments_entry_when_list_is_empty() {
    let config = sample_ledger_config([sample_uint256(0xD3)]);

    let items = build_genesis_setup_items(&config, std::iter::empty::<Uint256>());

    assert_eq!(items.len(), 1);
    assert_eq!(items[0].0, fees_key());
    assert_eq!(
        decode_constructor_fee_settings_entry(&items[0].1)
            .expect("genesis setup fees entry should decode"),
        ConstructorFeeSettingsEntry::Legacy {
            base_fee: config.fees.base,
            reference_fee_units: 10,
            reserve_base: Some(
                u32::try_from(config.fees.reserve).expect("fee reserve should fit in u32"),
            ),
            reserve_increment: Some(
                u32::try_from(config.fees.increment).expect("fee increment should fit in u32"),
            ),
        }
    );
}

#[test]
fn build_genesis_setup_items_round_trip_through_setup_from_state_map() {
    let amendment = sample_uint256(0xD4);
    let config = sample_ledger_config([sample_uint256(0xD5), feature_xrp_fees()]);
    let items = build_genesis_setup_items(&config, [feature_xrp_fees(), amendment]);
    let mut ledger = Ledger::new(
        LedgerHeader {
            seq: 1,
            ..LedgerHeader::default()
        },
        false,
    );
    *ledger.state_map_mut() = build_state_map_with_items(&items, false, 1);
    ledger.apply_default_fees(config.fees);

    let loaded = ledger
        .setup_from_state_map(&feature_xrp_fees())
        .expect("genesis setup entries should decode through current ledger setup path");

    assert!(loaded);
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    assert!(ledger.rules().enabled(&amendment));
    assert_eq!(ledger.fees(), config.fees);
}

#[test]
fn create_genesis_setup_only_matches_current_ctor_surface_except_master_account_state() {
    let config = sample_ledger_config([sample_uint256(0xD6)]);
    let ledger = Ledger::create_genesis_setup_only(false, &config, [feature_xrp_fees()])
        .expect("setup-only genesis constructor should insert singleton state entries");

    assert!(ledger.is_immutable());
    assert_eq!(ledger.header().seq, 1);
    assert_eq!(ledger.header().drops, INITIAL_XRP_DROPS);
    assert_eq!(
        ledger.header().close_time_resolution,
        LEDGER_GENESIS_TIME_RESOLUTION
    );
    assert_eq!(ledger.fees(), config.fees);
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    let (amendments, _amendments_hash) = ledger
        .state_map()
        .peek_item_with_hash(amendments_key(), &mut |_| None)
        .expect("genesis setup-only constructor should keep state map readable")
        .expect("genesis setup-only constructor should insert amendments entry");
    assert_eq!(
        decode_constructor_amendments_entry(amendments.data())
            .expect("genesis setup-only constructor should keep amendments decodable"),
        ConstructorAmendmentsEntry {
            amendments: vec![feature_xrp_fees()]
        }
    );
    let (fees, _fees_hash) = ledger
        .state_map()
        .peek_item_with_hash(fees_key(), &mut |_| None)
        .expect("genesis setup-only constructor should keep state map readable")
        .expect("genesis setup-only constructor should insert fees entry");
    assert_eq!(
        decode_constructor_fee_settings_entry(fees.data())
            .expect("genesis setup-only constructor should keep fees decodable"),
        ConstructorFeeSettingsEntry::XrpDrops {
            base_fee_drops: config.fees.base,
            reserve_base_drops: config.fees.reserve,
            reserve_increment_drops: config.fees.increment,
        }
    );
    assert!(
        ledger
            .state_map()
            .peek_item_with_hash(
                Uint256::from_hex(
                    "2B6AC232AA4C4BE41BF49D2459FA4A0347E1B543A4C92FCEE0821C0201E2E9A8"
                )
                .expect("expected genesis account-root key should parse"),
                &mut |_| None,
            )
            .expect("genesis setup-only constructor should keep state map readable")
            .is_none()
    );
}

#[test]
fn create_genesis_setup_only_omits_amendments_entry_when_none_are_supplied() {
    let config = sample_ledger_config([]);
    let ledger = Ledger::create_genesis_setup_only(false, &config, [])
        .expect("setup-only genesis constructor should insert the fees singleton only");

    assert!(ledger.is_immutable());
    assert_eq!(ledger.header().seq, 1);
    assert_eq!(ledger.header().drops, INITIAL_XRP_DROPS);
    assert_eq!(
        ledger.header().close_time_resolution,
        LEDGER_GENESIS_TIME_RESOLUTION
    );
    assert_eq!(ledger.fees(), config.fees);
    assert!(!ledger.rules().enabled(&feature_xrp_fees()));
    assert!(
        ledger
            .state_map()
            .peek_item_with_hash(amendments_key(), &mut |_| None)
            .expect("genesis setup-only constructor should keep state map readable")
            .is_none()
    );
    let (fees, _fees_hash) = ledger
        .state_map()
        .peek_item_with_hash(fees_key(), &mut |_| None)
        .expect("genesis setup-only constructor should keep state map readable")
        .expect("genesis setup-only constructor should insert fees entry");
    assert_eq!(
        decode_constructor_fee_settings_entry(fees.data())
            .expect("genesis setup-only constructor should keep fees decodable"),
        ConstructorFeeSettingsEntry::Legacy {
            base_fee: config.fees.base,
            reference_fee_units: 10,
            reserve_base: Some(
                u32::try_from(config.fees.reserve).expect("fee reserve should fit in u32"),
            ),
            reserve_increment: Some(
                u32::try_from(config.fees.increment).expect("fee increment should fit in u32"),
            ),
        }
    );
}

#[test]
fn create_genesis_setup_only_uses_legacy_fee_shape_without_xrp_fees_amendment() {
    let amendment = sample_uint256(0xDA);
    let config = sample_ledger_config([sample_uint256(0xDB)]);
    let ledger = Ledger::create_genesis_setup_only(false, &config, [amendment])
        .expect("setup-only genesis constructor should insert singleton state entries");

    let (amendments, _amendments_hash) = ledger
        .state_map()
        .peek_item_with_hash(amendments_key(), &mut |_| None)
        .expect("legacy genesis setup-only constructor should keep state map readable")
        .expect("legacy genesis setup-only constructor should insert amendments entry");
    assert_eq!(
        decode_constructor_amendments_entry(amendments.data())
            .expect("legacy genesis setup-only constructor should keep amendments decodable"),
        ConstructorAmendmentsEntry {
            amendments: vec![amendment]
        }
    );

    let (fees, _fees_hash) = ledger
        .state_map()
        .peek_item_with_hash(fees_key(), &mut |_| None)
        .expect("legacy genesis setup-only constructor should keep state map readable")
        .expect("legacy genesis setup-only constructor should insert fees entry");
    assert_eq!(
        decode_constructor_fee_settings_entry(fees.data())
            .expect("legacy genesis setup-only constructor should keep fees decodable"),
        ConstructorFeeSettingsEntry::Legacy {
            base_fee: config.fees.base,
            reference_fee_units: 10,
            reserve_base: Some(20),
            reserve_increment: Some(30),
        }
    );
}

#[test]
fn amendment_helpers_match_current_cpp_enabled_and_majority_rules() {
    let enabled_one = feature_xrp_fees();
    let enabled_two = sample_uint256(0xE1);
    let majority = sample_uint256(0xA6);
    let state_map = build_state_map_with_items(
        &[(
            amendments_key(),
            amendments_entry_bytes(&[enabled_one, enabled_two], true),
        )],
        false,
        1,
    );
    let ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 1,
            ..LedgerHeader::default()
        },
        state_map,
        SyncTree::new_with_type(SHAMapType::Transaction, false, 1),
    );

    let expected_enabled = [enabled_one, enabled_two].into_iter().collect();
    assert_eq!(get_enabled_amendments(&ledger), expected_enabled);
    assert_eq!(ledger.get_enabled_amendments(), expected_enabled);

    let expected_majorities = [(majority, NetClockTimePoint::from(999))]
        .into_iter()
        .collect();
    assert_eq!(get_majority_amendments(&ledger), expected_majorities);
    assert_eq!(ledger.get_majority_amendments(), expected_majorities);
}

#[test]
fn amendment_helpers_return_empty_when_amendments_entry_is_missing_or_empty() {
    let missing_entry = Ledger::from_maps(
        LedgerHeader {
            seq: 1,
            ..LedgerHeader::default()
        },
        build_state_map_with_items(&[], false, 1),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 1),
    );
    assert!(get_enabled_amendments(&missing_entry).is_empty());
    assert!(get_majority_amendments(&missing_entry).is_empty());

    let mut empty_amendments_payload = Vec::new();
    empty_amendments_payload.extend_from_slice(&encode_u16_field(1, 0x0066));
    empty_amendments_payload.extend_from_slice(&encode_u32_field(4, 1));
    empty_amendments_payload.extend_from_slice(&encode_u32_field(5, 2));
    empty_amendments_payload.extend_from_slice(&encode_u32_field(6, 3));
    let empty_entry = Ledger::from_maps(
        LedgerHeader {
            seq: 1,
            ..LedgerHeader::default()
        },
        build_state_map_with_items(&[(amendments_key(), empty_amendments_payload)], false, 1),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 1),
    );
    assert!(get_enabled_amendments(&empty_entry).is_empty());
    assert!(get_majority_amendments(&empty_entry).is_empty());
}

#[test]
fn flag_and_voting_ledger_helpers_match_current_cpp_interval_rules() {
    assert!(is_flag_ledger(256));
    assert!(!is_flag_ledger(255));
    assert!(is_voting_ledger(256));
    assert!(!is_voting_ledger(255));

    let flag_ledger = Ledger::new(
        LedgerHeader {
            seq: 256,
            ..LedgerHeader::default()
        },
        false,
    );
    assert!(flag_ledger.is_flag_ledger());
    assert!(!flag_ledger.is_voting_ledger());

    let voting_ledger = Ledger::new(
        LedgerHeader {
            seq: 255,
            ..LedgerHeader::default()
        },
        false,
    );
    assert!(voting_ledger.is_voting_ledger());
    assert!(!voting_ledger.is_flag_ledger());
}

#[test]
fn update_negative_unl_noops_without_entry_or_action_fields() {
    let mut missing_entry_ledger = Ledger::new(
        LedgerHeader {
            seq: 500,
            ..LedgerHeader::default()
        },
        false,
    );

    missing_entry_ledger
        .update_negative_unl()
        .expect("missing NegativeUNL entry should be a no-op");
    assert!(
        missing_entry_ledger
            .state_map()
            .peek_item_with_hash(negative_unl_keylet().key, &mut |_| None)
            .expect("missing NegativeUNL lookup should succeed")
            .is_none()
    );

    let no_action_entry = negative_unl_entry_bytes(&[(vec![0x11, 0x22], 7)], None, None);
    let mut no_action_ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 500,
            ..LedgerHeader::default()
        },
        build_state_map_with_items(&[(negative_unl_keylet().key, no_action_entry)], false, 500),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 500),
    );

    no_action_ledger
        .update_negative_unl()
        .expect("NegativeUNL entry without action fields should be a no-op");
    assert_eq!(
        decode_negative_unl_from_ledger(&no_action_ledger)
            .expect("NegativeUNL entry should still exist"),
        DecodedNegativeUnlEntry {
            disabled_validators: vec![DecodedDisabledValidator {
                public_key: vec![0x11, 0x22],
                first_ledger_sequence: 7,
            }],
            validator_to_disable: None,
            validator_to_re_enable: None,
            previous_txn_id: None,
            previous_txn_lgr_seq: None,
        }
    );
}

#[test]
fn update_negative_unl_rebuilds_array_and_clears_action_fields() {
    let validator_to_re_enable = vec![0xAA, 0xBB, 0xCC];
    let validator_to_disable = vec![0xDD, 0xEE, 0xFF];
    let preserved_validator = vec![0x44, 0x55, 0x66];
    let entry = negative_unl_entry_bytes(
        &[
            (validator_to_re_enable.clone(), 12),
            (preserved_validator.clone(), 13),
        ],
        Some(validator_to_disable.clone()),
        Some(validator_to_re_enable.clone()),
    );
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 777,
            ..LedgerHeader::default()
        },
        build_state_map_with_items(&[(negative_unl_keylet().key, entry)], false, 777),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 777),
    );

    ledger
        .update_negative_unl()
        .expect("NegativeUNL update should succeed");

    assert_eq!(
        decode_negative_unl_from_ledger(&ledger)
            .expect("NegativeUNL entry should still exist after rebuild"),
        DecodedNegativeUnlEntry {
            disabled_validators: vec![
                DecodedDisabledValidator {
                    public_key: preserved_validator,
                    first_ledger_sequence: 13,
                },
                DecodedDisabledValidator {
                    public_key: validator_to_disable,
                    first_ledger_sequence: 777,
                },
            ],
            validator_to_disable: None,
            validator_to_re_enable: None,
            previous_txn_id: None,
            previous_txn_lgr_seq: None,
        }
    );
}

#[test]
fn update_negative_unl_erases_entry_when_rebuild_becomes_empty() {
    let to_re_enable = vec![0x77, 0x88, 0x99];
    let entry = negative_unl_entry_bytes(&[(to_re_enable.clone(), 88)], None, Some(to_re_enable));
    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 888,
            ..LedgerHeader::default()
        },
        build_state_map_with_items(&[(negative_unl_keylet().key, entry)], false, 888),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 888),
    );

    ledger
        .update_negative_unl()
        .expect("NegativeUNL update should succeed");

    assert!(
        ledger
            .state_map()
            .peek_item_with_hash(negative_unl_keylet().key, &mut |_| None)
            .expect("NegativeUNL lookup should succeed")
            .is_none()
    );
}

#[test]
fn negative_unl_read_helpers_match_current_cpp_field_filtering_rules() {
    let valid_validator = genesis_public_key();
    let invalid_validator = vec![0x04; 32];
    let disable_validator = genesis_public_key();
    let re_enable_validator = genesis_public_key();
    let entry = negative_unl_entry_bytes(
        &[
            (valid_validator.to_vec(), 11),
            (invalid_validator.clone(), 12),
        ],
        Some(disable_validator.to_vec()),
        Some(re_enable_validator.to_vec()),
    );
    let ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 901,
            ..LedgerHeader::default()
        },
        build_state_map_with_items(&[(negative_unl_keylet().key, entry)], false, 901),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 901),
    );

    assert_eq!(ledger.negative_unl(), HashSet::from([valid_validator]));
    assert_eq!(ledger.validator_to_disable(), Some(disable_validator));
    assert_eq!(ledger.validator_to_re_enable(), Some(re_enable_validator));
}

#[test]
fn negative_unl_read_helpers_return_none_for_missing_or_invalid_action_fields() {
    let invalid_disable = vec![0x04; 32];
    let invalid_re_enable = vec![0x05; 32];
    let entry = negative_unl_entry_bytes(&[(genesis_public_key().to_vec(), 7)], None, None);
    let invalid_entry = negative_unl_entry_bytes(
        &[(genesis_public_key().to_vec(), 7)],
        Some(invalid_disable),
        Some(invalid_re_enable),
    );
    let empty_ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 902,
            ..LedgerHeader::default()
        },
        build_state_map_with_items(&[(negative_unl_keylet().key, entry)], false, 902),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 902),
    );
    let invalid_ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 903,
            ..LedgerHeader::default()
        },
        build_state_map_with_items(&[(negative_unl_keylet().key, invalid_entry)], false, 903),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 903),
    );

    assert!(empty_ledger.validator_to_disable().is_none());
    assert!(empty_ledger.validator_to_re_enable().is_none());
    assert!(invalid_ledger.validator_to_disable().is_none());
    assert!(invalid_ledger.validator_to_re_enable().is_none());
}

#[test]
fn build_genesis_master_account_root_item_matches_current_cpp_constants() {
    let account_id = Uint160::from_hex("B5F762798A53D543A014CAF8B297CFF8F2F937E8")
        .expect("expected genesis master account id should parse");
    let expected_key =
        Uint256::from_hex("2B6AC232AA4C4BE41BF49D2459FA4A0347E1B543A4C92FCEE0821C0201E2E9A8")
            .expect("expected genesis account-root key should parse");
    let mut expected_payload = Vec::new();
    expected_payload.extend_from_slice(&encode_u16_field(1, 0x0061));
    expected_payload.extend_from_slice(&encode_u32_field(2, 0)); // Flags=0
    expected_payload.extend_from_slice(&encode_u32_field(4, 1)); // Sequence=1
    expected_payload.extend_from_slice(&encode_native_amount_field(2, INITIAL_XRP_DROPS));
    expected_payload.extend_from_slice(&encode_account_field(1, account_id));

    let (key, payload) = build_genesis_master_account_root_item(INITIAL_XRP_DROPS);

    assert_eq!(key, expected_key);
    assert_eq!(payload, expected_payload);
}

#[test]
fn build_genesis_state_items_puts_master_account_before_singletons() {
    let amendment = sample_uint256(0xD7);
    let config = sample_ledger_config([sample_uint256(0xD8)]);

    let items =
        build_genesis_state_items(&config, [feature_xrp_fees(), amendment], INITIAL_XRP_DROPS);

    assert_eq!(items.len(), 3);
    assert_eq!(
        items[0].0,
        Uint256::from_hex("2B6AC232AA4C4BE41BF49D2459FA4A0347E1B543A4C92FCEE0821C0201E2E9A8")
            .expect("expected genesis account-root key should parse")
    );
    assert_eq!(items[1].0, amendments_key());
    assert_eq!(items[2].0, fees_key());
}

#[test]
fn create_genesis_matches_current_ctor_surface_for_ported_objects() {
    let preset = sample_uint256(0xD9);
    let config = sample_ledger_config([preset]);
    let ledger = Ledger::create_genesis(false, &config, [feature_xrp_fees()])
        .expect("genesis constructor should insert the genesis objects");

    assert!(ledger.is_immutable());
    assert_eq!(ledger.header().seq, 1);
    assert_eq!(ledger.header().drops, INITIAL_XRP_DROPS);
    assert_eq!(
        ledger.header().close_time_resolution,
        LEDGER_GENESIS_TIME_RESOLUTION
    );
    assert_eq!(ledger.fees(), config.fees);
    assert!(ledger.rules().enabled(&preset));
    assert!(ledger.rules().enabled(&feature_xrp_fees()));
    let (master_account, _master_account_hash) = ledger
        .state_map()
        .peek_item_with_hash(
            Uint256::from_hex("2B6AC232AA4C4BE41BF49D2459FA4A0347E1B543A4C92FCEE0821C0201E2E9A8")
                .expect("expected genesis account-root key should parse"),
            &mut |_| None,
        )
        .expect("genesis constructor should keep master account root readable")
        .expect("genesis constructor should insert the master account root");
    let decoded_master_account = decode_constructor_account_root_entry(master_account.data())
        .expect("genesis constructor should keep the master account root decodable");
    assert_eq!(
        decoded_master_account,
        ConstructorAccountRootEntry {
            sequence: 1,
            balance_drops: INITIAL_XRP_DROPS,
            account_id: Uint160::from_hex("B5F762798A53D543A014CAF8B297CFF8F2F937E8")
                .expect("expected genesis master account id should parse"),
        }
    );
    let (amendments, _amendments_hash) = ledger
        .state_map()
        .peek_item_with_hash(amendments_key(), &mut |_| None)
        .expect("genesis constructor should keep amendments entry readable")
        .expect("genesis constructor should insert amendments entry");
    assert_eq!(
        decode_constructor_amendments_entry(amendments.data())
            .expect("genesis constructor should keep amendments decodable"),
        ConstructorAmendmentsEntry {
            amendments: vec![feature_xrp_fees()]
        }
    );
    let (fees, _fees_hash) = ledger
        .state_map()
        .peek_item_with_hash(fees_key(), &mut |_| None)
        .expect("genesis constructor should keep fees entry readable")
        .expect("genesis constructor should insert fees entry");
    assert_eq!(
        decode_constructor_fee_settings_entry(fees.data())
            .expect("genesis constructor should keep fees decodable"),
        ConstructorFeeSettingsEntry::XrpDrops {
            base_fee_drops: config.fees.base,
            reserve_base_drops: config.fees.reserve,
            reserve_increment_drops: config.fees.increment,
        }
    );
}

#[test]
fn create_genesis_omits_amendments_entry_when_none_are_supplied() {
    let config = sample_ledger_config([]);
    let ledger = Ledger::create_genesis(false, &config, [])
        .expect("genesis constructor should insert the current state singleton set");

    assert!(ledger.is_immutable());
    assert_eq!(ledger.header().seq, 1);
    assert_eq!(ledger.header().drops, INITIAL_XRP_DROPS);
    assert_eq!(
        ledger.header().close_time_resolution,
        LEDGER_GENESIS_TIME_RESOLUTION
    );
    assert_eq!(ledger.fees(), config.fees);
    assert!(!ledger.rules().enabled(&feature_xrp_fees()));

    let (master_account, _master_account_hash) = ledger
        .state_map()
        .peek_item_with_hash(
            Uint256::from_hex("2B6AC232AA4C4BE41BF49D2459FA4A0347E1B543A4C92FCEE0821C0201E2E9A8")
                .expect("expected genesis account-root key should parse"),
            &mut |_| None,
        )
        .expect("genesis constructor should keep master account root readable")
        .expect("genesis constructor should insert the master account root");
    assert_eq!(
        decode_constructor_account_root_entry(master_account.data())
            .expect("genesis constructor should keep the master account root decodable"),
        ConstructorAccountRootEntry {
            sequence: 1,
            balance_drops: INITIAL_XRP_DROPS,
            account_id: Uint160::from_hex("B5F762798A53D543A014CAF8B297CFF8F2F937E8")
                .expect("expected genesis master account id should parse"),
        }
    );
    assert!(
        ledger
            .state_map()
            .peek_item_with_hash(amendments_key(), &mut |_| None)
            .expect("genesis constructor should keep state map readable")
            .is_none()
    );
    let (fees, _fees_hash) = ledger
        .state_map()
        .peek_item_with_hash(fees_key(), &mut |_| None)
        .expect("genesis constructor should keep fees entry readable")
        .expect("genesis constructor should insert fees entry");
    assert_eq!(
        decode_constructor_fee_settings_entry(fees.data())
            .expect("genesis constructor should keep fees decodable"),
        ConstructorFeeSettingsEntry::Legacy {
            base_fee: config.fees.base,
            reference_fee_units: 10,
            reserve_base: Some(
                u32::try_from(config.fees.reserve).expect("fee reserve should fit in u32"),
            ),
            reserve_increment: Some(
                u32::try_from(config.fees.increment).expect("fee increment should fit in u32"),
            ),
        }
    );
}

#[test]
fn update_skip_list_records_the_previous_hash_in_the_short_list() {
    let config = sample_ledger_config([]);
    let genesis = Ledger::create_genesis(false, &config, []).expect("genesis ledger should build");
    let mut next = Ledger::from_previous(&genesis, 10);

    next.update_skip_list()
        .expect("skip-list update should write the short list");

    let (short_list, _) = next
        .state_map()
        .peek_item_with_hash(skip_keylet().key, &mut |_| None)
        .expect("skip-list read should succeed")
        .expect("short skip-list entry should exist");
    let decoded =
        decode_ledger_hashes_entry(short_list.data()).expect("short skip-list entry should decode");

    assert_eq!(decoded.last_ledger_sequence, Some(genesis.header().seq));
    assert_eq!(decoded.hashes, vec![*genesis.header().hash.as_uint256()]);
    assert_eq!(
        next.hash_of_seq(next.header().seq, &RecordingLedgerJournal::default()),
        Some(next.header().hash)
    );
    assert_eq!(
        next.hash_of_seq(genesis.header().seq, &RecordingLedgerJournal::default()),
        Some(genesis.header().hash)
    );
}

#[test]
fn update_skip_list_rolls_the_short_list_and_keeps_the_long_bucket() {
    let config = sample_ledger_config([]);
    let genesis = Ledger::create_genesis(false, &config, []).expect("genesis ledger should build");
    let mut history = vec![genesis];

    for close_time in 1..=512u32 {
        let mut next = Ledger::from_previous(
            history
                .last()
                .expect("history should contain a previous ledger"),
            close_time,
        );
        next.update_skip_list()
            .expect("skip-list update should succeed across the history build");
        history.push(next);
    }

    let latest = history
        .last()
        .expect("history should contain the latest ledger");
    assert_eq!(latest.header().seq, 513);

    let (short_list, _) = latest
        .state_map()
        .peek_item_with_hash(skip_keylet().key, &mut |_| None)
        .expect("short skip-list read should succeed")
        .expect("short skip-list entry should exist");
    let short_decoded =
        decode_ledger_hashes_entry(short_list.data()).expect("short skip-list should decode");
    assert_eq!(short_decoded.last_ledger_sequence, Some(512));
    assert_eq!(short_decoded.hashes.len(), 256);
    assert_eq!(
        short_decoded
            .hashes
            .first()
            .copied()
            .expect("rolled short list should retain 256 hashes"),
        *history[256].header().hash.as_uint256()
    );
    assert_eq!(
        short_decoded
            .hashes
            .last()
            .copied()
            .expect("rolled short list should retain the parent hash"),
        *history[511].header().hash.as_uint256()
    );

    let (long_list, _) = latest
        .state_map()
        .peek_item_with_hash(skip_keylet_for_ledger(256).key, &mut |_| None)
        .expect("long skip-list read should succeed")
        .expect("long skip-list entry should exist");
    let long_decoded =
        decode_ledger_hashes_entry(long_list.data()).expect("long skip-list should decode");
    assert_eq!(long_decoded.last_ledger_sequence, Some(512));
    assert_eq!(
        long_decoded.hashes,
        vec![
            *history[255].header().hash.as_uint256(),
            *history[511].header().hash.as_uint256(),
        ]
    );

    let journal = RecordingLedgerJournal::default();
    assert_eq!(
        latest.hash_of_seq(512, &journal),
        Some(history[511].header().hash)
    );
    assert_eq!(
        latest.hash_of_seq(257, &journal),
        Some(history[256].header().hash)
    );
    assert_eq!(
        latest.hash_of_seq(256, &journal),
        Some(history[255].header().hash)
    );
    assert_eq!(latest.hash_of_seq(255, &journal), None);
    assert_eq!(latest.hash_of_seq(514, &journal), None);
}
