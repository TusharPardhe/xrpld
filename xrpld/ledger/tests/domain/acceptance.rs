use basics::base_uint::Uint256;
use basics::intrusive_pointer::make_shared_intrusive;
use basics::sha_map_hash::SHAMapHash;
use ledger::{
    Fees, Ledger, LedgerConfig, LedgerHeader, Rules, SLCF_NO_CONSENSUS_TIME, amendments_key,
    calculate_ledger_hash, fees_key,
};
use protocol::{
    FeatureSet, LedgerEntryType, STAmount, STLedgerEntry, STVector256, encode_amendments_entry,
    encode_fee_settings_entry, feature_xrp_fees, get_field_by_symbol,
};
use shamap::item::SHAMapItem;
use shamap::mutation::MutableTree;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};

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

fn typed_amendments_entry_bytes(amendments: &[Uint256]) -> Vec<u8> {
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::Amendments, amendments_key());
    entry.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), sample_uint256(0xAD));
    entry.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 905);
    entry.set_field_v256(
        get_field_by_symbol("sfAmendments"),
        STVector256::from_values(get_field_by_symbol("sfAmendments"), amendments.to_vec()),
    );
    entry.get_serializer().data().to_vec()
}

fn typed_xrp_fee_settings_entry_bytes(base: u64, reserve: u64, increment: u64) -> Vec<u8> {
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::FeeSettings, fees_key());
    entry.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), sample_uint256(0xAE));
    entry.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 906);
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

#[test]
fn ledger_set_immutable_and_setup_from_state_map_runs_setup_after_finalization() {
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                typed_amendments_entry_bytes(&[feature_xrp_fees(), sample_uint256(0x88)]),
            ),
            (fees_key(), typed_xrp_fee_settings_entry_bytes(44, 55, 66)),
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
            tx_root,
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
                encode_amendments_entry(&[feature_xrp_fees(), sample_uint256(0x8C)]),
            ),
            (fees_key(), encode_fee_settings_entry(44, 55, 66, false)),
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
            increment: 66,
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
            (fees_key(), typed_xrp_fee_settings_entry_bytes(10, 20, 30)),
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
            increment: 30,
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
        SHAMapItem::new(fees_key(), encode_fee_settings_entry(10, 20, 30, false)),
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
        close_time_resolution: 30,
        close_flags: SLCF_NO_CONSENSUS_TIME,
        ..LedgerHeader::default()
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
