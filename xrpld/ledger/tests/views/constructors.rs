use basics::base_uint::Uint256;
use basics::intrusive_pointer::make_shared_intrusive;
use basics::sha_map_hash::SHAMapHash;
use ledger::{
    Fees, Ledger, LedgerConfig, LedgerHeader, RawView, SLCF_NO_CONSENSUS_TIME, StateBatchOp,
    calculate_ledger_hash,
};
use protocol::{
    FeatureSet, Keylet, LedgerEntryType, Rules, STLedgerEntry, feature_xrp_fees,
    get_field_by_symbol,
};
use shamap::item::SHAMapItem;
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
fn ledger_from_previous_candidate_mutation_preserves_parent_threading_fields() {
    // rippled BuildLedger.cpp constructs a distinct mutable Ledger from its
    // immutable parent before ApplyStateTable threads candidate SLEs. A failed
    // candidate must therefore leave the parent transaction threading intact.
    let key = sample_uint256(0x71);
    let keylet = Keylet::new(LedgerEntryType::AccountRoot, key);
    let parent_tx_id = sample_uint256(0x72);
    let candidate_tx_id = sample_uint256(0x73);
    let mut parent_sle = STLedgerEntry::new(keylet);
    parent_sle.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), parent_tx_id);
    parent_sle.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 53);

    let mut state = shamap::mutation::MutableTree::new(1);
    state
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, parent_sle.get_serializer().data().to_vec()),
        )
        .expect("parent state insertion should succeed");
    let parent = Ledger::from_maps(
        LedgerHeader {
            seq: 53,
            hash: sample_hash(0x70),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state.root(),
            SHAMapType::State,
            false,
            53,
            SyncState::Immutable,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 53),
    );
    let mut candidate = Ledger::from_previous(&parent, 100);

    let mut candidate_sle = parent_sle.clone();
    candidate_sle.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), candidate_tx_id);
    candidate_sle.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 54);
    candidate
        .raw_apply_batch(&[(
            StateBatchOp::Update,
            key,
            candidate_sle.get_serializer().data().to_vec(),
        )])
        .expect("candidate update should succeed");

    let parent_after = parent
        .read(keylet)
        .expect("parent lookup should succeed")
        .expect("parent SLE should remain present");
    assert_eq!(
        parent_after.get_field_h256(get_field_by_symbol("sfPreviousTxnID")),
        parent_tx_id
    );
    assert_eq!(
        parent_after.get_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq")),
        53
    );
    let candidate_after = candidate
        .read(keylet)
        .expect("candidate lookup should succeed")
        .expect("candidate SLE should remain present");
    assert_eq!(
        candidate_after.get_field_h256(get_field_by_symbol("sfPreviousTxnID")),
        candidate_tx_id
    );
    assert_eq!(
        candidate_after.get_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq")),
        54
    );
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
fn ledger_from_previous_uses_close_flags_to_round_resolution_field() {
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
fn ledger_set_total_drops_updates_account_state_field() {
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
