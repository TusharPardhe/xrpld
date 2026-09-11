use basics::base_uint::Uint256;
use basics::intrusive_pointer::make_shared_intrusive;
use basics::sha_map_hash::SHAMapHash;
use ledger::{Ledger, LedgerHeader};
use protocol::{
    DecodedDisabledValidator, DecodedNegativeUnlEntry, STArray, STLedgerEntry, STObject,
    genesis_public_key, get_field_by_symbol, negative_unl_keylet,
};
use shamap::item::SHAMapItem;
use shamap::mutation::MutableTree;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::traversal::TraversalError;
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use std::collections::HashSet;

fn build_state_map_with_items(items: &[(Uint256, Vec<u8>)], ledger_seq: u32) -> SyncTree {
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
        false,
        ledger_seq,
        SyncState::Immutable,
    )
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
        build_state_map_with_items(&[(negative_unl_keylet().key, no_action_entry)], 500),
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
        build_state_map_with_items(&[(negative_unl_keylet().key, entry)], 777),
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
        build_state_map_with_items(&[(negative_unl_keylet().key, entry)], 888),
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
        build_state_map_with_items(&[(negative_unl_keylet().key, entry)], 901),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 901),
    );

    assert_eq!(ledger.negative_unl(), HashSet::from([valid_validator]));
    assert_eq!(ledger.validator_to_disable(), Some(disable_validator));
    assert_eq!(ledger.validator_to_re_enable(), Some(re_enable_validator));
}

#[test]
fn strict_negative_unl_read_preserves_missing_node_error() {
    let root = SHAMapTreeNode::new_inner(1);
    let branch = usize::from(negative_unl_keylet().key.data()[0] >> 4);
    let missing = SHAMapHash::new(Uint256::from_array([0xA5; 32]));
    root.set_child_hash(branch, missing);
    root.update_hash();
    let ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 904,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(root, SHAMapType::State, true, 904, SyncState::Immutable),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 904),
    );

    assert!(matches!(
        ledger.try_negative_unl(),
        Err(TraversalError::MissingNode(hash)) if hash == missing
    ));
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
        build_state_map_with_items(&[(negative_unl_keylet().key, entry)], 902),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 902),
    );
    let invalid_ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 903,
            ..LedgerHeader::default()
        },
        build_state_map_with_items(&[(negative_unl_keylet().key, invalid_entry)], 903),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 903),
    );

    assert!(empty_ledger.validator_to_disable().is_none());
    assert!(empty_ledger.validator_to_re_enable().is_none());
    assert!(invalid_ledger.validator_to_disable().is_none());
    assert!(invalid_ledger.validator_to_re_enable().is_none());
}
