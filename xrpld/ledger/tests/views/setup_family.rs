use basics::base_uint::Uint256;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{
    AmendmentsEntry, AmountField, FeeSettingsFields, Fees, Ledger, LedgerConfig, LedgerHeader,
    LedgerSetupEntries, Rules, SetupLookup, amendments_key, fees_key,
};
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

const OBJECT_END: u8 = 0xE1;

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

fn encode_native_amount_field(field_name: u8, value: u64) -> Vec<u8> {
    let mut bytes = encode_field_id(6, field_name);
    bytes.extend_from_slice(&(value | 0x4000_0000_0000_0000).to_be_bytes());
    bytes
}

fn encode_negative_native_amount_field(field_name: u8, value: u64) -> Vec<u8> {
    let mut bytes = encode_field_id(6, field_name);
    bytes.extend_from_slice(&value.to_be_bytes());
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

#[derive(Debug, Default)]
struct RecordingFetcher {
    expected: HashMap<SHAMapHash, SharedIntrusive<SHAMapTreeNode>>,
}

impl SHAMapNodeFetcher for RecordingFetcher {
    fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        self.expected.get(&hash).cloned()
    }
}

#[derive(Debug, Default)]
struct RecordingMissingNodeReporter;

impl MissingNodeReporter for RecordingMissingNodeReporter {
    fn missing_node_acquire_by_seq(&self, _ref_num: u32, _node_hash: Uint256) {}
    fn missing_node_acquire_by_hash(&self, _ref_hash: Uint256, _ref_num: u32) {}
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
        RecordingMissingNodeReporter,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees(), sample_uint256(0xCD)]),
            ),
            (fees_key(), encode_fee_settings_entry(44, 55, 66, true)),
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
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-setup-family",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher::default(),
        RecordingMissingNodeReporter,
    );
    let state_map = build_state_map_with_items(
        &[
            (
                amendments_key(),
                encode_amendments_entry(&[feature_xrp_fees()]),
            ),
            (fees_key(), encode_fee_settings_entry(44, 55, 66, true)),
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

    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "ledger-setup-missing-node",
            8,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(0),
        RecordingFetcher::default(),
        RecordingMissingNodeReporter,
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
                encode_amendments_entry(&[feature_xrp_fees()]),
            ),
            (fees_key(), {
                let mut bytes = encode_field_id(1, 1);
                bytes.extend_from_slice(&0x0073u16.to_be_bytes());
                bytes.extend_from_slice(&encode_negative_native_amount_field(22, 44));
                bytes.extend_from_slice(&encode_native_amount_field(23, 55));
                bytes.extend_from_slice(&encode_native_amount_field(24, 66));
                bytes.push(OBJECT_END);
                bytes
            }),
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
