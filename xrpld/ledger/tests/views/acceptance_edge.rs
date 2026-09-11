use basics::base_uint::Uint256;
use basics::intrusive_pointer::make_shared_intrusive;
use basics::sha_map_hash::SHAMapHash;
use ledger::{Ledger, LedgerHeader, SLCF_NO_CONSENSUS_TIME};
use shamap::item::SHAMapItem;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

fn sample_uint256(fill: u8) -> Uint256 {
    Uint256::from_array([fill; 32])
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
