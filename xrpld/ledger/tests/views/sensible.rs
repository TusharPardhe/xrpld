use basics::base_uint::Uint256;
use basics::intrusive_pointer::make_shared_intrusive;
use basics::sha_map_hash::SHAMapHash;
use ledger::{Ledger, LedgerHeader, calculate_ledger_hash};
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
