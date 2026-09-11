use basics::base_uint::Uint256;
use basics::intrusive_pointer::make_shared_intrusive;
use ledger::{Ledger, LedgerHeader, ReadView};
use shamap::item::SHAMapItem;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};

fn sample_uint256(fill: u8) -> Uint256 {
    Uint256::from_array([fill; 32])
}

#[test]
fn ledger_tx_exists_reports_exact_membership() {
    let tx_key = sample_uint256(0x41);
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(tx_key, vec![0xAB; 20]),
        0,
    );
    let ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 900,
            ..LedgerHeader::default()
        },
        SyncTree::new_with_type(SHAMapType::State, false, 900),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            false,
            900,
            SyncState::Immutable,
        ),
    );

    assert!(ledger.tx_exists(tx_key));
    assert!(!ledger.tx_exists(sample_uint256(0x42)));
}

#[test]
fn ledger_tx_exists_resolves_backed_transaction_branches() {
    let tx_key = sample_uint256(0x41);
    let leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(tx_key, vec![0xAB; 20]),
        0,
    );
    let root = SHAMapTreeNode::new_inner(0);
    root.set_child_hash(4, leaf.get_hash());
    root.update_hash_deep();

    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 902,
            ..LedgerHeader::default()
        },
        SyncTree::new_with_type(SHAMapType::State, true, 902),
        SyncTree::from_root_with_type(
            root,
            SHAMapType::Transaction,
            true,
            902,
            SyncState::Immutable,
        ),
    );
    let expected_hash = leaf.get_hash();
    ledger.set_node_fetcher(std::sync::Arc::new(move |hash| {
        (hash == expected_hash).then_some(leaf.clone())
    }));

    assert!(
        ledger
            .try_tx_exists(tx_key)
            .expect("backed branch should resolve"),
        "candidate admission must see transactions retained in backed parent tx maps"
    );
    assert!(
        ledger.tx_exists(tx_key),
        "best-effort callers retain the legacy boolean result after a successful lookup"
    );
}

#[test]
fn ledger_tx_exists_does_not_need_fetch_for_missing_child_paths() {
    let root = SHAMapTreeNode::new_inner(1);
    root.set_child_hash(
        0,
        ledger::calculate_ledger_hash(&LedgerHeader {
            seq: 901,
            ..LedgerHeader::default()
        }),
    );
    root.update_hash_deep();

    let ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 901,
            ..LedgerHeader::default()
        },
        SyncTree::new_with_type(SHAMapType::State, true, 901),
        SyncTree::from_root_with_type(
            root,
            SHAMapType::Transaction,
            true,
            901,
            SyncState::Immutable,
        ),
    );

    let missing_key = sample_uint256(0x00);
    assert!(
        ledger.try_tx_exists(missing_key).is_err(),
        "consensus admission must distinguish an unreadable backed branch from a missing transaction"
    );
    assert!(
        ReadView::tx_exists(&ledger, missing_key).is_err(),
        "the fallible ReadView seam must preserve transaction-map traversal failure"
    );
    assert!(
        !ledger.tx_exists(missing_key),
        "the legacy best-effort helper still maps traversal failure to false"
    );
    assert!(ledger.tx_map().root().get_child(0).is_none());
}
