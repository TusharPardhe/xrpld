use std::sync::{Arc, Mutex};
use std::time::Duration;

use app::{
    AppLedgerPersistenceRuntime, SqliteSHAMapStoreRelational, TransStatus, Transaction,
    TransactionMaster,
};
use basics::base_uint::Uint256;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use ledger::calculate_ledger_hash;
use ledger::{Ledger, LedgerHeader, pend_save_validated};
use protocol::{
    AccountID, MPTAmount, MPTIssue, STAmount, STArray, STObject, STTx, Serializer, TxMeta, TxType,
    get_field_by_symbol, make_mpt_id,
};
use quaxar_core::{DatabaseCon, LEDGER_DB_INIT, TRANSACTION_DB_INIT};
use shamap::item::SHAMapItem;
use shamap::mutation::MutableTree;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};

fn account(fill: u8) -> AccountID {
    AccountID::from_array([fill; 20])
}

fn state_leaf(fill: u8) -> SharedIntrusive<SHAMapTreeNode> {
    SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        SHAMapItem::new(Uint256::from_array([fill; 32]), vec![fill; 12]),
        0,
    )
}

fn payment_tx(sequence: u32) -> Arc<STTx> {
    Arc::new(STTx::new(TxType::PAYMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), account(0x11));
        tx.set_account_id(get_field_by_symbol("sfDestination"), account(0x22));
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(1_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
    }))
}

fn affected_node(account: AccountID, fill: u8) -> STObject {
    let mut final_fields = STObject::new(get_field_by_symbol("sfFinalFields"));
    final_fields.set_account_id(get_field_by_symbol("sfAccount"), account);

    let mut node = STObject::new(get_field_by_symbol("sfModifiedNode"));
    node.set_field_h256(
        get_field_by_symbol("sfLedgerIndex"),
        Uint256::from_array([fill; 32]),
    );
    node.set_field_u16(get_field_by_symbol("sfLedgerEntryType"), 97);
    node.set_field_object(get_field_by_symbol("sfFinalFields"), final_fields);
    node
}

fn metadata(index: u32) -> STObject {
    let mut affected_nodes = STArray::new(get_field_by_symbol("sfAffectedNodes"));
    affected_nodes.push_back(affected_node(account(0x11), 0x31));
    affected_nodes.push_back(affected_node(account(0x22), 0x32));

    let mut meta = STObject::new(get_field_by_symbol("sfTransactionMetaData"));
    meta.set_field_u8(get_field_by_symbol("sfTransactionResult"), 0);
    meta.set_field_u32(get_field_by_symbol("sfTransactionIndex"), index);
    meta.set_field_array(get_field_by_symbol("sfAffectedNodes"), affected_nodes);
    meta
}

fn tx_md_payload(tx: &STTx, meta: &STObject) -> Vec<u8> {
    let tx_bytes = tx.get_serializer().data().to_vec();
    let meta_bytes = meta.get_serializer().data().to_vec();
    let mut serializer = Serializer::new(0);
    serializer.add_vl(&tx_bytes);
    serializer.add_vl(&meta_bytes);
    serializer.data().to_vec()
}

fn immutable_ledger_with_txs(items: &[(Arc<STTx>, STObject)], seq: u32) -> Arc<Ledger> {
    let root = state_leaf(seq as u8);
    let mut tree = MutableTree::new(seq);
    for (tx, meta) in items {
        tree.add_item(
            SHAMapNodeType::TransactionMd,
            SHAMapItem::new(tx.get_transaction_id(), tx_md_payload(tx, meta)),
        )
        .expect("transaction-with-metadata item should insert");
    }

    let tx_root = tree.root();
    let mut header = LedgerHeader {
        seq,
        account_hash: root.get_hash(),
        tx_hash: tx_root.get_hash(),
        ..LedgerHeader::default()
    };
    header.hash = calculate_ledger_hash(&header);

    let mut ledger = Ledger::from_maps(
        header,
        SyncTree::from_root_with_type(root, SHAMapType::State, false, seq, SyncState::Immutable),
        SyncTree::from_root_with_type(
            tx_root,
            SHAMapType::Transaction,
            false,
            seq,
            SyncState::Immutable,
        ),
    );
    ledger.set_immutable(true);
    Arc::new(ledger)
}

fn count_rows(db: &DatabaseCon, table_name: &str) -> i64 {
    let connection = db.get_session();
    connection
        .query_row(&format!("SELECT COUNT(*) FROM {table_name}"), [], |row| {
            row.get(0)
        })
        .expect("count query should succeed")
}

#[test]
fn validated_ledger_persistence_writes_cpp_style_relational_rows_and_marks_cache() {
    let temp = tempfile::TempDir::new().expect("tempdir");
    let ledger_db = Arc::new(
        DatabaseCon::new_at_path(temp.path(), "ledger.db", &[], LEDGER_DB_INIT).expect("ledger db"),
    );
    let transaction_db = Arc::new(
        DatabaseCon::new_at_path(temp.path(), "transaction.db", &[], TRANSACTION_DB_INIT)
            .expect("transaction db"),
    );
    let relational = Arc::new(SqliteSHAMapStoreRelational::new(
        Arc::clone(&ledger_db),
        Some(Arc::clone(&transaction_db)),
        true,
        100,
        Duration::from_secs(0),
    ));

    let tx = payment_tx(7);
    let delivered_amount = STAmount::from_mpt_amount(
        get_field_by_symbol("sfDeliveredAmount"),
        MPTAmount::from_value(800),
        MPTIssue::new(make_mpt_id(7, account(0x71))),
    );
    let mut meta = metadata(3);
    meta.set_field_amount(
        get_field_by_symbol("sfDeliveredAmount"),
        delivered_amount.clone(),
    );
    let raw_txn = tx.get_serializer().data().to_vec();
    let raw_meta = meta.get_serializer().data().to_vec();
    let ledger = immutable_ledger_with_txs(&[(Arc::clone(&tx), meta)], 8123);

    let transaction_master = Arc::new(TransactionMaster::new());
    let mut cached = Arc::new(Mutex::new(Transaction::new(Arc::clone(&tx))));
    transaction_master.canonicalize(&mut cached);

    let persistence = Arc::new(AppLedgerPersistenceRuntime::new(
        Some(relational),
        None,
        Arc::clone(&transaction_master),
        1025,
        None,
    ));

    assert!(pend_save_validated(
        persistence,
        Arc::clone(&ledger),
        false,
        true
    ));

    assert_eq!(count_rows(&ledger_db, "Ledgers"), 1);
    assert_eq!(count_rows(&transaction_db, "Transactions"), 1);
    assert_eq!(count_rows(&transaction_db, "AccountTransactions"), 2);

    let connection = transaction_db.get_session();
    let saved = connection
        .query_row(
            "SELECT TransType, FromSeq, LedgerSeq, Status, RawTxn, TxnMeta FROM Transactions WHERE TransID = ?1",
            [tx.get_transaction_id().to_string()],
            |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, i64>(1)?,
                    row.get::<_, i64>(2)?,
                    row.get::<_, String>(3)?,
                    row.get::<_, Vec<u8>>(4)?,
                    row.get::<_, Vec<u8>>(5)?,
                ))
            },
        )
        .expect("saved transaction row should exist");

    assert_eq!(saved.0, "Payment");
    assert_eq!(saved.1, 7);
    assert_eq!(saved.2, 8123);
    assert_eq!(saved.3, "V");
    assert_eq!(saved.4, raw_txn);
    assert_eq!(saved.5, raw_meta);

    let reparsed = TxMeta::from_raw(tx.get_transaction_id(), 8123, &saved.5);
    assert_eq!(
        reparsed.get_delivered_amount(),
        Some(&delivered_amount),
        "Transactions.TxnMeta must retain the exact MPT sfDeliveredAmount"
    );

    let cached = transaction_master
        .fetch_from_cache(&tx.get_transaction_id())
        .expect("transaction should remain cached");
    let cached = cached
        .lock()
        .expect("transaction mutex should not be poisoned");
    assert_eq!(cached.get_status(), TransStatus::COMMITTED);
    assert_eq!(cached.get_ledger(), 8123);
}
