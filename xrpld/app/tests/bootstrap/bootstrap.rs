use app::{
    AppBootstrapOptions, SHAMapStoreOperatingMode, build_bootstrap_root, build_bootstrap_runtime,
    load_basic_config_file, parse_bootstrap_args,
};
use basics::{base_uint::Uint256, intrusive_pointer::make_shared_intrusive, str_hex::str_hex};
use ledger::{Ledger, LedgerHeader, calculate_ledger_hash};
use nodestore::{DummyScheduler, Manager, ManagerImp, NodeObjectType, NullJournal, Scheduler};
use protocol::{
    AccountID, KeyType, LedgerEntryType, MPTAmount, MPTIssue, STAmount, STArray, STLedgerEntry,
    STObject, STTx, SecretKey, TxType, account_keylet, calc_account_id, derive_public_key,
    get_field_by_symbol, make_mpt_id,
};
use quaxar_core::{DatabaseCon, LEDGER_DB_INIT, TRANSACTION_DB_INIT};
use shamap::{
    item::SHAMapItem,
    mutation::MutableTree,
    sync::{SHAMapType, SyncState, SyncTree},
    tree_node::{SHAMapNodeType, SHAMapTreeNode},
};
use std::fs;
use std::path::PathBuf;
use std::sync::Arc;
use tempfile::TempDir;
use xrpl_core::StartUpType;

fn count_rows(db: &DatabaseCon, table: &str) -> i64 {
    let connection = db.get_session();
    connection
        .query_row(&format!("SELECT COUNT(*) FROM {table}"), [], |row| {
            row.get(0)
        })
        .expect("count query")
}

fn raw_account_id(account: AccountID) -> basics::base_uint::Uint160 {
    basics::base_uint::Uint160::from_slice(account.data())
        .expect("account width should match Uint160")
}

fn account(fill: u8) -> AccountID {
    AccountID::from_array([fill; 20])
}

fn payment_tx(sequence: u32, account_fill: u8, destination_fill: u8) -> Arc<STTx> {
    Arc::new(STTx::new(TxType::PAYMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), account(account_fill));
        tx.set_account_id(
            get_field_by_symbol("sfDestination"),
            account(destination_fill),
        );
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

fn signed_payment_tx(
    sequence: u32,
    secret_fill: u8,
    destination: AccountID,
) -> (Arc<STTx>, AccountID) {
    let secret = SecretKey::from_bytes([secret_fill; 32]);
    let public = derive_public_key(KeyType::Secp256k1, &secret).expect("public key");
    let source = calc_account_id(public.as_bytes());
    let mut tx = STTx::new(TxType::PAYMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), source);
        tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(1_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    });
    tx.sign(&public, &secret, None)
        .expect("payment signature should succeed");
    (Arc::new(tx), source)
}

fn metadata(index: u32, fill: u8) -> STObject {
    let mut final_fields = STObject::new(get_field_by_symbol("sfFinalFields"));
    final_fields.set_account_id(get_field_by_symbol("sfAccount"), account(fill));

    let mut node = STObject::new(get_field_by_symbol("sfModifiedNode"));
    node.set_field_h256(
        get_field_by_symbol("sfLedgerIndex"),
        Uint256::from_array([fill; 32]),
    );
    node.set_field_u16(get_field_by_symbol("sfLedgerEntryType"), 97);
    node.set_field_object(get_field_by_symbol("sfFinalFields"), final_fields);

    let mut affected_nodes = STArray::new(get_field_by_symbol("sfAffectedNodes"));
    affected_nodes.push_back(node);

    let mut meta = STObject::new(get_field_by_symbol("sfTransactionMetaData"));
    meta.set_field_u8(get_field_by_symbol("sfTransactionResult"), 0);
    meta.set_field_u32(get_field_by_symbol("sfTransactionIndex"), index);
    meta.set_field_array(get_field_by_symbol("sfAffectedNodes"), affected_nodes);
    meta
}

fn tx_md_payload(tx: &STTx, meta: &STObject) -> Vec<u8> {
    let tx_bytes = tx.get_serializer().data().to_vec();
    let meta_bytes = meta.get_serializer().data().to_vec();
    let mut serializer = protocol::Serializer::new(0);
    serializer.add_vl(&tx_bytes);
    serializer.add_vl(&meta_bytes);
    serializer.data().to_vec()
}

fn persisted_bootstrap_account_root_for(account: AccountID, sequence: u32) -> SHAMapItem {
    let key = account_keylet(raw_account_id(account)).key;
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::AccountRoot, key);
    entry.set_account_id(get_field_by_symbol("sfAccount"), account);
    entry.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(1_000_000_000, false),
    );
    entry.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
    entry.set_field_u32(get_field_by_symbol("sfOwnerCount"), 0);
    entry.set_field_u32(get_field_by_symbol("sfFlags"), 0);
    entry.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), Uint256::zero());
    entry.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 0);
    SHAMapItem::new(key, entry.get_serializer().data().to_vec())
}

fn persisted_bootstrap_account_root(fill: u8) -> SHAMapItem {
    let account = account(fill);
    let key = account_keylet(raw_account_id(account)).key;
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::AccountRoot, key);
    entry.set_account_id(get_field_by_symbol("sfAccount"), account);
    entry.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(1_000_000_000 + u64::from(fill), false),
    );
    entry.set_field_u32(get_field_by_symbol("sfSequence"), u32::from(fill));
    SHAMapItem::new(key, entry.get_serializer().data().to_vec())
}

fn persisted_bootstrap_ledger(seq: u32) -> Arc<Ledger> {
    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        persisted_bootstrap_account_root(0x10 + seq as u8),
        0,
    );
    let tx_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::TransactionNm,
        SHAMapItem::new(
            Uint256::from_array([0x40 + seq as u8; 32]),
            vec![seq as u8; 16],
        ),
        0,
    );

    let mut header = LedgerHeader {
        seq,
        account_hash: state_root.get_hash(),
        tx_hash: tx_root.get_hash(),
        close_time: 500 + seq,
        parent_close_time: 499 + seq,
        close_time_resolution: ledger::LEDGER_DEFAULT_TIME_RESOLUTION,
        ..LedgerHeader::default()
    };
    header.hash = calculate_ledger_hash(&header);

    let mut ledger = Ledger::from_maps(
        header,
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            false,
            seq,
            SyncState::Immutable,
        ),
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

fn persisted_bootstrap_state_only_ledger(seq: u32) -> Arc<Ledger> {
    persisted_bootstrap_state_only_ledger_with_accounts(
        seq,
        &[(account(0x10 + seq as u8), u32::from(0x10 + seq as u8))],
    )
}

fn persisted_bootstrap_state_only_ledger_with_accounts(
    seq: u32,
    accounts: &[(AccountID, u32)],
) -> Arc<Ledger> {
    let mut state_tree = MutableTree::new(seq);
    for (account, account_sequence) in accounts {
        state_tree
            .add_item(
                SHAMapNodeType::AccountState,
                persisted_bootstrap_account_root_for(*account, *account_sequence),
            )
            .expect("account-state item should insert");
    }
    let state_root = state_tree.root();
    let mut header = LedgerHeader {
        seq,
        account_hash: state_root.get_hash(),
        close_time: 500 + seq,
        parent_close_time: 499 + seq,
        close_time_resolution: ledger::LEDGER_DEFAULT_TIME_RESOLUTION,
        ..LedgerHeader::default()
    };
    header.hash = calculate_ledger_hash(&header);

    let mut ledger = Ledger::from_maps(
        header,
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            false,
            seq,
            SyncState::Immutable,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, false, seq),
    );
    ledger.set_immutable(true);
    Arc::new(ledger)
}

fn persisted_bootstrap_replay_ledger(
    seq: u32,
    parent_hash: Uint256,
    items: &[(Arc<STTx>, STObject)],
) -> Arc<Ledger> {
    let mut tx_tree = MutableTree::new(seq);
    for (tx, meta) in items {
        tx_tree
            .add_item(
                SHAMapNodeType::TransactionMd,
                SHAMapItem::new(tx.get_transaction_id(), tx_md_payload(tx, meta)),
            )
            .expect("transaction-with-metadata item should insert");
    }

    let state_root = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        persisted_bootstrap_account_root(0x20 + seq as u8),
        0,
    );
    let tx_root = tx_tree.root();
    let mut header = LedgerHeader {
        seq,
        parent_hash: basics::sha_map_hash::SHAMapHash::new(parent_hash),
        account_hash: state_root.get_hash(),
        tx_hash: tx_root.get_hash(),
        close_time: 800 + seq,
        parent_close_time: 799 + seq,
        close_time_resolution: ledger::LEDGER_DEFAULT_TIME_RESOLUTION,
        ..LedgerHeader::default()
    };
    header.hash = calculate_ledger_hash(&header);

    let mut ledger = Ledger::from_maps(
        header,
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            false,
            seq,
            SyncState::Immutable,
        ),
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

fn persist_tree_subtree(
    database: &dyn nodestore::Database,
    node: basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>,
    object_type: NodeObjectType,
    ledger_seq: u32,
) {
    if node.get_hash().is_zero() {
        return;
    }
    let _ = database.store(
        object_type,
        node.serialize_with_prefix()
            .expect("tree node should serialize"),
        *node.get_hash().as_uint256(),
        ledger_seq,
    );

    if !node.is_inner() {
        return;
    }

    for branch in 0..16 {
        let Some(child) = node.get_child(branch) else {
            continue;
        };
        persist_tree_subtree(database, child, object_type, ledger_seq);
    }
}

fn persisted_bootstrap_incomplete_state_only_ledger(seq: u32) -> Arc<Ledger> {
    let state_leaf = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        persisted_bootstrap_account_root(0x10 + seq as u8),
        0,
    );
    let state_root = SHAMapTreeNode::new_inner(0);
    state_root.set_child_hash(3, state_leaf.get_hash());
    state_root.update_hash();

    let mut header = LedgerHeader {
        seq,
        account_hash: state_root.get_hash(),
        close_time: 500 + seq,
        parent_close_time: 499 + seq,
        close_time_resolution: ledger::LEDGER_DEFAULT_TIME_RESOLUTION,
        ..LedgerHeader::default()
    };
    header.hash = calculate_ledger_hash(&header);

    let mut ledger = Ledger::from_maps(
        header,
        SyncTree::from_root_with_type(
            state_root,
            SHAMapType::State,
            false,
            seq,
            SyncState::Immutable,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, false, seq),
    );
    ledger.set_immutable(true);
    Arc::new(ledger)
}

fn persist_bootstrap_storage(
    dir: &TempDir,
    ledgers: &[Arc<Ledger>],
    node_type: &str,
) -> (PathBuf, PathBuf, PathBuf) {
    persist_bootstrap_storage_with_missing_state_children(dir, ledgers, node_type, None)
}

fn persist_bootstrap_storage_with_missing_state_children(
    dir: &TempDir,
    ledgers: &[Arc<Ledger>],
    node_type: &str,
    missing_state_children_for: Option<u32>,
) -> (PathBuf, PathBuf, PathBuf) {
    let database_path = dir.path().join("sql");
    let node_db_path = dir.path().join("node-db");
    fs::create_dir_all(&database_path).expect("sql dir");
    fs::create_dir_all(&node_db_path).expect("node dir");

    let ledger_db = DatabaseCon::new_at_path(&database_path, "ledger.db", &[], LEDGER_DB_INIT)
        .expect("ledger db");
    let _transaction_db =
        DatabaseCon::new_at_path(&database_path, "transaction.db", &[], TRANSACTION_DB_INIT)
            .expect("transaction db");

    let manager = ManagerImp::new();
    let mut node_db = basics::basic_config::Section::new("node_db");
    node_db.set("type", node_type);
    node_db.set("path", node_db_path.to_string_lossy());
    let database = manager
        .make_database(
            8,
            Arc::new(DummyScheduler) as Arc<dyn Scheduler>,
            1,
            &node_db,
            Arc::new(NullJournal),
        )
        .expect("node store");

    let mut persisted_roots = Vec::new();
    for ledger in ledgers {
        let state_root = ledger.state_map().root();
        if missing_state_children_for == Some(ledger.header().seq) {
            // Persist only the parent root. This is the production failure
            // shape: the SQL header and root are present, but walk_ledger
            // discovers that a reachable account-state node is absent.
            let _ = database.store(
                NodeObjectType::AccountNode,
                state_root
                    .serialize_with_prefix()
                    .expect("state root should serialize"),
                *state_root.get_hash().as_uint256(),
                ledger.header().seq,
            );
        } else {
            persist_tree_subtree(
                database.as_ref(),
                state_root.clone(),
                NodeObjectType::AccountNode,
                ledger.header().seq,
            );
        }

        let tx_root = ledger.tx_map().root();
        persist_tree_subtree(
            database.as_ref(),
            tx_root.clone(),
            NodeObjectType::TransactionNode,
            ledger.header().seq,
        );
        persisted_roots.push((
            ledger.header().seq,
            *state_root.get_hash().as_uint256(),
            *tx_root.get_hash().as_uint256(),
        ));
    }
    database.sync();
    database.stop();
    drop(database);
    let reopened = manager
        .make_database(
            8,
            Arc::new(DummyScheduler) as Arc<dyn Scheduler>,
            1,
            &node_db,
            Arc::new(NullJournal),
        )
        .expect("reopened node store");
    for (seq, state_hash, tx_hash) in &persisted_roots {
        assert!(
            reopened
                .fetch_node_object(state_hash, *seq, nodestore::FetchType::Synchronous, false)
                .is_some(),
            "state root should be readable after reopen"
        );
        if !tx_hash.is_zero() {
            assert!(
                reopened
                    .fetch_node_object(tx_hash, *seq, nodestore::FetchType::Synchronous, false)
                    .is_some(),
                "tx root should be readable after reopen"
            );
        }
    }
    reopened.stop();
    drop(reopened);

    let connection = ledger_db.get_session();
    for ledger in ledgers {
        connection
            .execute(
                "INSERT INTO Ledgers (LedgerHash, LedgerSeq, PrevHash, TotalCoins, ClosingTime, PrevClosingTime, CloseTimeRes, CloseFlags, AccountSetHash, TransSetHash) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10)",
                rusqlite::params![
                    ledger.header().hash.as_uint256().to_string(),
                    i64::from(ledger.header().seq),
                    ledger.header().parent_hash.as_uint256().to_string(),
                    i64::try_from(ledger.header().drops).expect("drops should fit"),
                    i64::from(ledger.header().close_time),
                    i64::from(ledger.header().parent_close_time),
                    i64::from(ledger.header().close_time_resolution),
                    i64::from(ledger.header().close_flags),
                    ledger.header().account_hash.as_uint256().to_string(),
                    ledger.header().tx_hash.as_uint256().to_string(),
                ],
            )
            .expect("insert ledger row");
    }

    (database_path, node_db_path, dir.path().join("quaxar.cfg"))
}

#[test]
fn app_bootstrap_defaults_to_the_quaxar_config_filename() {
    let options = parse_bootstrap_args(["quaxar-app".to_owned()]).expect("defaults");
    assert_eq!(options.config_path, PathBuf::from("quaxar.cfg"));
}

#[test]
fn app_bootstrap_loads_config_and_assembles_the_app_owned_runtime_shell() {
    let dir = TempDir::new().expect("tempdir");
    let config_path = dir.path().join("quaxar.cfg");
    let database_path = dir.path().join("sql");
    let node_db_path = dir.path().join("node-db");
    fs::write(
        &config_path,
        format!(
            r#"
# bootstrap config
[ledger_history]
128

[workers]
4

[io_workers]
2

[path_search_old]
6

[path_search]
7

[path_search_fast]
5

[database_path]
{}

[server]
port_rpc
port_peer

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http,ws

[port_peer]
ip = 0.0.0.0
port = 51235
protocol = peer
limit = 64

[network_id]
21338

[cluster_nodes]
n94a1u4jAz288pZLtw6yFWVbi89YamiC6JBXPVUj5zmExe5fTVg9 alpha

[node_db]
type = RocksDB
path = {}
online_delete = 256
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config should parse");
    assert_eq!(config.legacy("ledger_history").expect("legacy"), "128");
    assert_eq!(
        config.legacy("database_path").expect("legacy"),
        database_path.to_string_lossy()
    );
    assert_eq!(
        config.section("port_rpc").get::<u16>("port").expect("port"),
        Some(5005)
    );

    let bootstrap = build_bootstrap_runtime(
        &config,
        &AppBootstrapOptions {
            config_path: config_path.clone(),
            standalone: false,
            start_valid: true,
            elb_support: true,
            io_threads: 1,
            job_queue_threads: 1,
            debug: false,
            silent: false,
            verbose: false,
            quorum: None,
            start_type: StartUpType::Fresh,
            start_ledger: None,
            trap_tx_hash: None,
            force_ledger_present_range: None,
            vacuum: false,
            import: false,
            rpc_ip: None,
            rpc_port: None,
            unittest: None,
            unittest_arg: None,
            unittest_log: false,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("bootstrap should build");

    assert_eq!(bootstrap.report.config_path, config_path);
    assert_eq!(bootstrap.report.io_threads, 2);
    assert_eq!(bootstrap.report.job_queue_threads, 4);
    assert_eq!(bootstrap.report.ledger_history, 128);
    assert_eq!(bootstrap.report.path_search_old, 6);
    assert_eq!(bootstrap.report.path_search, 7);
    assert_eq!(bootstrap.report.path_search_fast, 5);
    assert_eq!(bootstrap.report.path_search_max, 3);
    assert!(bootstrap.report.has_overlay_runtime);
    assert_eq!(bootstrap.report.overlay_network_id, Some(21_338));
    assert_eq!(bootstrap.report.cluster_node_count, 1);
    assert!(bootstrap.report.has_node_family);
    assert!(bootstrap.report.has_server_ports_setup);
    assert!(bootstrap.report.has_shamap_store_service);
    assert_eq!(
        bootstrap.report.fd_required,
        bootstrap.runtime.root().fd_required()
    );
    assert_eq!(
        bootstrap.runtime.root().network_ops_operating_mode_string(),
        "full"
    );
    let closed = bootstrap
        .runtime
        .root()
        .closed_ledger()
        .expect("Fresh startup should install an immutable closed LCL");
    let validated = bootstrap
        .runtime
        .root()
        .validated_ledger()
        .expect("Fresh --valid startup should mark the initial LCL validated");
    let published = bootstrap
        .runtime
        .root()
        .published_ledger()
        .expect("Fresh --valid startup should publish the initial LCL");
    assert_eq!(validated.header().hash, closed.header().hash);
    assert_eq!(published.header().hash, closed.header().hash);
    assert!(bootstrap.runtime.root().overlay_runtime().is_some());
    assert!(bootstrap.runtime.root().server_ports_setup().is_some());
    assert!(bootstrap.runtime.root().node_family().is_some());
    assert!(bootstrap.runtime.root().shamap_store_service().is_some());
    assert!(bootstrap.runtime.root().elb_support_enabled());
    assert_eq!(bootstrap.runtime.root().path_search_old(), 6);
    assert_eq!(bootstrap.runtime.root().path_search(), 7);
    assert_eq!(bootstrap.runtime.root().path_search_fast(), 5);
    assert_eq!(bootstrap.runtime.root().path_search_max(), 3);

    let ledger_db = DatabaseCon::new_at_path(&database_path, "ledger.db", &[], LEDGER_DB_INIT)
        .expect("ledger db");
    let transaction_db =
        DatabaseCon::new_at_path(&database_path, "transaction.db", &[], TRANSACTION_DB_INIT)
            .expect("transaction db");
    // `--valid` explicitly promotes the initial next LCL through
    // setFullLedger, so one validated ledger is persisted before runtime
    // startup. Ordinary Fresh startup remains unvalidated and unchanged.
    assert_eq!(count_rows(&ledger_db, "Ledgers"), 1);
    assert!(count_rows(&transaction_db, "Transactions") >= 0);

    let rt = tokio::runtime::Runtime::new().unwrap();
    rt.block_on(async {
        bootstrap.runtime.start().expect("runtime should start");
    });
    bootstrap.runtime.signal_stop("test");
    bootstrap.runtime.shutdown();
}

#[test]
fn app_bootstrap_root_reports_app_owned_composition_before_main_binds_server_runtime() {
    let dir = TempDir::new().expect("tempdir");
    let config_path = dir.path().join("quaxar.cfg");
    let database_path = dir.path().join("sql");
    let node_db_path = dir.path().join("node-db");
    fs::write(
        &config_path,
        format!(
            r#"
[ledger_history]
128

[workers]
4

[io_workers]
2

[database_path]
{}

[server]
port_rpc
port_peer

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http,ws

[port_peer]
ip = 0.0.0.0
port = 51235
protocol = peer
limit = 64

[node_db]
type = Memory
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config should parse");
    let bootstrap = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path: config_path.clone(),
            standalone: false,
            start_valid: true,
            elb_support: true,
            io_threads: 1,
            job_queue_threads: 1,
            start_type: StartUpType::Fresh,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("bootstrap root should build");

    assert_eq!(bootstrap.report.config_path, config_path);
    assert!(bootstrap.report.has_overlay_runtime);
    assert!(bootstrap.report.has_resolver_runtime);
    assert!(bootstrap.report.has_ledger_runtime);
    assert!(bootstrap.report.has_ledger_master_runtime);
    assert!(bootstrap.report.has_network_ops_runtime);
    assert!(bootstrap.report.has_network_ops_validation_runtime);
    assert!(bootstrap.report.has_consensus_runtime);
    assert!(bootstrap.report.has_validator_site_runtime);
    assert!(bootstrap.report.has_perf_log_runtime);
    assert!(bootstrap.report.has_node_store);
    assert_eq!(bootstrap.report.node_store_kind.as_deref(), Some("single"));
    assert!(bootstrap.report.has_server_ports_setup);
    assert!(!bootstrap.report.has_server_runtime);
    assert_eq!(
        bootstrap.report.server_configured_ports,
        vec!["port_rpc".to_owned(), "port_peer".to_owned()]
    );
    assert!(bootstrap.report.deferred_protocols.is_empty());
    assert!(bootstrap.root.runtime_bindings().server.is_none());
    assert!(bootstrap.root.server_ports_setup().is_some());
    assert!(bootstrap.root.consensus_runtime().is_some());
    assert!(bootstrap.root.ledger_master_runtime().is_some());
    assert!(bootstrap.root.network_ops_runtime().is_some());
    assert!(bootstrap.root.network_ops_validation_runtime().is_some());
}

#[test]
fn app_bootstrap_online_delete_uses_production_rotation_runtime() {
    let dir = TempDir::new().expect("tempdir");
    let config_path = dir.path().join("quaxar.cfg");
    let database_path = dir.path().join("sql");
    let node_db_path = dir.path().join("node-db");
    fs::write(
        &config_path,
        format!(
            r#"
[ledger_history]
8

[database_path]
{}

[node_db]
type = RocksDB
path = {}
online_delete = 8
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let bootstrap = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path,
            standalone: true,
            start_type: StartUpType::Fresh,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("online-delete bootstrap");
    let service = bootstrap
        .root
        .shamap_store_service()
        .expect("online-delete service");
    let component = service.component();
    assert!(
        bootstrap
            .root
            .set_shamap_store_operating_mode(SHAMapStoreOperatingMode::Full)
    );

    let close_time = bootstrap.root.current_close_time_seconds();
    service.on_ledger_closed(Arc::new(Ledger::from_ledger_seq_and_close_time(
        100, close_time, false,
    )));
    let initialized = component
        .process_queued_ledger()
        .expect("initial worker step")
        .expect("initial queued ledger");
    assert!(!initialized.rotated);
    assert_eq!(component.get_last_rotated(), 100);

    service.on_ledger_closed(Arc::new(Ledger::from_ledger_seq_and_close_time(
        108, close_time, false,
    )));
    let rotated = component
        .process_queued_ledger()
        .expect("rotation worker step")
        .expect("rotation queued ledger");
    assert!(rotated.rotated);
    let saved = component.saved_state();
    assert_eq!(saved.last_rotated, 108);
    assert!(!saved.writable_db.is_empty());
    assert!(!saved.archive_db.is_empty());
    assert_ne!(saved.writable_db, saved.archive_db);
}

#[test]
fn app_bootstrap_loads_latest_local_ledger_from_sqlite_and_nodestore() {
    let dir = TempDir::new().expect("tempdir");
    let ledger = persisted_bootstrap_ledger(7);
    let (database_path, node_db_path, config_path) =
        persist_bootstrap_storage(&dir, &[Arc::clone(&ledger)], "RocksDB");

    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = RocksDB
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let bootstrap = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path: config_path.clone(),
            start_type: StartUpType::Load,
            start_ledger: Some("latest".to_owned()),
            start_valid: true,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("storage-backed bootstrap");

    assert_eq!(bootstrap.root.closed_ledger_seq(), Some(7));
    assert_eq!(bootstrap.root.validated_ledger_seq(), Some(7));
    assert_eq!(bootstrap.root.published_ledger_seq(), Some(7));
    assert_eq!(bootstrap.root.live_current_ledger_index(), Some(8));
}

#[test]
fn app_bootstrap_loads_local_ledger_by_sequence_from_sqlite_and_nodestore() {
    let dir = TempDir::new().expect("tempdir");
    let ledger = persisted_bootstrap_ledger(9);
    let (database_path, node_db_path, config_path) =
        persist_bootstrap_storage(&dir, &[Arc::clone(&ledger)], "RocksDB");

    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = RocksDB
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let bootstrap = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path: config_path.clone(),
            start_type: StartUpType::Load,
            start_ledger: Some("9".to_owned()),
            start_valid: true,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("storage-backed bootstrap");

    assert_eq!(bootstrap.root.closed_ledger_seq(), Some(9));
    assert_eq!(bootstrap.root.validated_ledger_seq(), Some(9));
    assert_eq!(bootstrap.root.published_ledger_seq(), Some(9));
    assert_eq!(bootstrap.root.live_current_ledger_index(), Some(10));
}

#[test]
fn app_bootstrap_loads_local_ledger_by_hash_from_sqlite_and_nodestore() {
    let dir = TempDir::new().expect("tempdir");
    let ledger = persisted_bootstrap_ledger(11);
    let ledger_hash = ledger.header().hash.as_uint256().to_string();
    let (database_path, node_db_path, config_path) =
        persist_bootstrap_storage(&dir, &[Arc::clone(&ledger)], "RocksDB");

    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = RocksDB
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let bootstrap = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path: config_path.clone(),
            start_type: StartUpType::Load,
            start_ledger: Some(ledger_hash),
            start_valid: true,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("storage-backed bootstrap");

    assert_eq!(bootstrap.root.closed_ledger_seq(), Some(11));
    assert_eq!(bootstrap.root.validated_ledger_seq(), Some(11));
    assert_eq!(bootstrap.root.published_ledger_seq(), Some(11));
    assert_eq!(bootstrap.root.live_current_ledger_index(), Some(12));
}

#[test]
fn app_bootstrap_loads_replay_parent_and_injects_replay_transactions() {
    let dir = TempDir::new().expect("tempdir");
    let destination = account(0x21);
    let (replay_tx, source) = signed_payment_tx(1, 0x11, destination);
    let parent =
        persisted_bootstrap_state_only_ledger_with_accounts(20, &[(source, 1), (destination, 1)]);
    assert!(
        parent
            .read(account_keylet(raw_account_id(source)))
            .expect("fixture source account read")
            .is_some(),
        "strict replay fixture must contain the transaction source account"
    );
    let delivered_amount = STAmount::from_mpt_amount(
        get_field_by_symbol("sfDeliveredAmount"),
        MPTAmount::from_value(800),
        MPTIssue::new(make_mpt_id(7, account(0x71))),
    );
    let mut replay_meta = metadata(2, 0x92);
    replay_meta.set_field_amount(
        get_field_by_symbol("sfDeliveredAmount"),
        delivered_amount.clone(),
    );
    let replay = persisted_bootstrap_replay_ledger(
        21,
        *parent.header().hash.as_uint256(),
        &[(Arc::clone(&replay_tx), replay_meta)],
    );
    let replay_snapshot = replay.tx_snapshot().expect("replay transaction metadata");
    assert_eq!(replay_snapshot.len(), 1);
    assert_eq!(
        replay_snapshot[0].0.get_transaction_id(),
        replay_tx.get_transaction_id()
    );
    assert_eq!(
        replay_snapshot[0].1.get_delivered_amount(),
        Some(&delivered_amount),
        "serialized replay metadata must decode the exact MPT sfDeliveredAmount"
    );
    let (database_path, node_db_path, config_path) =
        persist_bootstrap_storage(&dir, &[Arc::clone(&parent), Arc::clone(&replay)], "RocksDB");

    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = RocksDB
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let bootstrap = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path: config_path.clone(),
            start_type: StartUpType::Replay,
            start_ledger: Some(replay.header().hash.as_uint256().to_string()),
            trap_tx_hash: Some(replay_tx.get_transaction_id()),
            start_valid: true,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("replay bootstrap");

    assert_eq!(bootstrap.root.closed_ledger_seq(), Some(20));
    assert_eq!(bootstrap.root.validated_ledger_seq(), Some(20));
    assert_eq!(bootstrap.root.published_ledger_seq(), Some(20));
    assert_eq!(bootstrap.root.live_current_ledger_index(), Some(21));
    assert_eq!(
        bootstrap.root.open_ledger().current().tx_ids(),
        vec![replay_tx.get_transaction_id()]
    );
}

#[test]
fn app_bootstrap_replay_raw_inserts_historical_transactions_before_later_replay() {
    // ../rippled/src/xrpld/app/main/Application.cpp::
    // ApplicationImp::loadOldLedger calls OpenView::rawTxInsert for replay
    // data before the later cumulative replay build applies it.
    let dir = TempDir::new().expect("tempdir");
    let parent = persisted_bootstrap_state_only_ledger(20);
    let rejected = payment_tx(1, 0x11, 0x21);
    let replay = persisted_bootstrap_replay_ledger(
        21,
        *parent.header().hash.as_uint256(),
        &[(Arc::clone(&rejected), metadata(0, 0x92))],
    );
    let (database_path, node_db_path, config_path) =
        persist_bootstrap_storage(&dir, &[Arc::clone(&parent), Arc::clone(&replay)], "RocksDB");

    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = RocksDB
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let error = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path,
            start_type: StartUpType::Replay,
            start_ledger: Some(replay.header().hash.as_uint256().to_string()),
            start_valid: true,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("raw replay transaction must reach the open-ledger shell");

    assert_eq!(
        error.root.open_ledger().current().tx_ids(),
        vec![rejected.get_transaction_id()]
    );
}

#[test]
fn app_bootstrap_replay_raw_inserts_future_sequence_for_cumulative_build() {
    // ../rippled/src/xrpld/app/main/Application.cpp::
    // ApplicationImp::loadOldLedger performs rawTxInsert instead of applying
    // immutable-parent preclaim to each historical transaction.
    let dir = TempDir::new().expect("tempdir");
    let destination = account(0x21);
    let (rejected, source) = signed_payment_tx(2, 0x11, destination);
    let parent =
        persisted_bootstrap_state_only_ledger_with_accounts(20, &[(source, 1), (destination, 1)]);
    let replay = persisted_bootstrap_replay_ledger(
        21,
        *parent.header().hash.as_uint256(),
        &[(Arc::clone(&rejected), metadata(0, 0x92))],
    );
    let (database_path, node_db_path, config_path) =
        persist_bootstrap_storage(&dir, &[Arc::clone(&parent), Arc::clone(&replay)], "RocksDB");

    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = RocksDB
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let error = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path,
            start_type: StartUpType::Replay,
            start_ledger: Some(replay.header().hash.as_uint256().to_string()),
            start_valid: true,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("raw replay transaction must not be rejected by immutable-parent preclaim");

    assert_eq!(
        error.root.open_ledger().current().tx_ids(),
        vec![rejected.get_transaction_id()]
    );
}

#[test]
fn app_bootstrap_replay_raw_inserts_stale_sequence_for_cumulative_build() {
    // ../rippled/src/xrpld/app/main/Application.cpp::
    // ApplicationImp::loadOldLedger restores the ordered transaction map with
    // rawTxInsert and does not run applySteps.cpp::preclaim at startup.
    let dir = TempDir::new().expect("tempdir");
    let destination = account(0x31);
    let (stale, source) = signed_payment_tx(2, 0x12, destination);
    let parent =
        persisted_bootstrap_state_only_ledger_with_accounts(20, &[(source, 1), (destination, 1)]);
    let replay = persisted_bootstrap_replay_ledger(
        21,
        *parent.header().hash.as_uint256(),
        &[(Arc::clone(&stale), metadata(0, 0x93))],
    );
    let (database_path, node_db_path, config_path) =
        persist_bootstrap_storage(&dir, &[Arc::clone(&parent), Arc::clone(&replay)], "RocksDB");

    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = RocksDB
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let error = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path,
            start_type: StartUpType::Replay,
            start_ledger: Some(replay.header().hash.as_uint256().to_string()),
            start_valid: true,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("raw replay transaction must not be rejected by immutable-parent preclaim");

    assert_eq!(
        error.root.open_ledger().current().tx_ids(),
        vec![stale.get_transaction_id()]
    );
}

#[test]
fn app_bootstrap_defers_replay_until_the_exact_incomplete_parent_is_acquired() {
    let dir = TempDir::new().expect("tempdir");
    let parent = persisted_bootstrap_incomplete_state_only_ledger(20);
    let replay = persisted_bootstrap_replay_ledger(21, *parent.header().hash.as_uint256(), &[]);
    let (database_path, node_db_path, config_path) =
        persist_bootstrap_storage_with_missing_state_children(
            &dir,
            &[Arc::clone(&parent), Arc::clone(&replay)],
            "RocksDB",
            Some(parent.header().seq),
        );

    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = RocksDB
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let bootstrap = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path,
            start_type: StartUpType::Replay,
            start_ledger: Some(replay.header().hash.as_uint256().to_string()),
            ..AppBootstrapOptions::default()
        },
    )
    .expect("incomplete replay parent should be deferred for inbound history");

    assert!(bootstrap.report.replay_startup_pending);
    assert_eq!(bootstrap.root.closed_ledger_seq(), None);
    assert_eq!(
        bootstrap.root.pending_replay_startup(),
        Some(app::PendingReplayStartup {
            parent_hash: *parent.header().hash.as_uint256(),
            parent_seq: parent.header().seq,
            start_ledger: Some(replay.header().hash.as_uint256().to_string()),
            trap_tx_hash: None,
        })
    );
}

#[test]
fn app_bootstrap_loads_ledger_file_into_live_state() {
    let dir = TempDir::new().expect("tempdir");
    let config_path = dir.path().join("quaxar.cfg");
    let ledger_path = dir.path().join("ledger.json");
    let database_path = dir.path().join("sql");
    let node_db_path = dir.path().join("node-db");

    let account = account(0x51);
    let account_key = account_keylet(raw_account_id(account)).key;
    let mut account_root =
        STLedgerEntry::from_type_and_key(LedgerEntryType::AccountRoot, account_key);
    account_root.set_account_id(get_field_by_symbol("sfAccount"), account);
    account_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(9_000_000, false),
    );
    account_root.set_field_u32(get_field_by_symbol("sfSequence"), 7);
    account_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 0);
    account_root.set_field_u32(get_field_by_symbol("sfFlags"), 0);
    account_root.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), Uint256::zero());
    account_root.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 0);
    let account_state = serde_json::json!({
        "index": account_key.to_string(),
        "blob": str_hex(account_root.get_serializer().data()),
    });

    fs::write(
        &ledger_path,
        serde_json::to_vec_pretty(&serde_json::json!({
            "result": {
                "ledger": {
                    "ledger_index": 44,
                    "close_time": 777,
                    "close_time_resolution": 30,
                    "close_time_estimated": false,
                    "total_coins": "1000000000",
                    "accountState": [account_state]
                }
            }
        }))
        .expect("ledger json"),
    )
    .expect("ledger file");

    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = Memory
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let bootstrap = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path: config_path.clone(),
            start_type: StartUpType::LoadFile,
            start_ledger: Some(ledger_path.to_string_lossy().into_owned()),
            start_valid: true,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("ledger-file bootstrap");

    assert_eq!(bootstrap.root.closed_ledger_seq(), Some(44));
    assert_eq!(bootstrap.root.validated_ledger_seq(), Some(44));
    assert_eq!(bootstrap.root.published_ledger_seq(), Some(44));
    assert_eq!(bootstrap.root.live_current_ledger_index(), Some(45));
}

#[test]
fn app_bootstrap_parses_comments_and_legacy_sections_like_the_config_shell() {
    let dir = TempDir::new().expect("tempdir");
    let config_path = dir.path().join("quaxar.cfg");
    fs::write(
        &config_path,
        r#"
# comment before any section
[database_path]
/var/lib/quaxar

[server]
port_rpc # comment on a value line

[port_rpc]
ip = 0.0.0.0
port = 5005
protocol = http
"#,
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config should parse");
    assert_eq!(
        config.legacy("database_path").expect("legacy"),
        "/var/lib/quaxar"
    );
    assert_eq!(config.section("server").values(), &["port_rpc"]);
}

#[test]
fn app_bootstrap_applies_path_search_max_defaults_and_explicit_override() {
    let dir = TempDir::new().expect("tempdir");
    let validator_default_path = dir.path().join("validator-default.cfg");
    fs::write(
        &validator_default_path,
        r#"
[validation_seed]
shUwVw52ofnCUX5m7kPTKzJdr4HEH

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http,ws
"#,
    )
    .expect("validator default config file");

    let validator_default_config =
        load_basic_config_file(&validator_default_path).expect("validator default config");
    let validator_default_bootstrap = build_bootstrap_runtime(
        &validator_default_config,
        &AppBootstrapOptions {
            config_path: validator_default_path.clone(),
            standalone: false,
            start_valid: false,
            elb_support: false,
            io_threads: 1,
            job_queue_threads: 1,
            debug: false,
            silent: false,
            verbose: false,
            quorum: None,
            start_type: StartUpType::Fresh,
            start_ledger: None,
            trap_tx_hash: None,
            force_ledger_present_range: None,
            vacuum: false,
            import: false,
            rpc_ip: None,
            rpc_port: None,
            unittest: None,
            unittest_arg: None,
            unittest_log: false,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("validator default bootstrap should build");
    assert_eq!(
        validator_default_bootstrap.runtime.root().path_search_max(),
        0
    );
    assert_eq!(
        validator_default_bootstrap.runtime.root().path_search_old(),
        2
    );
    assert_eq!(validator_default_bootstrap.runtime.root().path_search(), 2);
    assert_eq!(
        validator_default_bootstrap
            .runtime
            .root()
            .path_search_fast(),
        2
    );
    assert!(
        validator_default_bootstrap
            .runtime
            .root()
            .validated_ledger()
            .is_none()
    );
    assert!(
        validator_default_bootstrap
            .runtime
            .root()
            .published_ledger()
            .is_none()
    );
    validator_default_bootstrap.runtime.shutdown();

    let validator_override_path = dir.path().join("validator-override.cfg");
    fs::write(
        &validator_override_path,
        r#"
[validation_seed]
shUwVw52ofnCUX5m7kPTKzJdr4HEH

[path_search_max]
9

[path_search_old]
4

[path_search]
8

[path_search_fast]
3

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5006
protocol = http,ws
"#,
    )
    .expect("validator override config file");

    let validator_override_config =
        load_basic_config_file(&validator_override_path).expect("validator override config");
    let validator_override_bootstrap = build_bootstrap_runtime(
        &validator_override_config,
        &AppBootstrapOptions {
            config_path: validator_override_path,
            standalone: false,
            start_valid: false,
            elb_support: false,
            io_threads: 1,
            job_queue_threads: 1,
            debug: false,
            silent: false,
            verbose: false,
            quorum: None,
            start_type: StartUpType::Fresh,
            start_ledger: None,
            trap_tx_hash: None,
            force_ledger_present_range: None,
            vacuum: false,
            import: false,
            rpc_ip: None,
            rpc_port: None,
            unittest: None,
            unittest_arg: None,
            unittest_log: false,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("validator override bootstrap should build");
    assert_eq!(
        validator_override_bootstrap
            .runtime
            .root()
            .path_search_max(),
        9
    );
    assert_eq!(
        validator_override_bootstrap
            .runtime
            .root()
            .path_search_old(),
        4
    );
    assert_eq!(validator_override_bootstrap.runtime.root().path_search(), 8);
    assert_eq!(
        validator_override_bootstrap
            .runtime
            .root()
            .path_search_fast(),
        3
    );
    validator_override_bootstrap.runtime.shutdown();
}

#[test]
fn app_bootstrap_network_start_keeps_seeded_genesis_unvalidated() {
    let dir = TempDir::new().expect("tempdir");
    let config_path = dir.path().join("quaxar.cfg");
    let database_path = dir.path().join("sql");
    let node_db_path = dir.path().join("node-db");
    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc
port_peer

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http,ws

[port_peer]
ip = 0.0.0.0
port = 51235
protocol = peer
limit = 64

[node_db]
type = Memory
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config should parse");
    let bootstrap = build_bootstrap_runtime(
        &config,
        &AppBootstrapOptions {
            config_path,
            standalone: false,
            start_valid: false,
            elb_support: false,
            io_threads: 1,
            job_queue_threads: 1,
            start_type: StartUpType::Network,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("network bootstrap should build");

    assert!(bootstrap.runtime.root().need_network_ledger());
    assert_eq!(bootstrap.runtime.root().closed_ledger_seq(), Some(2));
    assert_eq!(bootstrap.runtime.root().published_ledger_seq(), None);
    assert_eq!(bootstrap.runtime.root().validated_ledger_seq(), None);
    assert_eq!(
        bootstrap.runtime.root().network_ops_operating_mode_string(),
        "connected"
    );

    bootstrap.runtime.shutdown();
}

#[test]
fn app_bootstrap_fresh_start_keeps_seeded_genesis_unvalidated() {
    // When the node is started without --start or --net (default Fresh startup
    // type), the genesis ledger must NOT be pre-validated.  This matches C++
    // behaviour: `startGenesisLedger()` only calls `storeLedger()` and
    // `switchLCL()` — it never calls `setValidLedger()` for network nodes.
    // Pre-validating genesis caused `validated_ledger.seq=1` to be set
    // immediately, which triggered premature `tracking` state promotion and
    // blocked real ledger resolution from the network.
    let dir = TempDir::new().expect("tempdir");
    let config_path = dir.path().join("quaxar.cfg");
    let database_path = dir.path().join("sql");
    let node_db_path = dir.path().join("node-db");
    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc
port_peer

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http,ws

[port_peer]
ip = 0.0.0.0
port = 51235
protocol = peer
limit = 64

[node_db]
type = Memory
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config should parse");
    let bootstrap = build_bootstrap_runtime(
        &config,
        &AppBootstrapOptions {
            config_path,
            standalone: false,
            start_valid: false,
            elb_support: false,
            io_threads: 1,
            job_queue_threads: 1,
            // Fresh is the default when no --start/--net flag is given.
            start_type: StartUpType::Fresh,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("fresh bootstrap should build");

    // Genesis plus its immutable successor are stored; the successor is the
    // closed LCL but must not be published/validated on a network startup.
    assert_eq!(bootstrap.runtime.root().closed_ledger_seq(), Some(2));
    assert_eq!(bootstrap.runtime.root().published_ledger_seq(), None);
    assert_eq!(
        bootstrap.runtime.root().validated_ledger_seq(),
        None,
        "genesis ledger must not be pre-validated on a network node (Fresh startup)"
    );
    // Operating mode should be connected, not tracking/full.
    assert_eq!(
        bootstrap.runtime.root().network_ops_operating_mode_string(),
        "connected"
    );

    bootstrap.runtime.shutdown();
}

#[test]
fn app_bootstrap_fast_load_falls_back_to_genesis_when_durable_load_fails() {
    let dir = TempDir::new().expect("tempdir");
    let config_path = dir.path().join("quaxar.cfg");
    let database_path = dir.path().join("sql");
    let node_db_path = dir.path().join("node");
    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = Memory
path = {}
fast_load = 1

[features]
MultiSign
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let bootstrap = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path,
            start_type: StartUpType::Normal,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("fast_load fallback should seed genesis successor");

    assert_eq!(bootstrap.root.closed_ledger_seq(), Some(2));
    assert_eq!(bootstrap.root.validated_ledger_seq(), None);
    assert_eq!(bootstrap.root.published_ledger_seq(), None);

    let closed = bootstrap.root.closed_ledger().expect("fallback LCL");
    assert!(closed.header().account_hash.is_non_zero());
    assert!(
        closed
            .read(protocol::Keylet::new(
                LedgerEntryType::AccountRoot,
                ledger::genesis_master_account_key(),
            ))
            .expect("genesis master AccountRoot lookup")
            .is_some(),
        "fast_load fallback must preserve the genesis master account",
    );
    assert!(
        closed
            .read(protocol::fee_settings_keylet())
            .expect("genesis FeeSettings lookup")
            .is_some(),
        "fast_load fallback must preserve genesis fee settings",
    );
    assert!(
        closed.rules().enabled(&protocol::feature_id("MultiSign")),
        "configured feature rules remain active after fallback",
    );
    assert!(
        closed.get_enabled_amendments().is_empty(),
        "Load-mode fallback matches rippled and does not inject Fresh-only genesis amendments",
    );
    assert!(
        !bootstrap.root.need_network_ledger(),
        "fast_load fallback preserves Load-mode need-network-ledger semantics",
    );
}

#[test]
fn app_bootstrap_normal_starts_genesis_next_lcl_even_with_durable_history() {
    let dir = TempDir::new().expect("tempdir");
    let parent = persisted_bootstrap_state_only_ledger(20);
    let latest = persisted_bootstrap_replay_ledger(21, *parent.header().hash.as_uint256(), &[]);
    let (database_path, node_db_path, config_path) =
        persist_bootstrap_storage(&dir, &[parent, latest], "RocksDB");

    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = RocksDB
path = {}
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let bootstrap = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path,
            start_type: StartUpType::Normal,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("Normal startup should seed rippled-style genesis successor");

    assert_eq!(bootstrap.root.closed_ledger_seq(), Some(2));
    assert_eq!(bootstrap.root.validated_ledger_seq(), None);
    assert_eq!(bootstrap.root.published_ledger_seq(), None);
    assert_eq!(
        bootstrap.root.open_ledger().current().parent_hash,
        *bootstrap
            .root
            .closed_ledger()
            .expect("next LCL")
            .header()
            .hash
            .as_uint256()
    );
}

#[test]
fn app_bootstrap_load_restores_latest_and_configured_history() {
    let dir = TempDir::new().expect("tempdir");
    let parent = persisted_bootstrap_state_only_ledger(20);
    let latest = persisted_bootstrap_replay_ledger(21, *parent.header().hash.as_uint256(), &[]);
    let (database_path, node_db_path, config_path) =
        persist_bootstrap_storage(&dir, &[Arc::clone(&parent), Arc::clone(&latest)], "RocksDB");

    fs::write(
        &config_path,
        format!(
            r#"
[database_path]
{}

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http

[node_db]
type = RocksDB
path = {}

[ledger_history]
2
"#,
            database_path.display(),
            node_db_path.display(),
        ),
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config");
    let bootstrap = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path,
            start_type: StartUpType::Load,
            ..AppBootstrapOptions::default()
        },
    )
    .expect("Load startup should restore durable storage");

    assert_eq!(bootstrap.root.closed_ledger_seq(), Some(21));
    assert_eq!(bootstrap.root.validated_ledger_seq(), Some(21));
    assert_eq!(bootstrap.root.published_ledger_seq(), Some(21));
    let master = bootstrap
        .root
        .ledger_master_runtime()
        .expect("ledger master runtime")
        .ledger_master();
    assert!(master.have_ledger(21));
    // Explicit Load registers the selected durable LCL; older configured
    // history is hydrated lazily through provider/NuDB recovery.
    assert_eq!(master.complete_ledgers().to_string(), "21");
}

#[test]
fn app_bootstrap_rejects_present_but_malformed_validation_seed_configuration() {
    let dir = TempDir::new().expect("tempdir");
    let config_path = dir.path().join("quaxar.cfg");
    fs::write(
        &config_path,
        r#"
[validation_seed]
first-seed
second-seed

[server]
port_rpc

[port_rpc]
ip = 127.0.0.1
port = 5005
protocol = http
"#,
    )
    .expect("config file");

    let config = load_basic_config_file(&config_path).expect("config should parse");
    let error = build_bootstrap_root(
        &config,
        &AppBootstrapOptions {
            config_path,
            ..AppBootstrapOptions::default()
        },
    )
    .expect_err("multi-line validation seed must not be silently ignored");
    assert!(error.contains("[validation_seed]"));
}
