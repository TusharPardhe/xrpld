use super::{
    AcceptLedgerPendingRuntime, AcceptLedgerPendingTransaction, AppOpenLedgerTxQApplyRuntime,
    ApplicationRoot, INVALID_BATCH_BASE_FEE, NodeFamilyRuntime, PersistentSubmitSandbox,
    TypedPreclaimRoute, advertised_ledger_range, apply_submit_transactor_shell,
    apply_submit_transactor_shell_with_flags,
    apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim,
    apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim_and_network_id,
    apply_submit_transactor_shell_with_preclaim_and_delivered_amount, batch_base_fee,
    calculate_default_sttx_base_fee, calculate_sttx_base_fee, canonical_sttx_consequences,
    consensus_status_event, loan_set_counterparty_preflight_ter,
    preferred_lcl_matches_local_or_parent, queue_apply_preclaim_ter,
    record_applied_open_transactions, transaction_preflight_ter,
    transaction_preflight_ter_with_flags, transaction_preflight_ter_with_network_id,
    typed_preclaim_route, typed_preclaim_ter,
};
use crate::ledger::ledger_master_runtime::AppLedgerMasterRuntime;
use crate::network::network_ops_runtime::AppNetworkOpsApplyHeldOutcome;
use crate::runtime::main_runtime::{GrpcRuntime, ManagedComponent};
use crate::shamap::shamap_store_service::SHAMapStoreService;
use crate::state::accept_ledger_pending_apply::AcceptLedgerPendingApplyRuntime;
use crate::state::transactor_dispatcher::{apply_dispatch_route, handle_real_dispatch};
use crate::tx_queue::transaction::Transaction;
use crate::{
    AppOpenLedgerView, AppQueueApplyTxSource, AppTxQ, NetworkOpsConsensusMode,
    NetworkOpsOperatingMode, NetworkOpsProcessSetOwnerSync, NetworkOpsTransactionSetOutcome,
    SHAMapStore, SHAMapStoreCloseTimeProvider, SHAMapStoreComponent, SHAMapStoreComponentRuntime,
    SHAMapStoreHealthRuntime, SHAMapStoreOperatingMode, SHAMapStoreRuntime, SharedAppTxQ,
    SharedSHAMapStoreHealthState,
};
use basics::base_uint::{Uint160, Uint256};
use basics::sha_map_hash::SHAMapHash;
use ledger::{
    ApplyView, Fees, FlowSandbox, LEDGER_DEFAULT_TIME_RESOLUTION, Ledger, LedgerHeader, OpenView,
    RawView, ReadView, Sandbox, TxsRawView, calculate_ledger_hash, encode_fee_settings_entry,
};
use protocol::{
    AccountID, BatchTransactionFlags, INNER_BATCH_TRANSACTION_FLAG, KeyType, LedgerEntryType,
    Rules, STAmount, STArray, STLedgerEntry, STObject, STTx, SecretKey, SeqProxy, StBase, Ter,
    TxType, account_keylet, calc_account_id, derive_public_key, fee_settings_keylet,
    get_field_by_symbol, negative_unl_keylet, ticket_keylet_from_seq_proxy,
};
use shamap::item::SHAMapItem;
use shamap::mutation::MutableTree;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::traversal::TraversalError;
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use std::collections::{BTreeMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use tx::ApplyResult;
use tx::{
    ApplyFlags, FeeQueueEntry, FeeQueueKey, MaybeTx, MaybeTxCore, PreflightResult,
    QueueAcceptOwnerState, QueueAdvanceCandidate, QueueApplyExecutionRuntime,
    QueueApplyHoldPreflightTxSource, QueueApplyObservedAccountLookup,
    QueueApplyObservedTicketLookup, QueueApplyObservedTxSource, QueueApplyObservedViewSource,
    QueueApplyPreclaimViewSource, QueueApplyViewAdjustment, QueueFeeMetricsSnapshot, QueueViews,
    TxConsequences, TxDetails, TxQAccount, TxQSetup,
};

#[derive(Default)]
struct RecordingNodeFamily {
    resets: AtomicUsize,
    sweeps: AtomicUsize,
    seq_calls: Mutex<Vec<(u32, [u8; 32])>>,
    hash_calls: Mutex<Vec<([u8; 32], u32)>>,
}

impl NodeFamilyRuntime for RecordingNodeFamily {
    fn sweep(&self) {
        self.sweeps.fetch_add(1, Ordering::Relaxed);
    }

    fn reset(&self) {
        self.resets.fetch_add(1, Ordering::Relaxed);
    }

    fn fetch_cached_node(
        &self,
        _hash: basics::sha_map_hash::SHAMapHash,
        _ledger_seq: u32,
    ) -> Option<basics::intrusive_pointer::SharedIntrusive<shamap::tree_node::SHAMapTreeNode>> {
        None
    }

    fn missing_node_acquire_by_seq(&self, seq: u32, hash: basics::base_uint::Uint256) {
        self.seq_calls
            .lock()
            .expect("seq calls mutex must not be poisoned")
            .push((seq, *hash.data()));
    }

    fn missing_node_acquire_by_hash(&self, hash: basics::base_uint::Uint256, seq: u32) {
        self.hash_calls
            .lock()
            .expect("hash calls mutex must not be poisoned")
            .push((*hash.data(), seq));
    }

    fn visit_state_map_hashes(
        &self,
        _ledger: &Ledger,
        _visit: &mut dyn FnMut(Uint256) -> bool,
    ) -> Result<(), TraversalError> {
        Ok(())
    }

    fn visit_state_map_nodes(
        &self,
        _ledger: &Ledger,
        _visit: &mut dyn FnMut(
            &basics::memory::intrusive_pointer::SharedIntrusive<shamap::tree_node::SHAMapTreeNode>,
        ) -> bool,
    ) -> Result<(), TraversalError> {
        Ok(())
    }
}

#[derive(Default)]
struct RecordingComponent {
    stops: AtomicUsize,
}

impl ManagedComponent for RecordingComponent {
    fn start(&self) -> Result<(), String> {
        Ok(())
    }

    fn stop(&self) {
        self.stops.fetch_add(1, Ordering::Relaxed);
    }
}

#[derive(Default)]
struct FixedCloseTimeProvider;

impl SHAMapStoreCloseTimeProvider for FixedCloseTimeProvider {
    fn current_close_time(&self) -> u32 {
        120
    }
}

#[derive(Default)]
struct ServiceRuntime;

impl SHAMapStoreRuntime for ServiceRuntime {
    fn start_background_work(&mut self) {}

    fn stop_background_work(&mut self) {}

    fn minimum_sql_seq(&self) -> Option<u32> {
        None
    }
}

impl SHAMapStoreHealthRuntime for ServiceRuntime {
    fn is_stopping(&self) -> bool {
        false
    }

    fn operating_mode(&self) -> SHAMapStoreOperatingMode {
        SHAMapStoreOperatingMode::Full
    }

    fn validated_ledger_age(&self) -> std::time::Duration {
        std::time::Duration::from_secs(1)
    }
}

impl SHAMapStoreComponentRuntime for ServiceRuntime {}

fn account(hex: &str) -> AccountID {
    AccountID::from_hex(hex).expect("account hex should parse")
}

fn raw_account_id(account: AccountID) -> Uint160 {
    Uint160::from_slice(account.data()).expect("account width should match Uint160")
}

fn decode_hex_fixture(value: &str) -> Vec<u8> {
    value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let nibble = |byte: u8| match byte {
                b'0'..=b'9' => byte - b'0',
                b'a'..=b'f' => byte - b'a' + 10,
                b'A'..=b'F' => byte - b'A' + 10,
                _ => panic!("invalid hexadecimal fixture"),
            };
            (nibble(pair[0]) << 4) | nibble(pair[1])
        })
        .collect()
}

#[test]
fn testnet_20176955_transfer_rate_issuer_redemption_matches_rippled_metadata() {
    let source = protocol::parse_base58_account_id("rLtfNbqW9en22CC6CSR5m9B3aqGiPL2WXT")
        .expect("source account");
    let issuer = protocol::parse_base58_account_id("rs7gSDfyhi3JUvgTTCc9ZibuqW8FRQckqa")
        .expect("issuer account");
    let currency = protocol::currency_from_string("BST");
    let source_keylet = account_keylet(raw_account_id(source));
    let issuer_keylet = account_keylet(raw_account_id(issuer));
    let line_keylet = protocol::line(source, issuer, currency);
    assert_eq!(
        line_keylet.key,
        Uint256::from_hex("B3373AF6C010FAE7811DEA0607B549944A74453DE64FA7CCFD390FECC1ACEE8E")
            .expect("canonical line key")
    );

    let mut source_root = STLedgerEntry::new(source_keylet);
    source_root.set_account_id(get_field_by_symbol("sfAccount"), source);
    source_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(101_419_976, false),
    );
    source_root.set_field_u32(get_field_by_symbol("sfFlags"), 0);
    source_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 1);
    source_root.set_field_u32(get_field_by_symbol("sfSequence"), 20_176_919);
    source_root.set_field_h256(
        get_field_by_symbol("sfPreviousTxnID"),
        Uint256::from_hex("0094F2FE19FB023EE0FFE210946E247B3E81585B2B859D3FCE658D4EB05217FE")
            .expect("prior source transaction"),
    );
    source_root.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 20_176_923);

    let first_destination = protocol::parse_base58_account_id("rsUMxq3xUCRWJHmfFCqPwzE2yLb4JAWhAP")
        .expect("first destination");
    let first_destination_keylet = account_keylet(raw_account_id(first_destination));
    let mut first_destination_root = STLedgerEntry::new(first_destination_keylet);
    first_destination_root.set_account_id(get_field_by_symbol("sfAccount"), first_destination);
    first_destination_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(1_419_976, false),
    );
    first_destination_root.set_field_u32(get_field_by_symbol("sfFlags"), 0);
    first_destination_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 1);
    first_destination_root.set_field_u32(get_field_by_symbol("sfSequence"), 20_176_928);
    first_destination_root.set_field_h256(
        get_field_by_symbol("sfPreviousTxnID"),
        Uint256::from_hex("228775FF8A31697F072D73E5D582B60E83AC97A78202674C09196E563DDD67C1")
            .expect("prior destination transaction"),
    );
    first_destination_root.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 20_176_929);

    let mut issuer_root = STLedgerEntry::new(issuer_keylet);
    issuer_root.set_account_id(get_field_by_symbol("sfAccount"), issuer);
    issuer_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(100_000_000, false),
    );
    issuer_root.set_field_u32(get_field_by_symbol("sfFlags"), 0x4080_0000);
    issuer_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 2);
    issuer_root.set_field_u32(get_field_by_symbol("sfSequence"), 19_089_239);
    issuer_root.set_field_u32(get_field_by_symbol("sfTransferRate"), 1_600_000_000);

    let mut line = STLedgerEntry::new(line_keylet);
    line.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::from_iou_amount(
            get_field_by_symbol("sfBalance"),
            protocol::IOUAmount::from_parts(-9_858, 0).expect("line balance"),
            protocol::Issue::new(currency, protocol::no_account()),
        ),
    );
    line.set_field_u32(get_field_by_symbol("sfFlags"), 2_228_224);
    line.set_field_amount(
        get_field_by_symbol("sfHighLimit"),
        STAmount::from_iou_amount(
            get_field_by_symbol("sfHighLimit"),
            protocol::IOUAmount::from_parts(1_000_000_000_000_000, -3).expect("high limit"),
            protocol::Issue::new(currency, source),
        ),
    );
    line.set_field_u64(get_field_by_symbol("sfHighNode"), 0);
    line.set_field_amount(
        get_field_by_symbol("sfLowLimit"),
        STAmount::from_iou_amount(
            get_field_by_symbol("sfLowLimit"),
            protocol::IOUAmount::new(),
            protocol::Issue::new(currency, issuer),
        ),
    );
    line.set_field_u64(get_field_by_symbol("sfLowNode"), 4);
    line.set_field_h256(
        get_field_by_symbol("sfPreviousTxnID"),
        Uint256::from_hex("44AB98E63A202EB959DFE839961C9BD303D0AB88F8E131E3A42E7F2641613225")
            .expect("prior line transaction"),
    );
    line.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 20_176_921);

    let mut base = Ledger::new(
        LedgerHeader {
            seq: 20_176_955,
            ..LedgerHeader::default()
        },
        false,
    );
    base.raw_insert(Arc::new(source_root)).expect("seed source");
    base.raw_insert(Arc::new(issuer_root)).expect("seed issuer");
    base.raw_insert(Arc::new(first_destination_root))
        .expect("seed first destination");
    base.raw_insert(Arc::new(line)).expect("seed line");
    let mut parent = Sandbox::new(Arc::new(base), ApplyFlags::NONE);
    let rules = parent.rules();

    let first_tx_bytes = decode_hex_fixture(concat!(
        "120000239B57C2E6240133E017201B0133E0426140000000001E848068400000000000000C73210308A2B0692D1DF7143352893A0DD6709DDAEC55587B5542FE180475C509E9981A",
        "744630440220759EF2278E0DC615C9E798D0AAB274FA943D331A2FC638DA37872907F1EED53D02200CA65AE963CF8D86D1DCA5D7B3808ED3F2A8876254A3332F7F774EAEB58FB551",
        "8114DA14CEE8905DF6907639868881DDC04E68B0561A831418165369BE2028B1BB00A5B312F88BA8E4914B61"
    ));
    let mut first_sit = protocol::SerialIter::new(&first_tx_bytes);
    let first_tx = STTx::from_serial_iter(&mut first_sit);
    let mut first_attempt = FlowSandbox::new_with_flags(&mut parent, ApplyFlags::RETRY);
    let first_outcome = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim(
        &mut first_attempt,
        &first_tx,
        TxType::PAYMENT,
        ApplyFlags::RETRY,
        Ter::TES_SUCCESS,
    );
    assert_eq!(first_outcome.result, Ter::TES_SUCCESS);
    assert_eq!(first_outcome.delivered_amount, None);
    let mut first_metadata = first_attempt
        .to_tx_meta(
            first_tx.get_transaction_id(),
            20_176_955,
            first_outcome.delivered_amount,
            &rules,
        )
        .expect("build first metadata");
    let mut first_serialized = protocol::Serializer::default();
    first_metadata.add_raw(&mut first_serialized, Ter::TES_SUCCESS, 2);
    assert_eq!(
        first_serialized.data(),
        decode_hex_fixture("201C00000002F8E5110061250133E02155228775FF8A31697F072D73E5D582B60E83AC97A78202674C09196E563DDD67C1562B866A8F880DB0BCDDA3AA8840CA2F83EE20C5C556A21AB5DF2E431515A81619E662400000000015AAC8E1E72200000000240133E0202D00000001624000000000342F48811418165369BE2028B1BB00A5B312F88BA8E4914B61E1E1E5110061250133E01B550094F2FE19FB023EE0FFE210946E247B3E81585B2B859D3FCE658D4EB05217FE56D59009FC59944F025BF20E113DA257810B17163EA4E0248FCB259E38FD338BF0E6240133E0176240000000060B8BC8E1E72200000000240133E0182D00000001624000000005ED073C8114DA14CEE8905DF6907639868881DDC04E68B0561AE1E1F1031000").as_slice()
    );
    first_attempt
        .apply_with_tx_thread(first_tx.get_transaction_id(), 20_176_955, &rules)
        .expect("commit first transaction");

    let tx_bytes = decode_hex_fixture(concat!(
        "120000239B57C2E6240133E018201B0133E3BE61D4C71AFD498D000000000000000000000000000042535400000000001B2C66A24273A3C742080CE90631F2D7A638C3FE",
        "68400000000000000C73210308A2B0692D1DF7143352893A0DD6709DDAEC55587B5542FE180475C509E9981A74473045022100FD5E91D136A26CE95EA3CD00401A9ABC933",
        "701B438DFCAC3575FC34ECBB474AF0220687018FBBDCDA821728081808DD7E0840FDC57B6ED84393E5688592935F1DC308114DA14CEE8905DF6907639868881DDC04E68B0561",
        "A83141B2C66A24273A3C742080CE90631F2D7A638C3FE"
    ));
    let mut sit = protocol::SerialIter::new(&tx_bytes);
    let tx = STTx::from_serial_iter(&mut sit);
    assert!(sit.empty());

    let mut attempt = FlowSandbox::new_with_flags(&mut parent, ApplyFlags::RETRY);
    let outcome = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim(
        &mut attempt,
        &tx,
        TxType::PAYMENT,
        ApplyFlags::RETRY,
        Ter::TES_SUCCESS,
    );
    assert_eq!(outcome.result, Ter::TES_SUCCESS);
    assert!(outcome.applied);
    assert_eq!(
        outcome.delivered_amount, None,
        "an exact Payment must not serialize sfDeliveredAmount"
    );

    let mut metadata = attempt
        .to_tx_meta(
            tx.get_transaction_id(),
            20_176_955,
            outcome.delivered_amount,
            &rules,
        )
        .expect("build metadata");
    let mut serialized = protocol::Serializer::default();
    metadata.add_raw(&mut serialized, Ter::TES_SUCCESS, 3);
    let expected = decode_hex_fixture(
        "201C00000003F8E5110072250133E0195544AB98E63A202EB959DFE839961C9BD303D0AB88F8E131E3A42E7F264161322556B3373AF6C010FAE7811DEA0607B549944A74453DE64FA7CCFD390FECC1ACEE8EE662956305CC7C32200000000000000000000000000042535400000000000000000000000000000000000000000000000001E1E72200220000370000000000000004380000000000000000629562F39BDF4CE0000000000000000000000000004253540000000000000000000000000000000000000000000000000166800000000000000000000000000000000000000042535400000000001B2C66A24273A3C742080CE90631F2D7A638C3FE67D7838D7EA4C680000000000000000000000000004253540000000000DA14CEE8905DF6907639868881DDC04E68B0561AE1E1E5110061250133E03B55934D06D0634FCDC7F310301DF8A6648B3D3B6E7CC93F38E5E7AF0C47BF6E8ECE56D59009FC59944F025BF20E113DA257810B17163EA4E0248FCB259E38FD338BF0E6240133E018624000000005ED073CE1E72200000000240133E0192D00000001624000000005ED07308114DA14CEE8905DF6907639868881DDC04E68B0561AE1E1F1031000",
    );
    assert_eq!(serialized.data(), expected.as_slice());
}

#[test]
fn clawback_ledger_20197848_matches_canonical_metadata() {
    let issuer = protocol::parse_base58_account_id("rscFuQuPHKH4ov3faze4GJZT3MzEgV4YYb")
        .expect("issuer account");
    let holder = protocol::parse_base58_account_id("r4f4xLpXJtCh9PwdzsQ6KYwLevVnBpJV6f")
        .expect("holder account");
    let currency = protocol::currency_from_string("CLW");

    let mut issuer_root = STLedgerEntry::new(account_keylet(raw_account_id(issuer)));
    issuer_root.set_account_id(get_field_by_symbol("sfAccount"), issuer);
    issuer_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(99_999_964, false),
    );
    issuer_root.set_field_u32(get_field_by_symbol("sfFlags"), 2_155_872_256);
    issuer_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 0);
    issuer_root.set_field_u32(get_field_by_symbol("sfSequence"), 20_197_787);
    issuer_root.set_field_h256(
        get_field_by_symbol("sfPreviousTxnID"),
        Uint256::from_hex("707F393E53A45FDE16D8C5A47825252EA83DFE8AE6CC1FEB384CFEB6D056F1CE")
            .expect("issuer previous transaction"),
    );
    issuer_root.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 20_197_793);

    let mut holder_root = STLedgerEntry::new(account_keylet(raw_account_id(holder)));
    holder_root.set_account_id(get_field_by_symbol("sfAccount"), holder);
    holder_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(348_177_633, false),
    );
    holder_root.set_field_u32(get_field_by_symbol("sfFlags"), 8_388_608);
    holder_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 489);
    holder_root.set_field_u32(get_field_by_symbol("sfSequence"), 13_211_557);

    let line_keylet = protocol::line(issuer, holder, currency);
    let mut line = STLedgerEntry::new(line_keylet);
    line.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::from_iou_amount(
            get_field_by_symbol("sfBalance"),
            protocol::IOUAmount::from_parts(-500, 0).expect("line balance"),
            protocol::Issue::new(currency, protocol::no_account()),
        ),
    );
    line.set_field_u32(get_field_by_symbol("sfFlags"), 2_228_224);
    line.set_field_amount(
        get_field_by_symbol("sfHighLimit"),
        STAmount::from_iou_amount(
            get_field_by_symbol("sfHighLimit"),
            protocol::IOUAmount::from_parts(1_000_000, 0).expect("high limit"),
            protocol::Issue::new(currency, holder),
        ),
    );
    // UInt64 JSON fields are hexadecimal strings; canonical "41" is 0x41.
    line.set_field_u64(get_field_by_symbol("sfHighNode"), 0x41);
    line.set_field_amount(
        get_field_by_symbol("sfLowLimit"),
        STAmount::from_iou_amount(
            get_field_by_symbol("sfLowLimit"),
            protocol::IOUAmount::new(),
            protocol::Issue::new(currency, issuer),
        ),
    );
    line.set_field_u64(get_field_by_symbol("sfLowNode"), 0);
    line.set_field_h256(
        get_field_by_symbol("sfPreviousTxnID"),
        Uint256::from_hex("707F393E53A45FDE16D8C5A47825252EA83DFE8AE6CC1FEB384CFEB6D056F1CE")
            .expect("line previous transaction"),
    );
    line.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 20_197_793);

    let mut base = Ledger::new(
        LedgerHeader {
            seq: 20_197_848,
            ..LedgerHeader::default()
        },
        false,
    );
    base.raw_insert(Arc::new(issuer_root)).expect("seed issuer");
    base.raw_insert(Arc::new(holder_root)).expect("seed holder");
    base.raw_insert(Arc::new(line)).expect("seed trust line");
    let mut parent = Sandbox::new(Arc::new(base), ApplyFlags::NONE);
    let rules = parent.rules();

    let tx_bytes = decode_hex_fixture(
        "12001E2305F6081A240134319B201B013431EB61D5044364C5BB0000000000000000000000000000434C570000000000E78F76A49DD9158FA85DA4AAD95C0767303CC46168400000000000000C7321EDD93C87A1D380ECBAB63CACA6E580061A14D71EF07F794A3CC5FDAB095C8B2D127440E5E84CD3BBB922019A31EA1DDA8EB1C5DC4D6DF57BC339FEBD234CFD9872DB4FBE0B90E4FE74335E134EC3269D8FE8586560B4689153A382CF07BA5D6D3E0C0781141CB6CC5625F6A6FEE009AECD3CAD8F2FB2B953AB",
    );
    let mut sit = protocol::SerialIter::new(&tx_bytes);
    let tx = STTx::from_serial_iter(&mut sit);
    assert!(sit.empty());

    let mut attempt = FlowSandbox::new_with_flags(&mut parent, ApplyFlags::RETRY);
    let outcome = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim(
        &mut attempt,
        &tx,
        TxType::CLAWBACK,
        ApplyFlags::RETRY,
        Ter::TES_SUCCESS,
    );
    assert_eq!(outcome.result, Ter::TES_SUCCESS);
    let mut metadata = attempt
        .to_tx_meta(tx.get_transaction_id(), 20_197_848, None, &rules)
        .expect("build Clawback metadata");
    let mut serialized = protocol::Serializer::default();
    metadata.add_raw(&mut serialized, Ter::TES_SUCCESS, 1);

    let expected = decode_hex_fixture(
        "201C00000001F8E511006125013431A155707F393E53A45FDE16D8C5A47825252EA83DFE8AE6CC1FEB384CFEB6D056F1CE56596B67FFE48EEA091EA43E3190487597035EC14AC08DFF1F12CE1BD54026C389E6240134319B624000000005F5E0DCE1E72280800000240134319C2D00000000624000000005F5E0D081141CB6CC5625F6A6FEE009AECD3CAD8F2FB2B953ABE1E1E511007225013431A155707F393E53A45FDE16D8C5A47825252EA83DFE8AE6CC1FEB384CFEB6D056F1CE56D3477E769AC1B0534CC8250E4A5867E51AB6E0DBCE8EC814E9B71C64882432F7E6629511C37937E08000000000000000000000000000434C5700000000000000000000000000000000000000000000000001E1E7220022000037000000000000000038000000000000004162950D801472258000000000000000000000000000434C5700000000000000000000000000000000000000000000000001668000000000000000000000000000000000000000434C5700000000001CB6CC5625F6A6FEE009AECD3CAD8F2FB2B953AB67D6038D7EA4C68000000000000000000000000000434C570000000000E78F76A49DD9158FA85DA4AAD95C0767303CC461E1E1F1031000",
    );
    assert_eq!(serialized.data(), expected.as_slice());
}

#[test]
fn signer_list_set_ledger_20197848_matches_canonical_metadata() {
    let account = protocol::parse_base58_account_id("r9iCr4Zdrih3UfLgKkeW8bcoo5Ww4zK9z6")
        .expect("signer-list account");
    let mut root = STLedgerEntry::new(account_keylet(raw_account_id(account)));
    root.set_account_id(get_field_by_symbol("sfAccount"), account);
    root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(99_999_990, false),
    );
    root.set_field_u32(get_field_by_symbol("sfFlags"), 8_388_608);
    root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 0);
    root.set_field_u32(get_field_by_symbol("sfSequence"), 20_197_845);
    root.set_field_h256(
        get_field_by_symbol("sfPreviousTxnID"),
        Uint256::from_hex("D89517ED11FAF72714CC6C4CF400BCD86BECF2230352F6FBBD3CB459789BBB98")
            .expect("account previous transaction"),
    );
    root.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 20_197_845);

    let mut base = Ledger::new(
        LedgerHeader {
            seq: 20_197_848,
            ..LedgerHeader::default()
        },
        false,
    );
    base.set_rules(Rules::new([
        protocol::feature_id("MultiSignReserve"),
        protocol::feature_id("fixIncludeKeyletFields"),
    ]));
    base.raw_insert(Arc::new(root)).expect("seed account");
    let mut parent = Sandbox::new(Arc::new(base), ApplyFlags::NONE);
    let rules = parent.rules();

    let tx_bytes = decode_hex_fixture(
        "12000C220000000024013431D5201B013431E920230000000168400000000000000A7321ED17F9B48FDED171A05335FCCBAFC694B7AB899F1E27CABF04B3E4BC74A03991A67440AFF17F8A1B11E4008F53F331E448D9FE789AF60A5B7F95B6B43DA91BF1585631C7BD2EB43CF26D2DB90A924C6562616AED648C5ABF4862EA6CC850ABDE6C3F00811461251D53379CE80CCB388F9FC1E7D9DB07AA253BF4EB1300018114D37D7648AFE3622168F68C76B21020F9F38F5720E1EB130001811409054C92B3DC3DE64581C0E574705C0016D1C6E8E1EB1300018114583727F31F9AF00548D5F001FA528283450BA3E5E1EB1300018114877BB195E7B297BA1AF7DEE6A4B2E2D561930F7FE1EB130001811499A3E76669876DF13CB82846C87B34469DBE84AAE1EB13000181144062CC266C97417295FAAB1BB4334B5DF1987E11E1EB130001811437185E0697511FCC08089A9CC004D2D8C9631FE6E1F1",
    );
    let mut sit = protocol::SerialIter::new(&tx_bytes);
    let tx = STTx::from_serial_iter(&mut sit);
    assert!(sit.empty());

    let mut attempt = FlowSandbox::new_with_flags(&mut parent, ApplyFlags::RETRY);
    let outcome = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim(
        &mut attempt,
        &tx,
        TxType::SIGNER_LIST_SET,
        ApplyFlags::RETRY,
        Ter::TES_SUCCESS,
    );
    assert_eq!(outcome.result, Ter::TES_SUCCESS);
    let mut metadata = attempt
        .to_tx_meta(tx.get_transaction_id(), 20_197_848, None, &rules)
        .expect("build SignerListSet metadata");
    let mut serialized = protocol::Serializer::default();
    metadata.add_raw(&mut serialized, Ter::TES_SUCCESS, 0);

    let expected = decode_hex_fixture(
        "201C00000000F8E511006125013431D555D89517ED11FAF72714CC6C4CF400BCD86BECF2230352F6FBBD3CB459789BBB985606F2DF5269518839BBF7A4F2C7A96113209A83DC941EC75986264C350A5E9730E624013431D52D00000000624000000005F5E0F6E1E7220080000024013431D62D00000001624000000005F5E0EC811461251D53379CE80CCB388F9FC1E7D9DB07AA253BE1E1E311006456A01346FB0C6E67EC42DBFEE7DEE729B9712060AD3E744023FDBB02D49F05A7EDE858A01346FB0C6E67EC42DBFEE7DEE729B9712060AD3E744023FDBB02D49F05A7ED821461251D53379CE80CCB388F9FC1E7D9DB07AA253BE1E1E311005356B76E5C5E7B135A7A5EF374B98F31836FF28E6B761156EBA2AEF933F178EF036CE82200010000202300000001821461251D53379CE80CCB388F9FC1E7D9DB07AA253BF4EB130001811409054C92B3DC3DE64581C0E574705C0016D1C6E8E1EB130001811437185E0697511FCC08089A9CC004D2D8C9631FE6E1EB13000181144062CC266C97417295FAAB1BB4334B5DF1987E11E1EB1300018114583727F31F9AF00548D5F001FA528283450BA3E5E1EB1300018114877BB195E7B297BA1AF7DEE6A4B2E2D561930F7FE1EB130001811499A3E76669876DF13CB82846C87B34469DBE84AAE1EB1300018114D37D7648AFE3622168F68C76B21020F9F38F5720E1F1E1E1F1031000",
    );
    assert_eq!(serialized.data(), expected.as_slice());
}

fn payment_tx(
    source: AccountID,
    destination: AccountID,
    sequence: u32,
    ticket_sequence: Option<u32>,
    fee_drops: u64,
) -> Arc<STTx> {
    Arc::new(STTx::new(TxType::PAYMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), source);
        tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(1_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(fee_drops, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        if let Some(ticket_sequence) = ticket_sequence {
            tx.set_field_u32(get_field_by_symbol("sfTicketSequence"), ticket_sequence);
        }
    }))
}

fn signed_payment_tx(
    seed: u8,
    destination: AccountID,
    sequence: u32,
    fee_drops: u64,
) -> (AccountID, Arc<STTx>) {
    let secret = SecretKey::from_bytes([seed; 32]);
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
            STAmount::new_native(fee_drops, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    });
    tx.sign(&public, &secret, None)
        .expect("signature should succeed");
    (source, Arc::new(tx))
}

fn signed_payment_tx_with_account_txn_id(
    seed: u8,
    destination: AccountID,
    sequence: u32,
    account_txn_id: Uint256,
    fee_drops: u64,
) -> (AccountID, Arc<STTx>) {
    let secret = SecretKey::from_bytes([seed; 32]);
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
            STAmount::new_native(fee_drops, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        tx.set_field_h256(get_field_by_symbol("sfAccountTxnID"), account_txn_id.into());
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    });
    tx.sign(&public, &secret, None)
        .expect("signature should succeed");
    (source, Arc::new(tx))
}

fn signed_payment_tx_with_ticket(
    seed: u8,
    destination: AccountID,
    ticket_sequence: u32,
    fee_drops: u64,
) -> (AccountID, Arc<STTx>) {
    let secret = SecretKey::from_bytes([seed; 32]);
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
            STAmount::new_native(fee_drops, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 0);
        tx.set_field_u32(get_field_by_symbol("sfTicketSequence"), ticket_sequence);
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    });
    tx.sign(&public, &secret, None)
        .expect("signature should succeed");
    (source, Arc::new(tx))
}

fn signed_escrow_create_tx_with_ticket(
    seed: u8,
    destination: AccountID,
    ticket_sequence: u32,
    fee_drops: u64,
) -> (AccountID, Arc<STTx>) {
    let secret = SecretKey::from_bytes([seed; 32]);
    let public = derive_public_key(KeyType::Secp256k1, &secret).expect("public key");
    let source = calc_account_id(public.as_bytes());
    let mut tx = STTx::new(TxType::ESCROW_CREATE, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), source);
        tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(1_000, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfFinishAfter"), 1_000);
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(fee_drops, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 0);
        tx.set_field_u32(get_field_by_symbol("sfTicketSequence"), ticket_sequence);
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    });
    tx.sign(&public, &secret, None)
        .expect("signature should succeed");
    (source, Arc::new(tx))
}

fn signed_ticket_create_tx(
    seed: u8,
    sequence: u32,
    ticket_count: u32,
    fee_drops: u64,
) -> (AccountID, Arc<STTx>) {
    let secret = SecretKey::from_bytes([seed; 32]);
    let public = derive_public_key(KeyType::Secp256k1, &secret).expect("public key");
    let source = calc_account_id(public.as_bytes());
    let mut tx = STTx::new(TxType::TICKET_CREATE, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), source);
        tx.set_field_u32(get_field_by_symbol("sfTicketCount"), ticket_count);
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(fee_drops, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    });
    tx.sign(&public, &secret, None)
        .expect("signature should succeed");
    (source, Arc::new(tx))
}

fn signed_set_regular_key_tx(
    source: AccountID,
    signer_seed: u8,
    sequence: u32,
    fee_drops: u64,
    regular_key: Option<AccountID>,
) -> Arc<STTx> {
    let secret = SecretKey::from_bytes([signer_seed; 32]);
    let public = derive_public_key(KeyType::Secp256k1, &secret).expect("public key");
    let mut tx = STTx::new(TxType::REGULAR_KEY_SET, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), source);
        tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(fee_drops, false),
        );
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
        if let Some(regular_key) = regular_key {
            tx.set_account_id(get_field_by_symbol("sfRegularKey"), regular_key);
        }
    });
    tx.sign(&public, &secret, None)
        .expect("signature should succeed");
    Arc::new(tx)
}

fn ledger_view(seq: u32, account: AccountID, account_sequence: u32, tx_ids: &[Uint256]) -> Ledger {
    let mut state_tree = MutableTree::new(1);
    let mut account_root = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        account_keylet(raw_account_id(account)).key,
    );
    account_root.set_account_id(get_field_by_symbol("sfAccount"), account);
    account_root.set_field_u32(get_field_by_symbol("sfSequence"), account_sequence);
    account_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(1_000_000_000, false),
    );
    state_tree
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                account_keylet(raw_account_id(account)).key,
                account_root.get_serializer().data().to_vec(),
            ),
        )
        .expect("account root should insert");

    let fee_keylet = fee_settings_keylet();
    state_tree
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                fee_keylet.key,
                encode_fee_settings_entry(
                    Fees {
                        base: 10,
                        reserve: 1_000_000,
                        increment: 200_000,
                    },
                    false,
                ),
            ),
        )
        .expect("fee settings should insert");

    let mut tx_tree = MutableTree::new(1);
    for (index, tx_id) in tx_ids.iter().enumerate() {
        tx_tree
            .add_item(
                SHAMapNodeType::TransactionNm,
                SHAMapItem::new(*tx_id, vec![index as u8 + 1; 12]),
            )
            .expect("tx should insert");
    }

    Ledger::from_maps(
        LedgerHeader {
            seq,
            close_time: 800 + seq,
            close_time_resolution: LEDGER_DEFAULT_TIME_RESOLUTION,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_tree.root(),
            SHAMapType::State,
            false,
            seq,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_tree.root(),
            SHAMapType::Transaction,
            false,
            seq,
            SyncState::Modifying,
        ),
    )
}

fn ledger_view_with_balance_and_owner_count(
    seq: u32,
    account: AccountID,
    account_sequence: u32,
    balance_drops: u64,
    owner_count: u32,
    tx_ids: &[Uint256],
) -> Ledger {
    let mut state_tree = MutableTree::new(1);
    let mut account_root = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        account_keylet(raw_account_id(account)).key,
    );
    account_root.set_account_id(get_field_by_symbol("sfAccount"), account);
    account_root.set_field_u32(get_field_by_symbol("sfSequence"), account_sequence);
    account_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(balance_drops, false),
    );
    account_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), owner_count);
    state_tree
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                account_keylet(raw_account_id(account)).key,
                account_root.get_serializer().data().to_vec(),
            ),
        )
        .expect("account root should insert");

    let mut tx_tree = MutableTree::new(1);
    for (index, tx_id) in tx_ids.iter().enumerate() {
        tx_tree
            .add_item(
                SHAMapNodeType::TransactionNm,
                SHAMapItem::new(*tx_id, vec![index as u8 + 1; 12]),
            )
            .expect("tx should insert");
    }

    Ledger::from_maps(
        LedgerHeader {
            seq,
            close_time: 800 + seq,
            close_time_resolution: LEDGER_DEFAULT_TIME_RESOLUTION,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_tree.root(),
            SHAMapType::State,
            false,
            seq,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_tree.root(),
            SHAMapType::Transaction,
            false,
            seq,
            SyncState::Modifying,
        ),
    )
}

fn ledger_view_with_account_txn_id(
    seq: u32,
    account: AccountID,
    account_sequence: u32,
    account_txn_id: Uint256,
    tx_ids: &[Uint256],
) -> Ledger {
    let mut state_tree = MutableTree::new(1);
    let mut account_root = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        account_keylet(raw_account_id(account)).key,
    );
    account_root.set_account_id(get_field_by_symbol("sfAccount"), account);
    account_root.set_field_u32(get_field_by_symbol("sfSequence"), account_sequence);
    account_root.set_field_h256(get_field_by_symbol("sfAccountTxnID"), account_txn_id.into());
    account_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(1_000_000_000, false),
    );
    state_tree
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                account_keylet(raw_account_id(account)).key,
                account_root.get_serializer().data().to_vec(),
            ),
        )
        .expect("account root should insert");

    let mut tx_tree = MutableTree::new(1);
    for (index, tx_id) in tx_ids.iter().enumerate() {
        tx_tree
            .add_item(
                SHAMapNodeType::TransactionNm,
                SHAMapItem::new(*tx_id, vec![index as u8 + 1; 12]),
            )
            .expect("tx should insert");
    }

    Ledger::from_maps(
        LedgerHeader {
            seq,
            close_time: 800 + seq,
            close_time_resolution: LEDGER_DEFAULT_TIME_RESOLUTION,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_tree.root(),
            SHAMapType::State,
            false,
            seq,
            SyncState::Modifying,
        ),
        SyncTree::from_root_with_type(
            tx_tree.root(),
            SHAMapType::Transaction,
            false,
            seq,
            SyncState::Modifying,
        ),
    )
}

fn ledger_view_with_ticket(
    seq: u32,
    account: AccountID,
    account_sequence: u32,
    balance_drops: u64,
    ticket_seq: SeqProxy,
) -> Ledger {
    let mut state_tree = MutableTree::new(1);
    let mut account_root = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        account_keylet(raw_account_id(account)).key,
    );
    account_root.set_account_id(get_field_by_symbol("sfAccount"), account);
    account_root.set_field_u32(get_field_by_symbol("sfSequence"), account_sequence);
    account_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(balance_drops, false),
    );
    state_tree
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                account_keylet(raw_account_id(account)).key,
                account_root.get_serializer().data().to_vec(),
            ),
        )
        .expect("account root should insert");

    let ticket = STLedgerEntry::from_type_and_key(
        LedgerEntryType::Ticket,
        ticket_keylet_from_seq_proxy(raw_account_id(account), ticket_seq).key,
    );
    state_tree
        .add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(
                ticket_keylet_from_seq_proxy(raw_account_id(account), ticket_seq).key,
                ticket.get_serializer().data().to_vec(),
            ),
        )
        .expect("ticket should insert");

    Ledger::from_maps(
        LedgerHeader {
            seq,
            close_time: 800 + seq,
            close_time_resolution: LEDGER_DEFAULT_TIME_RESOLUTION,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_tree.root(),
            SHAMapType::State,
            false,
            seq,
            SyncState::Modifying,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, false, seq),
    )
}

fn apply_submit_tx_for_test<V: ApplyView>(
    open_ledger: &mut AppOpenLedgerView,
    submit_view: &mut V,
    tx: Arc<STTx>,
    current_ledger_index: u32,
) -> ApplyResult {
    apply_submit_tx_for_test_with_flags(
        open_ledger,
        submit_view,
        tx,
        current_ledger_index,
        ApplyFlags::NONE,
    )
}

fn apply_submit_tx_for_test_with_flags<V: ApplyView>(
    open_ledger: &mut AppOpenLedgerView,
    submit_view: &mut V,
    tx: Arc<STTx>,
    current_ledger_index: u32,
    flags: ApplyFlags,
) -> ApplyResult {
    let fee_track = crate::load::load_fee_track::SharedLoadFeeTrack::new();
    let mut runtime = AppOpenLedgerTxQApplyRuntime::new(
        open_ledger,
        submit_view,
        tx,
        flags,
        current_ledger_index,
        &fee_track,
        Arc::new(std::sync::Mutex::new(std::collections::HashMap::new())),
    );
    runtime.direct_apply()
}

#[test]
fn simulate_clones_persistent_open_view_sequence_and_balance() {
    // Simulate.cpp::simulateTxn copies OpenLedger::current() before
    // TxQ::apply(TapDryRun). The Rust persistent submit sandbox is that live
    // OpenView: this regression fails with the old closed-parent-only base,
    // because `second` then sees sequence 1 rather than the live sequence 2.
    let destination = AccountID::from_array([0xC1; 20]);
    let (source, first) = signed_payment_tx(0xC1, destination, 1, 10);
    let (_, second) = signed_payment_tx(0xC1, destination, 2, 10);
    let base = Arc::new(ledger_view(10, source, 1, &[]));
    let mut live = Sandbox::new(
        Arc::new(OpenView::new_open(Arc::clone(&base), base.rules().clone())),
        ApplyFlags::NONE,
    );
    let mut open =
        AppOpenLedgerView::with_parent_hash(11, base.fees().base, *base.header().hash.as_uint256());

    assert!(
        live.open(),
        "persistent submit view must retain OpenView semantics"
    );

    assert_eq!(
        apply_submit_tx_for_test(&mut open, &mut live, Arc::clone(&first), 11),
        ApplyResult::new(Ter::TES_SUCCESS, true, false),
    );
    let live_account = live
        .read(account_keylet(raw_account_id(source)))
        .expect("live account read")
        .expect("live source account");
    let live_balance = live_account
        .get_field_amount(get_field_by_symbol("sfBalance"))
        .xrp()
        .drops();
    assert_eq!(
        live_account.get_field_u32(get_field_by_symbol("sfSequence")),
        2
    );
    assert!(
        live_balance
            < base
                .read(account_keylet(raw_account_id(source)))
                .expect("base account read")
                .expect("base source account")
                .get_field_amount(get_field_by_symbol("sfBalance"))
                .xrp()
                .drops(),
        "the persistent open view must include the first transaction's fee/balance state"
    );

    let root = ApplicationRoot::new(0).expect("application root should build");
    root.open_ledger().modify(|current| {
        *current = open;
        true
    });
    *root.open_ledger_sandbox.lock().expect("sandbox mutex") = Some(live);

    let rpc_current_account = root
        .current_open_ledger_entry(account_keylet(raw_account_id(source)))
        .expect("persistent current open view must be published")
        .expect("current open account read must succeed")
        .expect("current open source account must exist");
    assert_eq!(
        rpc_current_account.get_field_u32(get_field_by_symbol("sfSequence")),
        2,
        "current-ledger RPC reads must observe the persistent OpenView mutation"
    );

    let outcome = root.simulate_transaction(Arc::clone(&base), Arc::clone(&second));
    assert_eq!(outcome.result.ter, Ter::TES_SUCCESS);
    assert!(
        !outcome.result.applied,
        "TapDryRun must report a non-published simulation"
    );

    let retained = root
        .open_ledger_sandbox
        .lock()
        .expect("sandbox mutex")
        .as_ref()
        .expect("persistent open view must remain installed")
        .read(account_keylet(raw_account_id(source)))
        .expect("retained account read")
        .expect("retained source account");
    assert_eq!(retained.get_field_u32(get_field_by_symbol("sfSequence")), 2);
    assert_eq!(
        retained
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        live_balance,
        "simulation must clone, never mutate, the persistent open view"
    );
}

#[test]
fn signing_sequence_uses_rebuilt_open_sandbox_not_legacy_cache() {
    // TransactionSign.cpp reads OpenLedger::current() and then uses TxQ's
    // nextQueuableSeq. A LocalTx rebase reconstructs this sandbox but does
    // not reconstruct Quaxar's old monotonic cache; signing must therefore
    // use the sandbox rather than the cache or it will create duplicates/gaps.
    let destination = AccountID::from_array([0xC2; 20]);
    let (source, first) = signed_payment_tx(0xC2, destination, 1, 10);
    let (_, next) = signed_payment_tx(0xC2, destination, 2, 10);
    let base = Arc::new(ledger_view(10, source, 1, &[]));
    let mut sandbox = Sandbox::new(
        Arc::new(OpenView::new_open(Arc::clone(&base), base.rules().clone())),
        ApplyFlags::NONE,
    );
    let mut open =
        AppOpenLedgerView::with_parent_hash(11, base.fees().base, *base.header().hash.as_uint256());

    assert_eq!(
        apply_submit_tx_for_test(&mut open, &mut sandbox, first, 11),
        ApplyResult::new(Ter::TES_SUCCESS, true, false),
    );
    let root = ApplicationRoot::new(0).expect("application root should build");
    root.open_ledger().modify(|current| {
        *current = open;
        true
    });
    *root.open_ledger_sandbox.lock().expect("sandbox mutex") = Some(sandbox);

    // Deliberately poison the obsolete cache with a sequence that could never
    // be derived from the rebuilt OpenView. The signing authority must still
    // return the sandbox account sequence (2), not the cache's 100.
    root.note_open_ledger_tx(&source, 99);
    assert_eq!(root.network_ops_current_account_seq(&source), Some(100));
    assert_eq!(root.network_ops_next_account_seq_for_tx(&next), Some(2));
}

#[test]
fn closed_ledger_notification_preserves_rebuilt_same_parent_submit_sandbox() {
    // Consensus rebuilds OpenLedger before it notifies the closed-LCL side.
    // The notification must retain that exact-parent OpenView: TransactionSign
    // reads it for nextQueuableSeq, and clearing it would make a later submit
    // reuse a sequence already occupied by the rebuilt current open ledger.
    let destination = AccountID::from_array([0xC3; 20]);
    let (source, first) = signed_payment_tx(0xC3, destination, 1, 10);
    let (_, next) = signed_payment_tx(0xC3, destination, 2, 10);
    let parent = Arc::new(ledger_view(10, source, 1, &[]));
    let mut sandbox = Sandbox::new(
        Arc::new(OpenView::new_open(
            Arc::clone(&parent),
            parent.rules().clone(),
        )),
        ApplyFlags::NONE,
    );
    let mut open = AppOpenLedgerView::with_parent_hash(
        11,
        parent.fees().base,
        *parent.header().hash.as_uint256(),
    );
    assert_eq!(
        apply_submit_tx_for_test(&mut open, &mut sandbox, first, 11),
        ApplyResult::new(Ter::TES_SUCCESS, true, false),
    );

    let root = ApplicationRoot::new(0).expect("application root should build");
    root.open_ledger().modify(|current| {
        *current = open;
        true
    });
    *root.open_ledger_sandbox.lock().expect("sandbox mutex") = Some(sandbox);

    // This is the order in the accepted-consensus handoff: the rebuilt
    // same-parent sandbox is live before on_closed_ledger updates LCL state.
    root.on_closed_ledger(Arc::clone(&parent));

    assert!(
        root.open_ledger_sandbox
            .lock()
            .expect("sandbox mutex")
            .is_some(),
        "the exact-parent sandbox must survive closed-ledger notification"
    );
    assert_eq!(
        root.network_ops_next_account_seq_for_tx(&next),
        Some(2),
        "autofill must retain the rebuilt current-open sequence rather than reuse 1"
    );
}

#[test]
fn retry_pass_tec_does_not_commit_until_final_pass() {
    let source = account("ABABABABABABABABABABABABABABABABABABABAB");
    let missing_destination = account("CDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCD");
    let tx = payment_tx(source, missing_destination, 1, None, 10);
    let destination_root = || {
        let mut entry = STLedgerEntry::from_type_and_key(
            LedgerEntryType::AccountRoot,
            account_keylet(raw_account_id(missing_destination)).key,
        );
        entry.set_account_id(get_field_by_symbol("sfAccount"), missing_destination);
        entry.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        entry.set_field_u32(get_field_by_symbol("sfFlags"), protocol::lsfDepositAuth);
        entry.set_field_amount(
            get_field_by_symbol("sfBalance"),
            STAmount::new_native(1_000_000, false),
        );
        entry
    };
    let base = Arc::new(ledger_view(10, source, 1, &[]));

    let mut retry_view = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);
    retry_view
        .insert(Arc::new(destination_root()))
        .expect("retry destination insert");
    assert_eq!(
        apply_submit_transactor_shell_with_flags(
            &mut retry_view,
            &tx,
            TxType::PAYMENT,
            ApplyFlags::RETRY,
        ),
        Ter::TEC_NO_PERMISSION
    );
    let retry_source = retry_view
        .read(account_keylet(raw_account_id(source)))
        .expect("retry source read")
        .expect("retry source account");
    assert_eq!(
        retry_source.get_field_u32(get_field_by_symbol("sfSequence")),
        1,
        "TapRetry must discard a fee-claiming tec so BuildLedger can retry it"
    );

    let mut final_view = Sandbox::new(base, ApplyFlags::NONE);
    final_view
        .insert(Arc::new(destination_root()))
        .expect("final destination insert");
    assert_eq!(
        apply_submit_transactor_shell_with_flags(
            &mut final_view,
            &tx,
            TxType::PAYMENT,
            ApplyFlags::NONE,
        ),
        Ter::TEC_NO_PERMISSION
    );
    let final_source = final_view
        .read(account_keylet(raw_account_id(source)))
        .expect("final source read")
        .expect("final source account");
    assert_eq!(
        final_source.get_field_u32(get_field_by_symbol("sfSequence")),
        2,
        "the final pass must claim the fee and consume the sequence"
    );
}

#[test]
fn retry_outcome_distinguishes_ordinary_and_persistent_cleanup_tec() {
    let source = account("ABABABABABABABABABABABABABABABABABABABAB");
    let destination = account("CDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCD");
    let tx = payment_tx(source, destination, 1, None, 10);
    let account_key = account_keylet(raw_account_id(source));

    // An ordinary handler tec under TapRetry is returned but not committed.
    // Consensus must therefore neither construct metadata/thread the tx nor
    // remove it from the retry set.
    let mut ordinary_parent =
        Sandbox::new(Arc::new(ledger_view(10, source, 1, &[])), ApplyFlags::NONE);
    let mut destination_root = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        account_keylet(raw_account_id(destination)).key,
    );
    destination_root.set_account_id(get_field_by_symbol("sfAccount"), destination);
    destination_root.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    destination_root.set_field_u32(get_field_by_symbol("sfFlags"), protocol::lsfDepositAuth);
    destination_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(1_000_000, false),
    );
    ordinary_parent
        .insert(Arc::new(destination_root))
        .expect("destination insert should succeed");
    let ordinary_rules = ordinary_parent.rules();
    let mut ordinary_attempt = FlowSandbox::new_with_flags(&mut ordinary_parent, ApplyFlags::RETRY);
    let ordinary = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim(
        &mut ordinary_attempt,
        &tx,
        TxType::PAYMENT,
        ApplyFlags::RETRY,
        Ter::TES_SUCCESS,
    );
    assert_eq!(ordinary.result, Ter::TEC_NO_PERMISSION);
    assert!(!ordinary.applied);
    assert_eq!(ordinary_attempt.item_count(), 0);
    let ordinary_meta = ordinary_attempt
        .to_tx_meta(tx.get_transaction_id(), 11, None, &ordinary_rules)
        .expect("empty retry metadata should be representable");
    assert_eq!(ordinary_meta.get_nodes().len(), 0);
    drop(ordinary_attempt);
    assert_eq!(
        ordinary_parent
            .read(account_key)
            .expect("source read should succeed")
            .expect("source should exist")
            .get_field_u32(get_field_by_symbol("sfSequence")),
        1
    );
    assert!(!ordinary_parent.tx_exists(tx.get_transaction_id()).unwrap());

    // Persistent cleanup results are the exception to TapRetry's ordinary
    // tec rule. Even when supplied by preclaim they run reset, commit exactly
    // once, and must be accepted/threaded rather than retried.
    let mut persistent_parent =
        Sandbox::new(Arc::new(ledger_view(10, source, 1, &[])), ApplyFlags::NONE);
    let persistent_rules = persistent_parent.rules();
    let mut persistent_attempt =
        FlowSandbox::new_with_flags(&mut persistent_parent, ApplyFlags::RETRY);
    let persistent = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim(
        &mut persistent_attempt,
        &tx,
        TxType::PAYMENT,
        ApplyFlags::RETRY,
        Ter::TEC_KILLED,
    );
    assert_eq!(persistent.result, Ter::TEC_KILLED);
    assert!(persistent.applied);
    let persistent_meta = persistent_attempt
        .to_tx_meta(tx.get_transaction_id(), 11, None, &persistent_rules)
        .expect("persistent retry metadata should build");
    assert_eq!(persistent_meta.get_nodes().len(), 1);
    persistent_attempt
        .apply_with_tx_thread(tx.get_transaction_id(), 11, &persistent_rules)
        .expect("persistent retry state should commit once");
    let persistent_source = persistent_parent
        .read(account_key)
        .expect("source read should succeed")
        .expect("source should exist");
    assert_eq!(
        persistent_source.get_field_u32(get_field_by_symbol("sfSequence")),
        2
    );
    assert_eq!(
        persistent_source
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        999_999_990,
        "persistent retry outcome must charge the fee exactly once"
    );
    assert_eq!(
        persistent_source.get_field_h256(get_field_by_symbol("sfPreviousTxnID")),
        tx.get_transaction_id()
    );
    assert_eq!(
        persistent_source.get_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq")),
        11
    );
}

#[test]
fn direct_shell_rejects_standalone_inner_batch_and_preclaim_ordering_guards() {
    let source = account("ABABABABABABABABABABABABABABABABABABABAB");
    let destination = account("CDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCD");

    let mut inner = (*payment_tx(source, destination, 1, None, 10)).clone();
    inner.set_field_u32(get_field_by_symbol("sfFlags"), INNER_BATCH_TRANSACTION_FLAG);
    let base = Arc::new(ledger_view(10, source, 1, &[]));
    let mut view = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);
    assert_eq!(
        apply_submit_transactor_shell(&mut view, &inner, TxType::PAYMENT),
        Ter::TEM_INVALID_INNER_BATCH
    );

    let mut wrong_prior = (*payment_tx(source, destination, 1, None, 10)).clone();
    wrong_prior.set_field_h256(get_field_by_symbol("sfAccountTxnID"), Uint256::from_u64(2));
    let mut view = Sandbox::new(
        Arc::new(ledger_view_with_account_txn_id(
            10,
            source,
            1,
            Uint256::from_u64(1),
            &[],
        )),
        ApplyFlags::NONE,
    );
    assert_eq!(
        apply_submit_transactor_shell(&mut view, &wrong_prior, TxType::PAYMENT),
        Ter::TEF_WRONG_PRIOR
    );

    let mut expired = (*payment_tx(source, destination, 1, None, 10)).clone();
    expired.set_field_u32(get_field_by_symbol("sfLastLedgerSequence"), 9);
    let mut view = Sandbox::new(Arc::new(ledger_view(10, source, 1, &[])), ApplyFlags::NONE);
    assert_eq!(
        apply_submit_transactor_shell(&mut view, &expired, TxType::PAYMENT),
        Ter::TEF_MAX_LEDGER
    );

    let replay = (*payment_tx(source, destination, 1, None, 10)).clone();
    let mut view = Sandbox::new(
        Arc::new(ledger_view(10, source, 1, &[replay.get_transaction_id()])),
        ApplyFlags::NONE,
    );
    assert_eq!(
        apply_submit_transactor_shell(&mut view, &replay, TxType::PAYMENT),
        Ter::TEF_ALREADY
    );
}

#[test]
fn closed_ledger_transition_rebases_persistent_submit_state() {
    fn immutable_ledger(seq: u32, parent: u8) -> Arc<Ledger> {
        let mut header = LedgerHeader {
            seq,
            parent_hash: SHAMapHash::new(Uint256::from_array([parent; 32])),
            close_time: seq.saturating_add(10),
            close_time_resolution: LEDGER_DEFAULT_TIME_RESOLUTION,
            ..LedgerHeader::default()
        };
        header.hash = calculate_ledger_hash(&header);
        let mut ledger = Ledger::new(header, true);
        ledger.set_immutable(true);
        Arc::new(ledger)
    }

    let root = ApplicationRoot::new(0).expect("root should build");
    let first = immutable_ledger(100, 0x11);
    let second = immutable_ledger(101, 0x22);
    let account = AccountID::from_array([0xA5; 20]);

    root.on_closed_ledger(Arc::clone(&first));
    *root.open_ledger_sandbox.lock().expect("sandbox mutex") = Some(Sandbox::new(
        Arc::new(OpenView::new_open(
            Arc::clone(&first),
            first.rules().clone(),
        )),
        ApplyFlags::NONE,
    ));
    root.note_open_ledger_tx(&account, 7);
    assert_eq!(
        root.network_ops_current_account_seq(&account),
        Some(8),
        "an accepted open-ledger transaction must advance the next signing sequence",
    );
    root.note_open_ledger_tx(&account, 6);
    assert_eq!(
        root.network_ops_current_account_seq(&account),
        Some(8),
        "out-of-order observations must not regress the next signing sequence",
    );

    root.on_closed_ledger(second);

    assert!(
        root.open_ledger_sandbox
            .lock()
            .expect("sandbox mutex")
            .is_none(),
        "a submit sandbox cannot outlive its parent closed ledger"
    );
    assert_eq!(
        root.network_ops_current_account_seq(&account),
        None,
        "per-account submit sequence state must be rebased with the sandbox"
    );
}

#[test]
fn app_queue_apply_tx_source_reports_sttx_facts_submit_path() {
    let account = AccountID::from_array([0x61; 20]);
    let destination = AccountID::from_array([0x62; 20]);
    let tx = Arc::new(STTx::new(TxType::PAYMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), account);
        tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(1_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(25, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 0);
        tx.set_field_u32(get_field_by_symbol("sfTicketSequence"), 8);
        tx.set_field_h256(
            get_field_by_symbol("sfPreviousTxnID"),
            Uint256::from_u64(9).into(),
        );
        tx.set_field_h256(
            get_field_by_symbol("sfAccountTxnID"),
            Uint256::from_u64(10).into(),
        );
        tx.set_field_u32(get_field_by_symbol("sfLastLedgerSequence"), 123);
    }));

    let source = AppQueueApplyTxSource::new(tx.as_ref());
    assert_eq!(*source.account(), account);
    assert_eq!(source.transaction_id(), tx.get_transaction_id());
    assert_eq!(source.tx_id(), tx.get_transaction_id());
    assert_eq!(source.tx_seq_proxy(), SeqProxy::ticket(8));
    assert!(source.has_previous_txn_id());
    assert!(source.has_account_txn_id());
    assert_eq!(source.last_valid_ledger(), Some(123));
}

#[test]
fn app_open_ledger_queue_apply_view_reads_live_account_and_ticket_facts() {
    let account = AccountID::from_array([0x41; 20]);
    let destination = AccountID::from_array([0x42; 20]);
    let ticket_seq = SeqProxy::ticket(8);
    let ledger = ledger_view_with_ticket(10, account, 7, 5_000, ticket_seq);
    let tx = Arc::new(STTx::new(TxType::PAYMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), account);
        tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(1_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(25, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 0);
        tx.set_field_u32(get_field_by_symbol("sfTicketSequence"), 8);
    }));

    let mut open_ledger = AppOpenLedgerView::with_parent_hash(11, 10, Uint256::from_u64(99));
    open_ledger.push_transaction(Arc::clone(&tx));
    let metrics_snapshot = QueueFeeMetricsSnapshot {
        txns_expected: 32,
        escalation_multiplier: tx::TXQ_BASE_LEVEL * 500,
    };

    let view = open_ledger.queue_apply_view(&ledger, tx.as_ref(), metrics_snapshot);

    assert_eq!(
        view.account_lookup(&account),
        QueueApplyObservedAccountLookup::Present {
            sequence: 7,
            balance_drops: 5_000,
        }
    );
    assert_eq!(
        view.ticket_lookup(&account, ticket_seq),
        QueueApplyObservedTicketLookup::Present
    );
    assert_eq!(
        view.ticket_lookup(&account, SeqProxy::sequence(7)),
        QueueApplyObservedTicketLookup::NotRequired
    );
    assert_eq!(view.fee_paid_drops(), 25);
    assert_eq!(view.open_ledger_tx_count(), 1);
    assert_eq!(view.open_ledger_seq(), 11);
    assert_eq!(view.base_fee_drops(), ledger.fees().base);
    assert_eq!(view.reserve_drops(), ledger.fees().account_reserve(0));
    assert_eq!(view.metrics_snapshot(), metrics_snapshot);
    assert_eq!(view.rules(), &ledger.rules().clone());
}

#[test]
fn local_replay_txq_persists_sequence_chain_and_later_drains() {
    // rippled TxQ::apply returns terPRE_SEQ when an account has no queued
    // predecessor, so it must not be force-queued. Its persistent
    // sequence-chain path queues the current sequence while the open ledger is
    // fee-saturated, then queues the next sequence behind that first entry.
    let destination = AccountID::from_array([0xB2; 20]);
    let (source, first) = signed_payment_tx(0xB1, destination, 1, 10);
    let (same_source, deferred) = signed_payment_tx(0xB1, destination, 2, 10);
    assert_eq!(same_source, source);

    let root = ApplicationRoot::new(0).expect("root should build");
    let parent = Arc::new(ledger_view(10, source, 1, &[]));
    root.process_closed_ledger_txq(parent.as_ref(), false);
    let metrics = root.registry.tx_q.metrics_snapshot();
    assert!(
        root.registry.tx_q.current_max_size().is_some(),
        "closed-ledger maintenance must initialize TxQ admission capacity"
    );

    let mut open_ledger = AppOpenLedgerView::with_parent_hash(
        11,
        parent.fees().base,
        *parent.header().hash.as_uint256(),
    );
    // This count-only saturation makes tryDirectApply fall through to TxQ
    // admission. Filler transactions never mutate the rebase view.
    let saturation_count = u32::try_from(metrics.txns_expected.saturating_mul(2).max(2))
        .expect("test TxQ saturation count must fit in a transaction sequence");
    for sequence in 1..=saturation_count {
        open_ledger.push_transaction(Arc::new(STTx::new(TxType::PAYMENT, |tx| {
            tx.set_account_id(
                get_field_by_symbol("sfAccount"),
                AccountID::from_array([0xD1; 20]),
            );
            tx.set_account_id(
                get_field_by_symbol("sfDestination"),
                AccountID::from_array([0xD2; 20]),
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
        })));
    }
    let mut rebase_view = Sandbox::new(
        Arc::new(OpenView::new_open(
            Arc::clone(&parent),
            parent.rules().clone(),
        )),
        ApplyFlags::NONE,
    );
    let mut applied_ids = std::collections::HashSet::new();

    let first_result = root.apply_local_open_ledger_record_with_txq(
        &mut open_ledger,
        &mut rebase_view,
        &mut applied_ids,
        &super::AppOpenLedgerTxRecord::new(Arc::clone(&first)),
        ApplyFlags::NONE,
    );
    assert_eq!(first_result.ter, Ter::TER_QUEUED);
    assert!(!first_result.applied);

    let deferred_result = root.apply_local_open_ledger_record_with_txq(
        &mut open_ledger,
        &mut rebase_view,
        &mut applied_ids,
        &super::AppOpenLedgerTxRecord::new(Arc::clone(&deferred)),
        ApplyFlags::NONE,
    );
    assert_eq!(deferred_result.ter, Ter::TER_QUEUED);
    assert!(!deferred_result.applied);

    let queued_before = root.registry.tx_q.current_account_txs(source);
    assert_eq!(
        queued_before.len(),
        2,
        "LocalTx sequence chain must persist in TxQ"
    );
    assert_eq!(
        queued_before[0].tx.get_transaction_id(),
        first.get_transaction_id()
    );
    assert_eq!(
        queued_before[1].tx.get_transaction_id(),
        deferred.get_transaction_id()
    );

    // A new open-ledger rebuild starts without saturation. TxQ::accept must
    // apply both persisted LocalTxs in sequence order and remove them.
    open_ledger = AppOpenLedgerView::with_parent_hash(
        11,
        parent.fees().base,
        *parent.header().hash.as_uint256(),
    );
    let snapshot = super::AppOpenLedgerTxQAcceptView {
        open_ledger_tx_count: open_ledger.tx_ids().len(),
        parent_hash: open_ledger.parent_hash,
    };
    let mut runtime = super::AppOpenLedgerTxQAcceptRuntime {
        root: &root,
        view: &mut open_ledger,
        rebase_view: &mut rebase_view,
        applied_ids: &mut applied_ids,
        flags: ApplyFlags::NONE,
    };
    let mut lock = super::AppTxQLock;
    let accepted = root
        .registry
        .tx_q
        .accept(&mut lock, &mut runtime, &snapshot);
    assert!(
        accepted.ledger_changed,
        "TxQ::accept must drain the ready LocalTx chain"
    );

    assert!(
        root.registry.tx_q.current_account_txs(source).is_empty(),
        "the drained LocalTx sequence chain must be removed from persistent TxQ"
    );
    assert_eq!(
        open_ledger.tx_ids(),
        vec![first.get_transaction_id(), deferred.get_transaction_id()],
        "both queued LocalTxs must be applied to the new open ledger in sequence order"
    );
    let source_root = rebase_view
        .read(account_keylet(raw_account_id(source)))
        .expect("source account read should succeed")
        .expect("source account should remain present");
    assert_eq!(
        source_root.get_field_u32(get_field_by_symbol("sfSequence")),
        3,
        "draining the queued transactions must advance live sequence state"
    );
}

#[test]
fn submit_direct_apply_ticket_create_updates_ticket_tracking() {
    let (source, ticket_create) = signed_ticket_create_tx(0x51, 1, 2, 10);
    let base = Arc::new(ledger_view_with_balance_and_owner_count(
        1,
        source,
        1,
        2_000_000,
        0,
        &[],
    ));
    let mut open_ledger =
        AppOpenLedgerView::with_parent_hash(2, 10, *base.header().hash.as_uint256());
    let mut submit_view = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);

    let result = apply_submit_tx_for_test(&mut open_ledger, &mut submit_view, ticket_create, 2);

    assert_eq!(result.ter, Ter::TES_SUCCESS);
    assert!(result.applied);

    let account_root = submit_view
        .read(account_keylet(raw_account_id(source)))
        .expect("account read should succeed")
        .expect("account should exist");
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfSequence")),
        4
    );
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfTicketCount")),
        2
    );
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        2
    );
    assert_eq!(
        account_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_999_990
    );
    assert!(
        submit_view
            .exists(protocol::ticket_keylet(raw_account_id(source), 2))
            .expect("ticket 2 lookup should succeed")
    );
    assert!(
        submit_view
            .exists(protocol::ticket_keylet(raw_account_id(source), 3))
            .expect("ticket 3 lookup should succeed")
    );
}

#[test]
fn set_regular_key_zero_minimum_fee_arms_password_spent() {
    let master_secret = SecretKey::from_bytes([0x61; 32]);
    let master_public =
        derive_public_key(KeyType::Secp256k1, &master_secret).expect("master public key");
    let source = calc_account_id(master_public.as_bytes());
    let regular_key = AccountID::from_array([0x62; 20]);
    let tx = signed_set_regular_key_tx(source, 0x61, 1, 0, Some(regular_key));
    let parent = Arc::new(ledger_view(1, source, 1, &[]));
    let mut view = Sandbox::new(Arc::clone(&parent), ApplyFlags::NONE);

    assert_eq!(
        apply_submit_transactor_shell(&mut view, &tx, TxType::REGULAR_KEY_SET),
        Ter::TES_SUCCESS
    );

    let account_root = view
        .read(account_keylet(raw_account_id(source)))
        .expect("account read should succeed")
        .expect("account should exist");
    assert_eq!(
        account_root.get_account_id(get_field_by_symbol("sfRegularKey")),
        regular_key
    );
    assert_ne!(
        account_root.get_field_u32(get_field_by_symbol("sfFlags")) & protocol::lsfPasswordSpent,
        0,
        "the master-signed zero-minimum-fee transaction must spend the password privilege"
    );
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfSequence")),
        2
    );
    assert_eq!(
        account_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000_000_000,
        "a zero-fee SetRegularKey must not burn XRP"
    );
}

#[test]
fn set_regular_key_cannot_remove_the_last_alternative_key() {
    let master_secret = SecretKey::from_bytes([0x63; 32]);
    let master_public =
        derive_public_key(KeyType::Secp256k1, &master_secret).expect("master public key");
    let source = calc_account_id(master_public.as_bytes());
    let regular_secret = SecretKey::from_bytes([0x64; 32]);
    let regular_public =
        derive_public_key(KeyType::Secp256k1, &regular_secret).expect("regular public key");
    let regular_key = calc_account_id(regular_public.as_bytes());
    let parent = Arc::new(ledger_view(1, source, 1, &[]));
    let mut view = Sandbox::new(Arc::clone(&parent), ApplyFlags::NONE);
    let account_key = account_keylet(raw_account_id(source));
    let account_root = view
        .peek(account_key)
        .expect("account peek should succeed")
        .expect("account should exist");
    let mut account_object = account_root.clone_as_object();
    account_object.set_field_u32(get_field_by_symbol("sfFlags"), protocol::lsfDisableMaster);
    account_object.set_account_id(get_field_by_symbol("sfRegularKey"), regular_key);
    view.update(Arc::new(STLedgerEntry::from_stobject(
        account_object,
        *account_root.key(),
    )))
    .expect("account seed update should succeed");

    let tx = signed_set_regular_key_tx(source, 0x64, 1, 10, None);
    assert_eq!(
        apply_submit_transactor_shell(&mut view, &tx, TxType::REGULAR_KEY_SET),
        Ter::TEC_NO_ALTERNATIVE_KEY
    );

    let account_root = view
        .read(account_key)
        .expect("account read should succeed")
        .expect("account should exist");
    assert_eq!(
        account_root.get_account_id(get_field_by_symbol("sfRegularKey")),
        regular_key,
        "the ordinary tec reset must preserve the existing regular key"
    );
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfFlags")),
        protocol::lsfDisableMaster,
        "failed removal must not arm password-spent or change account flags"
    );
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfSequence")),
        2,
        "the claimed tec consumes sequence"
    );
    assert_eq!(
        account_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        999_999_990,
        "the claimed tec retains only the fee and sequence preamble"
    );
}

#[test]
fn set_regular_key_missing_account_uses_transactor_and_do_apply_error_codes() {
    let source = AccountID::from_array([0x65; 20]);
    let other = AccountID::from_array([0x66; 20]);
    let tx = signed_set_regular_key_tx(source, 0x67, 1, 10, Some(other));
    let parent = Arc::new(ledger_view(1, other, 1, &[]));

    let mut shell_view = Sandbox::new(Arc::clone(&parent), ApplyFlags::NONE);
    assert_eq!(
        apply_submit_transactor_shell(&mut shell_view, &tx, TxType::REGULAR_KEY_SET),
        Ter::TER_NO_ACCOUNT,
        "the generic transactor preamble owns the public missing-account result"
    );

    let mut dispatch_view = Sandbox::new(Arc::clone(&parent), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut dispatch_view, &tx, TxType::REGULAR_KEY_SET, None),
        Ter::TEF_INTERNAL,
        "SetRegularKey::doApply treats a vanished source as an internal ledger error"
    );
}

#[test]
fn ticket_create_preclaim_tec_never_dispatches_do_apply() {
    // Testnet ledger 20124169, tx 8F96C9A5...: the account already owns
    // 250 tickets, so rippled preserves preclaim's tecDIR_FULL and applies
    // only the generic fee/sequence state. The old path discarded that TER,
    // ran TicketCreate::doApply, and incorrectly created ticket 18895321.
    let (source, ticket_create) = signed_ticket_create_tx(0x52, 1, 1, 10);

    for (flags, should_claim_fee) in [
        (ApplyFlags::NONE, true),
        (ApplyFlags::RETRY, false),
        (ApplyFlags::FAIL_HARD, false),
    ] {
        let base = Arc::new(ledger_view_with_balance_and_owner_count(
            1,
            source,
            1,
            1_000_000_000,
            251,
            &[],
        ));
        let mut parent = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);
        let account_key = account_keylet(raw_account_id(source));
        let account_root = parent
            .peek(account_key)
            .expect("account read should succeed")
            .expect("account should exist");
        let mut account_object = account_root.clone_as_object();
        account_object.set_field_u32(get_field_by_symbol("sfTicketCount"), 250);
        parent
            .update(Arc::new(STLedgerEntry::from_stobject(
                account_object,
                *account_root.key(),
            )))
            .expect("ticket count should seed");

        let preclaim = queue_apply_preclaim_ter(&parent, &ticket_create, 2, flags);
        assert_eq!(preclaim, Ter::TEC_DIR_FULL);
        let rules = parent.rules();
        let mut attempt = FlowSandbox::new_with_flags(&mut parent, flags);
        let (result, delivered_amount) =
            apply_submit_transactor_shell_with_preclaim_and_delivered_amount(
                &mut attempt,
                &ticket_create,
                TxType::TICKET_CREATE,
                flags,
                preclaim,
            );
        assert_eq!(result, Ter::TEC_DIR_FULL);
        assert_eq!(delivered_amount, None);

        let account_root = attempt
            .read(account_key)
            .expect("account read should succeed")
            .expect("account should remain");
        assert_eq!(
            account_root.get_field_u32(get_field_by_symbol("sfTicketCount")),
            250,
            "preclaim tec must never enter TicketCreate::doApply"
        );
        assert_eq!(
            account_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
            251
        );
        assert!(
            !attempt
                .exists(protocol::ticket_keylet(raw_account_id(source), 2))
                .expect("ticket lookup should succeed")
        );

        if should_claim_fee {
            assert_eq!(
                account_root.get_field_u32(get_field_by_symbol("sfSequence")),
                2
            );
            assert_eq!(
                account_root
                    .get_field_amount(get_field_by_symbol("sfBalance"))
                    .xrp()
                    .drops(),
                999_999_990
            );
            let meta = attempt
                .to_tx_meta(ticket_create.get_transaction_id(), 2, None, &rules)
                .expect("fee-only metadata should build");
            assert_eq!(meta.get_nodes().len(), 1);
            let node = meta
                .get_nodes()
                .iter()
                .next()
                .expect("fee-only metadata should contain its AccountRoot");
            assert_eq!(node.fname(), get_field_by_symbol("sfModifiedNode"));
            assert_eq!(
                node.get_field_h256(get_field_by_symbol("sfLedgerIndex")),
                account_key.key
            );
        } else {
            assert_eq!(
                account_root.get_field_u32(get_field_by_symbol("sfSequence")),
                1
            );
            assert_eq!(
                account_root
                    .get_field_amount(get_field_by_symbol("sfBalance"))
                    .xrp()
                    .drops(),
                1_000_000_000
            );
            assert_eq!(attempt.item_count(), 0);
        }
    }
}

#[test]
fn prefunded_capped_fee_reset_charges_actual_fee_and_obeys_fail_hard() {
    let destination = AccountID::from_array([0x91; 20]);
    let sponsor = AccountID::from_array([0x92; 20]);
    let (source, payment) = signed_payment_tx(0x90, destination, 1, 25);
    let mut object = payment.clone_as_object();
    object.set_account_id(get_field_by_symbol("sfSponsor"), sponsor);
    object.set_field_u32(get_field_by_symbol("sfSponsorFlags"), 1);
    let payment = STTx::from_stobject(object);

    for (flags, claims) in [(ApplyFlags::NONE, true), (ApplyFlags::FAIL_HARD, false)] {
        let base = Arc::new(ledger_view_with_balance_and_owner_count(
            1,
            source,
            1,
            1_000_000_000,
            0,
            &[],
        ));
        let mut parent = Sandbox::new(base, ApplyFlags::NONE);
        let sponsor_account_keylet = account_keylet(raw_account_id(sponsor));
        let mut sponsor_account = STLedgerEntry::from_type_and_key(
            LedgerEntryType::AccountRoot,
            sponsor_account_keylet.key,
        );
        sponsor_account.set_account_id(get_field_by_symbol("sfAccount"), sponsor);
        sponsor_account.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        sponsor_account.set_field_u32(get_field_by_symbol("sfOwnerCount"), 0);
        sponsor_account.set_field_amount(
            get_field_by_symbol("sfBalance"),
            STAmount::new_native(1_000_000_000, false),
        );
        parent
            .insert(Arc::new(sponsor_account))
            .expect("sponsor account insert");
        let sponsorship_keylet =
            protocol::sponsorship_keylet(raw_account_id(sponsor), raw_account_id(source));
        let mut sponsorship =
            STLedgerEntry::from_type_and_key(LedgerEntryType::Sponsorship, sponsorship_keylet.key);
        sponsorship.set_field_u32(get_field_by_symbol("sfFlags"), 0);
        sponsorship.set_field_amount(
            get_field_by_symbol("sfFeeAmount"),
            STAmount::new_native(50, false),
        );
        sponsorship.set_field_amount(
            get_field_by_symbol("sfMaxFee"),
            STAmount::new_native(20, false),
        );
        parent
            .insert(Arc::new(sponsorship))
            .expect("prefund insert");

        let mut attempt = FlowSandbox::new_with_flags(&mut parent, flags);
        let outcome = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim(
            &mut attempt,
            &payment,
            TxType::PAYMENT,
            flags,
            Ter::TEC_INSUFF_FEE,
        );
        assert_eq!(outcome.result, Ter::TEC_INSUFF_FEE);

        let source_root = attempt
            .read(account_keylet(raw_account_id(source)))
            .expect("source read")
            .expect("source");
        let prefund = attempt
            .read(sponsorship_keylet)
            .expect("prefund read")
            .expect("prefund");
        if claims {
            assert_eq!(
                source_root.get_field_u32(get_field_by_symbol("sfSequence")),
                2
            );
            assert_eq!(
                prefund
                    .get_field_amount(get_field_by_symbol("sfFeeAmount"))
                    .xrp()
                    .drops(),
                30,
                "reset charges min(requested fee, MaxFee, prefunded balance)"
            );
            assert!(outcome.applied);
            assert_eq!(attempt.drops_destroyed().drops(), 20);
        } else {
            assert_eq!(
                source_root.get_field_u32(get_field_by_symbol("sfSequence")),
                1
            );
            assert_eq!(
                prefund
                    .get_field_amount(get_field_by_symbol("sfFeeAmount"))
                    .xrp()
                    .drops(),
                50
            );
            assert!(!outcome.applied);
            assert_eq!(attempt.drops_destroyed().drops(), 0);
        }
    }
}

#[test]
fn cosigned_sponsor_reset_never_spends_account_reserve() {
    let destination = AccountID::from_array([0x94; 20]);
    let sponsor = AccountID::from_array([0x95; 20]);
    let (source, payment) = signed_payment_tx(0x93, destination, 1, 25);
    let mut object = payment.clone_as_object();
    object.set_account_id(get_field_by_symbol("sfSponsor"), sponsor);
    object.set_field_u32(get_field_by_symbol("sfSponsorFlags"), 1);
    object.set_field_object(
        get_field_by_symbol("sfSponsorSignature"),
        STObject::make_inner_object(get_field_by_symbol("sfSponsorSignature")),
    );
    let payment = STTx::from_stobject(object);

    let base = Arc::new(ledger_view_with_balance_and_owner_count(
        1,
        source,
        1,
        1_000_000_000,
        0,
        &[],
    ));
    let mut parent = Sandbox::new(base, ApplyFlags::NONE);
    let reserve = parent.fees().account_reserve(0);
    let sponsor_keylet = account_keylet(raw_account_id(sponsor));
    let mut sponsor_root =
        STLedgerEntry::from_type_and_key(LedgerEntryType::AccountRoot, sponsor_keylet.key);
    sponsor_root.set_account_id(get_field_by_symbol("sfAccount"), sponsor);
    sponsor_root.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    sponsor_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 0);
    sponsor_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(reserve + 20, false),
    );
    parent
        .insert(Arc::new(sponsor_root))
        .expect("sponsor insert");

    let mut attempt = FlowSandbox::new(&mut parent);
    let outcome = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim(
        &mut attempt,
        &payment,
        TxType::PAYMENT,
        ApplyFlags::NONE,
        Ter::TEC_INSUFF_FEE,
    );
    assert_eq!(outcome.result, Ter::TEC_INSUFF_FEE);
    assert!(outcome.applied);
    assert_eq!(attempt.drops_destroyed().drops(), 20);
    assert_eq!(
        attempt
            .read(account_keylet(raw_account_id(source)))
            .expect("source read")
            .expect("source")
            .get_field_u32(get_field_by_symbol("sfSequence")),
        2
    );
    assert_eq!(
        attempt
            .read(sponsor_keylet)
            .expect("sponsor read")
            .expect("sponsor")
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        reserve as i64,
        "co-signed reset must cap the fee above reserve"
    );
}

#[test]
fn submit_direct_apply_ticket_use_clears_ticket_tracking() {
    let destination = account("F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0");
    let (source, ticket_create) = signed_ticket_create_tx(0x61, 1, 1, 10);
    let (_, ticket_payment) = signed_payment_tx_with_ticket(0x61, destination, 2, 11);
    let base = Arc::new(ledger_view_with_balance_and_owner_count(
        1,
        source,
        1,
        2_000_000,
        0,
        &[],
    ));
    let mut open_ledger =
        AppOpenLedgerView::with_parent_hash(2, 10, *base.header().hash.as_uint256());
    let mut submit_view = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);

    let create_result =
        apply_submit_tx_for_test(&mut open_ledger, &mut submit_view, ticket_create, 2);
    assert_eq!(create_result.ter, Ter::TES_SUCCESS);
    assert!(create_result.applied);

    let payment_result =
        apply_submit_tx_for_test(&mut open_ledger, &mut submit_view, ticket_payment, 2);
    assert_eq!(payment_result.ter, Ter::TES_SUCCESS);
    assert!(payment_result.applied);

    let account_root = submit_view
        .read(account_keylet(raw_account_id(source)))
        .expect("account read should succeed")
        .expect("account should exist");
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfSequence")),
        3
    );
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        0
    );
    assert!(!account_root.is_field_present(get_field_by_symbol("sfTicketCount")));
    assert_eq!(
        account_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        999_979
    );
    assert!(
        !submit_view
            .exists(protocol::ticket_keylet(raw_account_id(source), 2))
            .expect("ticket lookup should succeed")
    );
}

#[test]
fn submit_ticketed_offer_cancel_replays_canonical_ticket_preamble() {
    // Mainnet ledger 106053457, tx
    // 2CE664B532583AD41B24BB61AFC0E56382F8B1C619FF22CC5DA2A0A6F52ACD8C:
    // OfferCancel is a no-op, but its TicketSequence consumes a ticket from
    // owner-directory page 0xd2a while preserving AccountRoot.Sequence.
    let source = protocol::parse_base58_account_id("rMsXVzCug7nUsMYFGPXBTWY732fRZqxgfY")
        .expect("canonical account should parse");
    let ticket_sequence = 83_432_963;
    let owner_page = 0xd2a;
    let offer_sequence = 83_432_938;
    let retained_directory_key = Uint256::from_u64(1);
    let mut parent = ledger_view_with_balance_and_owner_count(
        106_053_456,
        source,
        83_433_003,
        365_990_743,
        68,
        &[],
    );

    let mut seed = Sandbox::new(Arc::new(parent.clone()), ApplyFlags::NONE);
    let account_keylet = account_keylet(raw_account_id(source));
    let account_root = seed
        .peek(account_keylet)
        .expect("parent account lookup should succeed")
        .expect("parent account should exist");
    let mut account_object = account_root.clone_as_object();
    account_object.set_field_u32(get_field_by_symbol("sfTicketCount"), 42);
    seed.update(Arc::new(STLedgerEntry::from_stobject(
        account_object,
        *account_root.key(),
    )))
    .expect("parent account ticket count should update");

    let ticket_keylet = protocol::ticket_keylet(raw_account_id(source), ticket_sequence);
    assert_eq!(
        ticket_keylet.key,
        Uint256::from_hex("6AC24AC49A5F4F5C9FFE6F014D2E797037C51D07B1A8B58CB6C6157FE7D672AB")
            .expect("canonical ticket key should parse")
    );
    let mut ticket = STLedgerEntry::new(ticket_keylet);
    ticket.set_account_id(get_field_by_symbol("sfAccount"), source);
    ticket.set_field_u32(get_field_by_symbol("sfTicketSequence"), ticket_sequence);
    ticket.set_field_u64(get_field_by_symbol("sfOwnerNode"), owner_page);
    seed.insert(Arc::new(ticket))
        .expect("parent ticket should insert");

    let owner_directory = protocol::owner_dir_keylet(raw_account_id(source));
    assert_eq!(
        owner_directory.key,
        Uint256::from_hex("0A824FE4651E6709A9B7D46DBA2F938C7508B286F4083F614374249359A0381D")
            .expect("canonical owner-directory root should parse")
    );
    let mut root = STLedgerEntry::new(owner_directory);
    root.set_field_h256(get_field_by_symbol("sfRootIndex"), owner_directory.key);
    root.set_account_id(get_field_by_symbol("sfOwner"), source);
    root.set_field_u64(get_field_by_symbol("sfIndexNext"), owner_page);
    root.set_field_u64(get_field_by_symbol("sfIndexPrevious"), owner_page);
    seed.insert(Arc::new(root))
        .expect("parent owner-directory root should insert");

    let owner_page_keylet = protocol::page_keylet(owner_directory, owner_page);
    assert_eq!(
        owner_page_keylet.key,
        Uint256::from_hex("BCF3866ABAC2AEA5015D5EE108F915840CD2FAF753311F2BACE72B51590AEB99")
            .expect("canonical owner-directory page should parse")
    );
    let mut page = STLedgerEntry::new(owner_page_keylet);
    page.set_field_h256(get_field_by_symbol("sfRootIndex"), owner_directory.key);
    page.set_account_id(get_field_by_symbol("sfOwner"), source);
    page.set_field_v256(
        get_field_by_symbol("sfIndexes"),
        protocol::STVector256::from_values(
            get_field_by_symbol("sfIndexes"),
            vec![ticket_keylet.key, retained_directory_key],
        ),
    );
    seed.insert(Arc::new(page))
        .expect("parent owner-directory page should insert");
    seed.apply(&mut parent)
        .expect("seeded parent state should apply");

    let tx_bytes = basics::string_utilities::str_unhex(
        "12000822000000002400000000201904F915EA201B06523F62202904F9160368400000000000000A7321ED2639E0869A74D7F5FEC402C343FABB29BF58754926DFFDA2C1338F9CFF8C85F774401A92A69C8E19C136C6EF5F39BC179173045D0847EDD73EC0713D040A2A749F644B55E94182F7785264E6892F9DE17EE97A2F0D427A33242275279F23B053260F8114DBDCCEC12FA9F832CB83A099B28B39B00CBB0C11",
    )
    .expect("canonical OfferCancel blob should decode");
    let mut serial = protocol::SerialIter::new(&tx_bytes);
    let tx = STTx::from_serial_iter(&mut serial);
    assert!(
        serial.empty(),
        "canonical OfferCancel blob should fully parse"
    );
    assert_eq!(tx.get_account_id(get_field_by_symbol("sfAccount")), source);
    assert_eq!(tx.get_seq_proxy(), SeqProxy::ticket(ticket_sequence));
    assert_eq!(
        tx.get_field_u32(get_field_by_symbol("sfOfferSequence")),
        offer_sequence
    );

    let mut replay = Sandbox::new(Arc::new(parent), ApplyFlags::NONE);
    assert_eq!(
        apply_submit_transactor_shell(&mut replay, &tx, TxType::OFFER_CANCEL),
        Ter::TES_SUCCESS
    );

    let account_root = replay
        .read(account_keylet)
        .expect("replayed account lookup should succeed")
        .expect("replayed account should exist");
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfSequence")),
        83_433_003,
        "ticketed OfferCancel must not advance AccountRoot.Sequence"
    );
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        67
    );
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfTicketCount")),
        41
    );
    assert_eq!(
        account_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        365_990_733
    );
    assert!(
        !replay
            .exists(ticket_keylet)
            .expect("consumed ticket lookup should succeed")
    );

    let page = replay
        .read(owner_page_keylet)
        .expect("owner-directory page lookup should succeed")
        .expect("the populated owner-directory page should remain");
    assert_eq!(
        page.get_field_v256(get_field_by_symbol("sfIndexes"))
            .value(),
        &[retained_directory_key]
    );
}

#[test]
fn submit_ticketed_escrow_create_consumes_ticket_preserves_sequence_and_rejects_reuse() {
    let destination = account("F1F1F1F1F1F1F1F1F1F1F1F1F1F1F1F1F1F1F1F1");
    let (source, ticket_create) = signed_ticket_create_tx(0x63, 1, 1, 10);
    let (_, ticketed_escrow) = signed_escrow_create_tx_with_ticket(0x63, destination, 2, 11);
    let (_, stale_ticketed_escrow) = signed_escrow_create_tx_with_ticket(0x63, destination, 2, 12);

    let mut base = ledger_view_with_balance_and_owner_count(1, source, 1, 2_000_000, 0, &[]);
    base.set_rules(Rules::new([protocol::feature_id("fixIncludeKeyletFields")]));
    let base = Arc::new(base);
    let mut open_ledger =
        AppOpenLedgerView::with_parent_hash(2, 10, *base.header().hash.as_uint256());
    let mut submit_view = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);

    let mut destination_root = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        account_keylet(raw_account_id(destination)).key,
    );
    destination_root.set_account_id(get_field_by_symbol("sfAccount"), destination);
    destination_root.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    destination_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(2_000_000, false),
    );
    destination_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 0);
    submit_view
        .insert(Arc::new(destination_root))
        .expect("destination account should insert");

    let ticket_create_result =
        apply_submit_tx_for_test(&mut open_ledger, &mut submit_view, ticket_create, 2);
    assert_eq!(ticket_create_result.ter, Ter::TES_SUCCESS);
    assert!(ticket_create_result.applied);
    assert!(
        submit_view
            .exists(protocol::ticket_keylet(raw_account_id(source), 2))
            .expect("ticket should exist after TicketCreate")
    );

    let escrow_result =
        apply_submit_tx_for_test(&mut open_ledger, &mut submit_view, ticketed_escrow, 2);
    assert_eq!(escrow_result.ter, Ter::TES_SUCCESS);
    assert!(escrow_result.applied);

    let source_root = submit_view
        .read(account_keylet(raw_account_id(source)))
        .expect("source account read should succeed")
        .expect("source account should exist");
    assert_eq!(
        source_root.get_field_u32(get_field_by_symbol("sfSequence")),
        3,
        "ticket use must not advance the account-root sequence"
    );
    assert_eq!(
        source_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        1
    );
    assert!(
        !source_root.is_field_present(get_field_by_symbol("sfTicketCount")),
        "consuming the only ticket must clear TicketCount"
    );
    assert!(
        !submit_view
            .exists(protocol::ticket_keylet(raw_account_id(source), 2))
            .expect("consumed ticket lookup should succeed")
    );

    let escrow = submit_view
        .read(protocol::escrow_keylet(raw_account_id(source), 2))
        .expect("ticketed escrow read should succeed")
        .expect("ticketed escrow should exist");
    assert_eq!(
        escrow.get_field_u32(get_field_by_symbol("sfSequence")),
        2,
        "fixIncludeKeyletFields must persist the TicketSequence, not Sequence = 0"
    );

    let stale_result =
        apply_submit_tx_for_test(&mut open_ledger, &mut submit_view, stale_ticketed_escrow, 2);
    assert_eq!(stale_result.ter, Ter::TEF_NO_TICKET);
    assert!(!stale_result.applied);
}

#[test]
fn submit_direct_apply_ticket_create_uses_pre_fee_balance_for_reserve() {
    let (source, ticket_create) = signed_ticket_create_tx(0x62, 1, 1, 10);
    let base = Arc::new(ledger_view_with_balance_and_owner_count(
        1,
        source,
        1,
        259,
        0,
        &[],
    ));
    let mut open_ledger =
        AppOpenLedgerView::with_parent_hash(2, 10, *base.header().hash.as_uint256());
    let mut submit_view = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);

    let result = apply_submit_tx_for_test(&mut open_ledger, &mut submit_view, ticket_create, 2);

    assert_eq!(result.ter, Ter::TES_SUCCESS);
    assert!(result.applied);

    let account_root = submit_view
        .read(account_keylet(raw_account_id(source)))
        .expect("account read should succeed")
        .expect("account should exist");
    assert_eq!(
        account_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        249
    );
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfTicketCount")),
        1
    );
    assert!(
        submit_view
            .exists(protocol::ticket_keylet(raw_account_id(source), 2))
            .expect("ticket lookup should succeed")
    );
}

#[test]
fn application_root_reads_live_account_queue_txs_from_app_owned_txq() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let account = AccountID::from_array([0x55; 20]);
    let destination = AccountID::from_array([0x77; 20]);
    let seq_proxy = SeqProxy::sequence(7);
    let consequences = TxConsequences::with_potential_spend(12, seq_proxy, 100);
    let tx = payment_tx(account, destination, 7, None, 10);

    let mut queued_account = TxQAccount::new(account);
    queued_account.add(
        seq_proxy,
        MaybeTxCore::new(
            MaybeTx::new(
                Uint256::from_u64(77),
                256,
                account,
                Some(120),
                seq_proxy,
                ApplyFlags::NONE,
                PreflightResult::new(
                    Arc::clone(&tx),
                    None::<String>,
                    Rules::new(std::iter::empty()),
                    consequences,
                    ApplyFlags::NONE,
                    "journal".to_owned(),
                    Ter::TES_SUCCESS,
                ),
            ),
            consequences,
        ),
    );

    app.registry.tx_q = SharedAppTxQ::new(AppTxQ::new_from_setup(
        TxQSetup::default(),
        None,
        QueueAcceptOwnerState::new(Uint256::from_u64(0)),
        QueueViews::new(BTreeMap::from([(account, queued_account)]), Vec::new()),
    ));

    let queue_txs = app.tx_q_account_txs(account);
    assert_eq!(queue_txs.len(), 1);
    assert_eq!(queue_txs[0].seq_proxy, seq_proxy);
    assert_eq!(queue_txs[0].fee_level, 256);
    assert_eq!(queue_txs[0].last_valid, Some(120));
    assert_eq!(queue_txs[0].account, account);
    assert_eq!(queue_txs[0].consequences.fee(), 12);
    assert_eq!(queue_txs[0].consequences.potential_spend(), 100);
    assert_eq!(
        queue_txs[0].tx.get_transaction_id(),
        tx.get_transaction_id()
    );
}

#[test]
fn application_root_accept_ledger_runs_closed_ledger_txq_maintenance() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let account = AccountID::from_array([0x33; 20]);
    let destination = AccountID::from_array([0x44; 20]);
    let seq_proxy = SeqProxy::sequence(7);
    let tx_id = Uint256::from_u64(77);
    let consequences = TxConsequences::with_potential_spend(12, seq_proxy, 100);
    let tx = payment_tx(account, destination, 7, None, 10);

    let mut queued_account = TxQAccount::new(account);
    queued_account.add(
        seq_proxy,
        MaybeTxCore::new(
            MaybeTx::new(
                tx_id,
                256,
                account,
                Some(1),
                seq_proxy,
                ApplyFlags::NONE,
                PreflightResult::new(
                    Arc::clone(&tx),
                    None::<String>,
                    Rules::new(std::iter::empty()),
                    consequences,
                    ApplyFlags::NONE,
                    "journal".to_owned(),
                    Ter::TES_SUCCESS,
                ),
            ),
            consequences,
        ),
    );

    app.registry.tx_q = SharedAppTxQ::new(AppTxQ::new_from_setup(
        TxQSetup::default(),
        None,
        QueueAcceptOwnerState::new(Uint256::from_u64(0)),
        QueueViews::new(
            BTreeMap::from([(account, queued_account)]),
            vec![FeeQueueEntry::new(
                FeeQueueKey::new(account, seq_proxy),
                QueueAdvanceCandidate {
                    fee_level: 256,
                    tx_id,
                    seq_proxy,
                },
            )],
        ),
    ));

    let next_open = app
        .accept_ledger(1, 1_234, 10)
        .expect("ledger accept should complete");

    assert_eq!(next_open, 2);
    assert!(app.tx_q_account_txs(account).is_empty());
    assert_eq!(app.tx_q_rpc_report().current_queue_size, "0");
}

#[test]
fn application_root_accept_ledger_rebuilds_next_open_with_queued_txs() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let destination = AccountID::from_array([0x99; 20]);
    let (queued_account_id, queued_tx) = signed_payment_tx(0x22, destination, 1, 12);
    let queued_seq = SeqProxy::sequence(1);
    let queued_id = queued_tx.get_transaction_id();
    let consequences = TxConsequences::with_potential_spend(12, queued_seq, 100);

    let mut parent = ledger_view(1, queued_account_id, 1, &[]);
    parent.set_accepted(1_111, ledger::LEDGER_DEFAULT_TIME_RESOLUTION, true);
    let parent = Arc::new(parent);
    app.on_closed_ledger(Arc::clone(&parent));
    let _ = app.open_ledger().modify(|view| {
        *view = AppOpenLedgerView::with_parent_hash(2, 10, *parent.header().hash.as_uint256());
        true
    });

    let mut queued_account = TxQAccount::new(queued_account_id);
    queued_account.add(
        queued_seq,
        MaybeTxCore::new(
            MaybeTx::new(
                queued_id,
                512,
                queued_account_id,
                Some(10),
                queued_seq,
                ApplyFlags::NONE,
                PreflightResult::new(
                    Arc::clone(&queued_tx),
                    None::<String>,
                    Rules::new(std::iter::empty()),
                    consequences,
                    ApplyFlags::NONE,
                    "journal".to_owned(),
                    Ter::TES_SUCCESS,
                ),
            ),
            consequences,
        ),
    );

    app.registry.tx_q = SharedAppTxQ::new(AppTxQ::new_from_setup(
        TxQSetup::default(),
        None,
        QueueAcceptOwnerState::new(Uint256::from_u64(0)),
        QueueViews::new(
            BTreeMap::from([(queued_account_id, queued_account)]),
            vec![FeeQueueEntry::new(
                FeeQueueKey::new(queued_account_id, queued_seq),
                QueueAdvanceCandidate {
                    fee_level: 512,
                    tx_id: queued_id,
                    seq_proxy: queued_seq,
                },
            )],
        ),
    ));

    let next_open = app
        .accept_ledger(2, 1_234, 10)
        .expect("ledger accept should complete");

    let rebuilt = app.open_ledger().current();
    assert_eq!(next_open, 3);
    assert_eq!(rebuilt.ledger_current_index, 3);
    assert_eq!(rebuilt.base_fee_drops, 10);
    assert_eq!(
        rebuilt.parent_hash,
        *app.closed_ledger()
            .expect("closed")
            .header()
            .hash
            .as_uint256()
    );
    assert_eq!(rebuilt.tx_ids(), vec![queued_tx.get_transaction_id()]);
    assert!(app.tx_q_account_txs(queued_account_id).is_empty());
}

#[test]
fn application_root_applies_network_ops_pending_to_open_ledger_through_app_txq_runtime() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let runtime = app.attach_default_network_ops_runtime();
    let destination = account("CCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC");
    let (source, direct) = signed_payment_tx(0x13, destination, 1, 10);
    let (_, queued) = signed_payment_tx(0x13, destination, 2, 11);

    let mut parent = ledger_view_with_balance_and_owner_count(1, source, 1, 1_000_000_000, 0, &[]);
    parent.set_accepted(1_111, ledger::LEDGER_DEFAULT_TIME_RESOLUTION, true);
    let parent = Arc::new(parent);
    app.on_closed_ledger(Arc::clone(&parent));
    let _ = app.open_ledger().modify(|view| {
        *view = AppOpenLedgerView::with_parent_hash(2, 10, *parent.header().hash.as_uint256());
        true
    });
    let mut direct_shared = Arc::new(Mutex::new(Transaction::new(Arc::clone(&direct))));
    let mut queued_shared = Arc::new(Mutex::new(Transaction::new(Arc::clone(&queued))));
    app.canonicalize_transaction(&mut direct_shared);
    app.canonicalize_transaction(&mut queued_shared);

    assert!(runtime.stage_transaction(Arc::clone(&direct_shared), false, false, false));
    assert!(runtime.stage_transaction(Arc::clone(&queued_shared), false, false, false));

    let report = app
        .apply_network_ops_pending_to_open_ledger()
        .expect("pending batch should apply to open ledger");

    assert_eq!(report.start.taken_transactions, 2);
    assert_eq!(report.entries.len(), 2);
    assert!(report.entries[0].applied, "{report:?}");
    assert_eq!(report.entries[0].result, Ter::TES_SUCCESS);
    assert!(report.entries[1].applied, "{report:?}");
    assert_eq!(report.entries[1].result, Ter::TES_SUCCESS);
    assert_eq!(
        app.open_ledger().current().tx_ids(),
        vec![direct.get_transaction_id(), queued.get_transaction_id()]
    );

    let queued_txs = app.tx_q_account_txs(source);
    assert!(queued_txs.is_empty());
    assert_eq!(app.network_ops_pending_transaction_count(), Some(0));
}

#[test]
fn application_root_submit_batch_reuses_live_ticket_and_sequence_state() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let runtime = app.attach_default_network_ops_runtime();
    let destination = account("DDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDD");
    let (source, ticket_create) = signed_ticket_create_tx(0x23, 1, 1, 10);
    let (_, ticket_payment) = signed_payment_tx_with_ticket(0x23, destination, 2, 11);
    let (_, sequence_payment) = signed_payment_tx(0x23, destination, 3, 12);

    let mut parent = ledger_view_with_balance_and_owner_count(1, source, 1, 2_000_100, 0, &[]);
    parent.set_accepted(1_111, ledger::LEDGER_DEFAULT_TIME_RESOLUTION, true);
    let parent = Arc::new(parent);
    app.on_closed_ledger(Arc::clone(&parent));
    let _ = app.open_ledger().modify(|view| {
        *view = AppOpenLedgerView::with_parent_hash(2, 10, *parent.header().hash.as_uint256());
        true
    });

    let mut ticket_create_shared =
        Arc::new(Mutex::new(Transaction::new(Arc::clone(&ticket_create))));
    let mut ticket_payment_shared =
        Arc::new(Mutex::new(Transaction::new(Arc::clone(&ticket_payment))));
    let mut sequence_payment_shared =
        Arc::new(Mutex::new(Transaction::new(Arc::clone(&sequence_payment))));
    app.canonicalize_transaction(&mut ticket_create_shared);
    app.canonicalize_transaction(&mut ticket_payment_shared);
    app.canonicalize_transaction(&mut sequence_payment_shared);

    assert!(runtime.stage_transaction(Arc::clone(&ticket_create_shared), false, false, false));
    assert!(runtime.stage_transaction(Arc::clone(&ticket_payment_shared), false, false, false));
    assert!(runtime.stage_transaction(Arc::clone(&sequence_payment_shared), false, false, false));

    let report = app
        .apply_network_ops_pending_to_open_ledger()
        .expect("pending batch should apply to open ledger");

    assert_eq!(report.start.taken_transactions, 3);
    assert_eq!(report.entries.len(), 3);
    for entry in &report.entries {
        assert!(entry.applied, "{report:?}");
        assert_eq!(entry.result, Ter::TES_SUCCESS);
    }
    assert_eq!(
        app.open_ledger().current().tx_ids(),
        vec![
            ticket_create.get_transaction_id(),
            ticket_payment.get_transaction_id(),
            sequence_payment.get_transaction_id()
        ]
    );
    assert_eq!(app.network_ops_pending_transaction_count(), Some(0));
}

#[test]
fn application_root_submit_batch_reuses_live_account_txn_id_state() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let runtime = app.attach_default_network_ops_runtime();
    let destination = account("EEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE");
    let (source, first) = signed_payment_tx(0x31, destination, 1, 10);
    let (_, second) =
        signed_payment_tx_with_account_txn_id(0x31, destination, 2, first.get_transaction_id(), 11);

    let mut parent = ledger_view_with_account_txn_id(1, source, 1, Uint256::from_u64(777), &[]);
    parent.set_accepted(1_111, ledger::LEDGER_DEFAULT_TIME_RESOLUTION, true);
    let parent = Arc::new(parent);
    app.on_closed_ledger(Arc::clone(&parent));
    let _ = app.open_ledger().modify(|view| {
        *view = AppOpenLedgerView::with_parent_hash(2, 10, *parent.header().hash.as_uint256());
        true
    });

    let mut first_shared = Arc::new(Mutex::new(Transaction::new(Arc::clone(&first))));
    let mut second_shared = Arc::new(Mutex::new(Transaction::new(Arc::clone(&second))));
    app.canonicalize_transaction(&mut first_shared);
    app.canonicalize_transaction(&mut second_shared);

    assert!(runtime.stage_transaction(Arc::clone(&first_shared), false, false, false));
    assert!(runtime.stage_transaction(Arc::clone(&second_shared), false, false, false));

    let report = app
        .apply_network_ops_pending_to_open_ledger()
        .expect("pending batch should apply to open ledger");

    assert_eq!(report.start.taken_transactions, 2);
    assert_eq!(report.entries.len(), 2);
    assert!(report.entries[0].applied, "{report:?}");
    assert_eq!(report.entries[0].result, Ter::TES_SUCCESS);
    assert!(report.entries[1].applied, "{report:?}");
    assert_eq!(report.entries[1].result, Ter::TES_SUCCESS);
    assert_eq!(
        app.open_ledger().current().tx_ids(),
        vec![first.get_transaction_id(), second.get_transaction_id()]
    );
}

#[test]
fn application_root_tracks_stop_reason_family_cleanup_and_runtime_bindings() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let network_ops = app.attach_default_network_ops_runtime();
    assert!(
        app.consensus_tx_set_submit_adapter
            .as_ref()
            .expect("consensus submit adapter")
            .is_enabled(),
        "binding NetworkOPs must enable acquired-transaction submission"
    );
    let family = Arc::new(RecordingNodeFamily::default());
    let family_runtime: Arc<dyn NodeFamilyRuntime> = family.clone();

    assert!(app.attach_node_family(family_runtime).is_none());
    let callback = app.wire_node_family_reset().expect("family reset callback");

    let server = Arc::new(RecordingComponent::default());
    assert!(app.bind_server(server.clone()).is_none());
    let shamap_store = Arc::new(RecordingComponent::default());
    assert!(app.bind_shamap_store(shamap_store.clone()).is_none());
    app.disable_grpc("disabled for parity");

    let events = Arc::new(Mutex::new(Vec::new()));
    let events_clone = Arc::clone(&events);
    app.register_stop_callback("marker", move || {
        events_clone
            .lock()
            .expect("events mutex must not be poisoned")
            .push("stopped");
    });

    assert!(app.signal_stop("testing"));
    assert!(
        !app.consensus_tx_set_submit_adapter
            .as_ref()
            .expect("consensus submit adapter")
            .is_enabled(),
        "StopTree must disable the acquired-transaction handoff"
    );
    let _ = app.attach_network_ops_runtime(network_ops);
    assert!(
        !app.consensus_tx_set_submit_adapter
            .as_ref()
            .expect("consensus submit adapter")
            .is_enabled(),
        "runtime attachment after shutdown must not re-enable the handoff"
    );
    assert!(!app.signal_stop("ignored"));
    assert!(app.is_stopping());
    assert_eq!(app.stop_reason(), Some("testing".to_owned()));
    assert_eq!(
        app.job_queue()
            .job_count(crate::job::job_types::JobType::JtAccept),
        0
    );
    assert_eq!(app.time_keeper().close_offset(), time::Duration::seconds(0));
    assert_eq!(family.resets.load(Ordering::Relaxed), 1);
    assert_eq!(
        events
            .lock()
            .expect("events mutex must not be poisoned")
            .as_slice(),
        &["stopped"]
    );
    assert_eq!(callback.name(), "node-family-reset");
    assert!(matches!(
        &app.runtime_bindings().grpc,
        GrpcRuntime::DisabledExplicit { .. }
    ));
    assert!(app.runtime_bindings().server.is_some());
    assert!(app.runtime_bindings().shamap_store.is_some());
}

#[test]
fn application_root_routes_validated_ledger_and_mode_into_attached_shamap_store_service() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let health = Arc::new(SharedSHAMapStoreHealthState::new(Arc::new(
        FixedCloseTimeProvider,
    )));
    let component = Arc::new(SHAMapStoreComponent::new(
        SHAMapStore::new(256, false, 9),
        Box::new(ServiceRuntime),
        None,
    ));
    let service = Arc::new(SHAMapStoreService::new(component.clone(), health.clone()));

    assert!(app.attach_shamap_store_service(service).is_none());
    assert!(app.set_shamap_store_operating_mode(SHAMapStoreOperatingMode::Full));
    assert!(
        app.on_validated_ledger(Arc::new(Ledger::from_ledger_seq_and_close_time(
            1_156, 100, false,
        )))
    );

    assert!(app.runtime_bindings().shamap_store.is_some());
    assert!(app.shamap_store_service().is_some());
    assert_eq!(health.operating_mode(), SHAMapStoreOperatingMode::Full);
    assert_eq!(
        app.shamap_store_operating_mode(),
        Some(SHAMapStoreOperatingMode::Full)
    );
    assert_eq!(
        health.validated_ledger_age(),
        std::time::Duration::from_secs(20)
    );
    assert_eq!(app.validated_ledger_seq(), Some(1_156));
    assert_eq!(component.snapshot().queued_ledger_seq(), Some(1_156));
}

#[test]
fn application_root_can_note_validated_ledger_without_store_hooks_for_sync() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let health = Arc::new(SharedSHAMapStoreHealthState::new(Arc::new(
        FixedCloseTimeProvider,
    )));
    let component = Arc::new(SHAMapStoreComponent::new(
        SHAMapStore::new(256, false, 9),
        Box::new(ServiceRuntime),
        None,
    ));
    let service = Arc::new(SHAMapStoreService::new(component.clone(), health));

    assert!(app.attach_shamap_store_service(service).is_none());
    app.note_validated_ledger_for_sync(Arc::new(Ledger::from_ledger_seq_and_close_time(
        1_157, 100, false,
    )));

    assert_eq!(app.validated_ledger_seq(), Some(1_157));
    assert_eq!(
        component.snapshot().queued_ledger_seq(),
        None,
        "sync hot path must not run heavier validated-ledger store hooks before publish advancement"
    );
}

#[test]
fn application_root_tracks_network_ops_operating_mode_strings() {
    let app = ApplicationRoot::new(0).expect("root shell should build");

    assert_eq!(
        app.network_ops_operating_mode(),
        NetworkOpsOperatingMode::Disconnected
    );
    assert_eq!(app.network_ops_operating_mode_string(), "disconnected");

    let previous = app.set_network_ops_operating_mode(NetworkOpsOperatingMode::Tracking);
    assert_eq!(previous, NetworkOpsOperatingMode::Disconnected);
    assert_eq!(
        app.network_ops_operating_mode(),
        NetworkOpsOperatingMode::Tracking
    );
    assert_eq!(app.network_ops_operating_mode_string(), "tracking");
}

#[test]
fn mode_promotion_rejects_a_divergent_preferred_lcl() {
    let local_hash = Uint256::from_u64(105_928_787);
    let parent_hash = Uint256::from_u64(105_928_786);

    assert!(preferred_lcl_matches_local_or_parent(
        local_hash,
        parent_hash,
        local_hash
    ));
    assert!(preferred_lcl_matches_local_or_parent(
        local_hash,
        parent_hash,
        parent_hash
    ));
    assert!(!preferred_lcl_matches_local_or_parent(
        local_hash,
        parent_hash,
        Uint256::from_u64(105_928_792)
    ));
}

#[test]
fn application_root_normalizes_connected_to_syncing_with_fresh_validated_ledger() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let now_close_time = app.time_keeper().close_time().as_seconds();
    app.note_validated_ledger_for_sync(Arc::new(Ledger::from_ledger_seq_and_close_time(
        1_200,
        now_close_time,
        false,
    )));

    let previous = app.set_network_ops_operating_mode(NetworkOpsOperatingMode::Connected);

    assert_eq!(previous, NetworkOpsOperatingMode::Disconnected);
    assert_eq!(
        app.network_ops_operating_mode(),
        NetworkOpsOperatingMode::Syncing
    );
    assert_eq!(app.network_ops_operating_mode_string(), "syncing");
}

#[test]
fn application_root_matches_rippled_admin_proposing_presentation() {
    let app = ApplicationRoot::with_options(super::ApplicationRootOptions {
        start_valid: true,
        ..super::ApplicationRootOptions::default()
    })
    .expect("root shell should build");

    // A full observing node, including every non-validator stock node, is full
    // to both public and admin RPC callers.
    assert_eq!(
        app.network_ops_operating_mode_string_for_admin(false),
        "full"
    );
    assert_eq!(
        app.network_ops_operating_mode_string_for_admin(true),
        "full"
    );

    app.network_ops_state()
        .set_consensus_mode(NetworkOpsConsensusMode::Proposing);
    // rippled only applies the proposing presentation to admin responses.
    assert_eq!(
        app.network_ops_operating_mode_string_for_admin(false),
        "full"
    );
    assert_eq!(
        app.network_ops_operating_mode_string_for_admin(true),
        "proposing"
    );

    app.network_ops_state()
        .set_consensus_mode(NetworkOpsConsensusMode::WrongLedger);
    assert_eq!(
        app.network_ops_operating_mode_string_for_admin(true),
        "full"
    );
}

#[test]
fn application_root_can_start_network_ops_in_full_mode_when_start_valid_is_set() {
    let app = ApplicationRoot::with_options(super::ApplicationRootOptions {
        start_valid: true,
        ..super::ApplicationRootOptions::default()
    })
    .expect("root shell should build");

    assert_eq!(
        app.network_ops_operating_mode(),
        NetworkOpsOperatingMode::Full
    );
    assert_eq!(app.network_ops_operating_mode_string(), "full");
}

#[test]
fn application_root_tracks_validated_and_published_ledgers_without_service() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    app.on_closed_ledger(Arc::new(Ledger::from_ledger_seq_and_close_time(
        1_154, 95, false,
    )));
    assert!(
        app.on_validated_ledger(Arc::new(Ledger::from_ledger_seq_and_close_time(
            1_156, 100, false,
        )))
    );
    app.on_published_ledger(Arc::new(Ledger::from_ledger_seq_and_close_time(
        1_155, 99, false,
    )));
    let now_close_time = app.time_keeper().close_time().as_seconds();
    app.ledger_master_state()
        .set_validated_close_time(now_close_time.saturating_sub(20));
    app.ledger_master_state()
        .set_published_close_time(now_close_time.saturating_sub(21));

    assert_eq!(app.closed_ledger_seq(), Some(1_154));
    assert_eq!(app.earliest_ledger_fetch(256), 898);
    assert_eq!(app.earliest_ledger_fetch(u32::MAX), 0);
    assert_eq!(app.validated_ledger_seq(), Some(1_156));
    assert_eq!(app.published_ledger_seq(), Some(1_155));
    assert_eq!(
        app.validated_ledger_age(),
        std::time::Duration::from_secs(20)
    );
    assert_eq!(
        app.validated_ledger()
            .expect("validated ledger should exist")
            .header()
            .seq,
        1_156
    );
}

#[test]
fn earliest_fetch_follows_canonical_lcl_not_legacy_master_slot() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let runtime = Arc::new(AppLedgerMasterRuntime::default());
    let mut legacy_closed = Ledger::from_ledger_seq_and_close_time(1_000, 90, false);
    legacy_closed.set_immutable(true);
    runtime
        .ledger_master()
        .set_closed_ledger(Arc::new(legacy_closed));
    let _ = app.attach_ledger_master_runtime(Arc::clone(&runtime));

    let mut canonical_closed = Ledger::from_ledger_seq_and_close_time(2_000, 100, false);
    canonical_closed.set_immutable(true);
    app.on_closed_ledger(Arc::new(canonical_closed));

    assert_eq!(runtime.ledger_master().earliest_fetch(256), 744);
    assert_eq!(app.earliest_ledger_fetch(256), 1_744);
    assert_eq!(
        advertised_ledger_range((1_500, 2_000), Some(1_600), app.earliest_ledger_fetch(256)),
        (1_744, 2_000)
    );
}

#[test]
fn application_root_configures_fee_voting_targets() {
    let fee_setup = crate::FeeSetup {
        reference_fee: protocol::XRPAmount::from_drops(42),
        account_reserve: protocol::XRPAmount::from_drops(1_234_567),
        owner_reserve: protocol::XRPAmount::from_drops(7_654_321),
    };
    let app = ApplicationRoot::with_options(super::ApplicationRootOptions {
        fee_setup,
        ..super::ApplicationRootOptions::default()
    })
    .expect("root shell should build");

    assert_eq!(app.fee_vote_setup, fee_setup);
}

#[test]
fn median_validation_sign_time_matches_rippled_even_odd_and_fallback_rules() {
    assert_eq!(
        super::median_validation_sign_time(vec![30, 10, 20], 3, 99),
        20
    );
    assert_eq!(
        super::median_validation_sign_time(vec![40, 10, 30, 20], 4, 99),
        25
    );
    assert_eq!(super::median_validation_sign_time(vec![10, 20], 3, 99), 99);
}

#[test]
fn needed_validations_is_zero_only_in_standalone_mode() {
    assert_eq!(super::needed_validations(true, 5), 0);
    assert_eq!(super::needed_validations(false, 5), 5);
}

#[test]
fn validation_resolver_miss_tracks_only_early_quorum_backed_observations() {
    assert!(super::should_check_tracking_on_validation_resolver_miss(
        812, 0, 3, 3
    ));
    assert!(!super::should_check_tracking_on_validation_resolver_miss(
        812, 811, 3, 3
    ));
    assert!(!super::should_check_tracking_on_validation_resolver_miss(
        812, 0, 2, 3
    ));
    assert!(!super::should_check_tracking_on_validation_resolver_miss(
        0, 0, 3, 3
    ));
}

#[test]
fn consensus_built_alternate_scan_requires_strictly_more_than_needed_validations() {
    assert!(!super::consensus_built_alternate_threshold_met(3, 3));
    assert!(super::consensus_built_alternate_threshold_met(4, 3));
}

#[test]
fn consensus_built_counts_only_its_filtered_current_validation_input() {
    let first_hash = Uint256::from_u64(81);
    let second_hash = Uint256::from_u64(82);
    let counts = super::consensus_built_current_validation_counts([
        (first_hash, 901),
        (first_hash, 901),
        (second_hash, 902),
    ]);

    assert_eq!(counts.get(&first_hash), Some(&(2, 901)));
    assert_eq!(counts.get(&second_hash), Some(&(1, 902)));
    assert!(super::consensus_built_alternate_threshold_met(
        counts[&first_hash].0,
        1
    ));
}

#[test]
fn application_root_exposes_validation_expiry_maintenance() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    app.expire_validations();
}

#[test]
fn application_root_published_ledger_emits_canonical_ledger_closed_event() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let events = Arc::new(Mutex::new(Vec::new()));
    let event_sink = Arc::clone(&events);
    app.set_subscription_publisher(move |stream, payload| {
        event_sink
            .lock()
            .expect("ledger event sink")
            .push((stream.to_owned(), payload));
    });

    let ledger = Arc::new(Ledger::from_ledger_seq_and_close_time(1_157, 101, false));
    app.on_published_ledger(Arc::clone(&ledger));

    let events = events.lock().expect("ledger event sink");
    assert_eq!(events.len(), 1);
    assert_eq!(events[0].0, "ledger");
    let protocol::JsonValue::Object(payload) = &events[0].1 else {
        panic!("ledgerClosed payload should be an object");
    };
    assert_eq!(
        payload.get("type"),
        Some(&protocol::JsonValue::String("ledgerClosed".to_owned()))
    );
    assert_eq!(
        payload.get("ledger_index"),
        Some(&protocol::JsonValue::Unsigned(1_157))
    );
    assert_eq!(
        payload.get("ledger_hash"),
        Some(&protocol::JsonValue::String(
            ledger.header().hash.to_string()
        ))
    );
    assert_eq!(
        payload.get("ledger_time"),
        Some(&protocol::JsonValue::Unsigned(101))
    );
    assert!(payload.contains_key("network_id"));
    assert!(payload.contains_key("fee_base"));
    assert!(payload.contains_key("reserve_base"));
    assert!(payload.contains_key("reserve_inc"));
    assert!(payload.contains_key("txn_count"));
}

#[test]
fn application_root_queue_relay_envelope_replaces_hostile_inbound_metadata() {
    let hostile = crate::tx_queue::transaction::TransactionRelayMetadata::new(
        1, // tsINVALID
        Some(1),
        Some(false),
    );
    let message = super::queue_relay_envelope(vec![0xFA, 0xCE], 42_424, true);

    assert_eq!(message.status, 2, "queue relay must emit tsCURRENT");
    assert_eq!(message.receive_timestamp, Some(42_424));
    assert_eq!(
        message.deferred,
        Some(true),
        "only local terQUEUED may defer"
    );
    assert_ne!(message.status, hostile.status);
    assert_ne!(message.receive_timestamp, hostile.receive_timestamp);
    assert_ne!(message.deferred, hostile.deferred);
}

#[test]
fn application_root_proposed_transaction_payload_matches_rippled_parity_fields() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let events = Arc::new(Mutex::new(Vec::new()));
    let event_sink = Arc::clone(&events);
    app.set_subscription_publisher(move |stream, payload| {
        event_sink
            .lock()
            .expect("proposed event sink")
            .push((stream.to_owned(), payload));
    });

    let _ = app.open_ledger().modify(|view| {
        view.ledger_current_index = 4_321;
        true
    });

    let transaction = Arc::new(Mutex::new(Transaction::new(payment_tx(
        account("4444444444444444444444444444444444444444"),
        account("5555555555555555555555555555555555555555"),
        1,
        None,
        10,
    ))));
    assert!(app.publish_proposed_transaction(&transaction, Ter::TES_SUCCESS));

    let events = events.lock().expect("proposed event sink");
    assert_eq!(events.len(), 1);
    assert_eq!(events[0].0, "transactions_proposed");
    let protocol::JsonValue::Object(payload) = &events[0].1 else {
        panic!("proposed transaction payload should be an object");
    };
    assert_eq!(
        payload.get("validated"),
        Some(&protocol::JsonValue::Bool(false))
    );
    assert_eq!(
        payload.get("engine_result"),
        Some(&protocol::JsonValue::String("tesSUCCESS".to_owned()))
    );
    assert_eq!(
        payload.get("status"),
        Some(&protocol::JsonValue::String("proposed".to_owned()))
    );
    assert_eq!(
        payload.get("ledger_current_index"),
        Some(&protocol::JsonValue::Unsigned(4_321))
    );
    assert_eq!(
        payload.get("hash"),
        Some(&protocol::JsonValue::String(
            transaction
                .lock()
                .expect("transaction mutex")
                .get_s_transaction()
                .get_transaction_id()
                .to_string(),
        ))
    );
    assert!(payload.contains_key("transaction"));
}

#[test]
fn application_root_inner_batch_transaction_does_not_publish_proposed_event() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let events = Arc::new(Mutex::new(Vec::new()));
    let event_sink = Arc::clone(&events);
    app.set_subscription_publisher(move |stream, payload| {
        event_sink
            .lock()
            .expect("proposed event sink")
            .push((stream.to_owned(), payload));
    });

    let mut inner = (*payment_tx(
        account("4444444444444444444444444444444444444444"),
        account("5555555555555555555555555555555555555555"),
        1,
        None,
        10,
    ))
    .clone();
    inner.set_field_u32(get_field_by_symbol("sfFlags"), INNER_BATCH_TRANSACTION_FLAG);
    let transaction = Arc::new(Mutex::new(Transaction::new(Arc::new(inner))));

    assert!(
        !app.publish_proposed_transaction(&transaction, Ter::TES_SUCCESS),
        "inner Batch transactions are not client-visible proposed events"
    );
    assert!(
        events.lock().expect("proposed event sink").is_empty(),
        "inner Batch transactions must not publish on any subscription stream"
    );
}

#[test]
fn application_root_fee_change_notification_uses_client_fee_job_and_open_ledger_fee() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let (sender, receiver) = std::sync::mpsc::channel();
    app.set_subscription_publisher(move |stream, payload| {
        sender
            .send((stream.to_owned(), payload))
            .expect("fee-change subscriber should receive one notification");
    });

    let _ = app.open_ledger().modify(|view| {
        view.base_fee_drops = 42;
        true
    });
    assert!(app.report_fee_change());

    let (stream, payload) = receiver
        .recv_timeout(std::time::Duration::from_secs(5))
        .expect("client fee-change job should publish server status");
    assert_eq!(stream, "server");
    let protocol::JsonValue::Object(payload) = payload else {
        panic!("server status should be an object");
    };
    assert_eq!(
        payload.get("type"),
        Some(&protocol::JsonValue::String("serverStatus".to_owned()))
    );
    assert_eq!(
        payload.get("base_fee"),
        Some(&protocol::JsonValue::Unsigned(42))
    );

    assert!(
        !app.report_fee_change(),
        "an unchanged ServerFeeSummary must not schedule another notification"
    );

    app.load_fee_track().set_remote_fee(512);
    assert!(
        app.report_fee_change(),
        "a changed fee summary must schedule one replacement notification"
    );
    let (stream, payload) = receiver
        .recv_timeout(std::time::Duration::from_secs(5))
        .expect("changed client fee summary should publish server status");
    assert_eq!(stream, "server");
    let protocol::JsonValue::Object(payload) = payload else {
        panic!("server status should be an object");
    };
    assert_eq!(
        payload.get("load_factor_server"),
        Some(&protocol::JsonValue::Unsigned(512))
    );
    assert!(payload.contains_key("load_factor_fee_escalation"));
    assert!(payload.contains_key("load_factor_fee_queue"));
    assert!(payload.contains_key("load_factor_fee_reference"));
}

#[test]
fn application_root_load_manager_fee_change_publishes_server_subscription_event() {
    let app = ApplicationRoot::with_options(super::ApplicationRootOptions {
        job_queue_threads: 1,
        load_manager_timing: crate::load::load_manager::LoadManagerTiming {
            tick_interval: std::time::Duration::from_millis(5),
            ..crate::load::load_manager::LoadManagerTiming::default()
        },
        ..super::ApplicationRootOptions::default()
    })
    .expect("root shell should build");
    let (sender, receiver) = std::sync::mpsc::channel();
    app.set_subscription_publisher(move |stream, payload| {
        sender
            .send((stream.to_owned(), payload))
            .expect("load manager fee-change subscriber should receive notification");
    });

    let (started_tx, started_rx) = std::sync::mpsc::channel();
    let (release_tx, release_rx) = std::sync::mpsc::channel();
    assert!(app.job_queue().add_job(
        crate::job::job_types::JobType::JtPack,
        "hold JQ slot",
        move || {
            started_tx.send(()).expect("holding job should start");
            release_rx.recv().expect("holding job should release");
        },
    ));
    started_rx
        .recv_timeout(std::time::Duration::from_secs(5))
        .expect("holding JQ job should start");
    assert!(app.job_queue().add_job(
        crate::job::job_types::JobType::JtPack,
        "queue overload",
        || {},
    ));
    assert!(
        app.job_queue().is_overloaded(),
        "JQ should drive fee raising"
    );

    // FeeTrack requires one sustained-overload observation before changing the
    // local fee; the LoadManager invocation below performs the changing one.
    use crate::load::load_manager::LoadFeeControl;
    assert!(!app.load_fee_track().raise_local_fee());
    let fee_before = app.load_fee_track().local_fee();
    app.load_manager().start();
    app.load_manager().stop();
    release_tx.send(()).expect("holding JQ job should release");
    assert!(app.load_fee_track().local_fee() > fee_before);

    let (stream, payload) = receiver
        .recv_timeout(std::time::Duration::from_secs(5))
        .expect("load-manager fee change should reach the server stream");
    assert_eq!(stream, "server");
    let protocol::JsonValue::Object(payload) = payload else {
        panic!("load-manager server event should be an object");
    };
    assert_eq!(
        payload.get("load_factor_server"),
        Some(&protocol::JsonValue::Unsigned(u64::from(
            app.load_fee_track().local_fee(),
        )))
    );
}

#[test]
fn application_root_can_own_ledger_master_runtime_local_and_held_tx_paths() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let runtime = Arc::new(AppLedgerMasterRuntime::default());
    assert!(
        app.attach_ledger_master_runtime(Arc::clone(&runtime))
            .is_none()
    );
    assert!(app.ledger_master_runtime().is_some());

    let source = account("4444444444444444444444444444444444444444");
    let current = payment_tx(
        source,
        account("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"),
        5,
        None,
        10,
    );
    let next = payment_tx(
        source,
        account("BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB"),
        6,
        None,
        11,
    );

    runtime.push_local_tx(10, Arc::clone(&current));
    assert_eq!(app.local_tx_count(), Some(1));
    assert!(
        app.update_local_tx(&ledger_view(11, source, 5, &[current.get_transaction_id()]))
            .expect("local tx update should succeed")
    );
    assert_eq!(app.local_tx_count(), Some(0));

    let next_tx = Transaction::new(Arc::clone(&next));
    assert!(app.add_held_transaction(&next_tx));
    assert_eq!(app.held_transaction_count(), Some(1));
    assert_eq!(
        app.pop_acct_transaction(&Transaction::new(Arc::clone(&current)))
            .expect("next sequence should pop")
            .get_transaction_id(),
        next.get_transaction_id()
    );
    assert_eq!(app.held_transaction_count(), Some(0));
}

#[test]
fn application_root_shares_one_persistence_runtime_with_real_dedup_state_across_calls() {
    use ledger::LedgerPersistenceRuntime;

    let app = ApplicationRoot::new(0).expect("root shell should build");
    let first = app.build_ledger_persistence_runtime();
    let second = app.build_ledger_persistence_runtime();
    assert!(
        Arc::ptr_eq(&first, &second),
        "build_ledger_persistence_runtime must return the same shared instance, \
         not a fresh throwaway one, so mark_saved/pending dedup state is real \
         across calls (matching rippled's long-lived HashRouter/PendingSaves)"
    );

    let hash = SHAMapHash::new(Uint256::from_u64(42));
    assert!(
        first.mark_saved(hash),
        "first mark_saved for a fresh hash should succeed"
    );
    assert!(
        !second.mark_saved(hash),
        "mark_saved for the same hash through a second handle must observe \
         the first call's dedup state -- proving the runtime is truly shared"
    );
}

#[test]
fn application_root_refreshes_persistence_runtime_in_place_on_storage_attach() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let before = app.build_ledger_persistence_runtime();
    app.attach_node_store(None);
    let after = app.build_ledger_persistence_runtime();
    assert!(
        !Arc::ptr_eq(&before, &after),
        "attaching storage must rebuild the shared persistence runtime so its \
         relational/node-store targets are current"
    );
}

#[test]
fn application_root_can_own_network_ops_runtime_and_bridge_held_tx_queue() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let runtime = app.attach_default_network_ops_runtime();
    assert!(app.network_ops_runtime().is_some());
    assert!(app.ledger_master_runtime().is_some());

    let source = account("5555555555555555555555555555555555555555");
    let first = payment_tx(
        source,
        account("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"),
        1,
        None,
        10,
    );
    let second = payment_tx(
        source,
        account("BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB"),
        2,
        None,
        11,
    );

    runtime
        .ledger_master_runtime()
        .add_held_sttx(Arc::clone(&second));
    runtime
        .ledger_master_runtime()
        .add_held_sttx(Arc::clone(&first));

    let syncs = Mutex::new(Vec::new());
    let outcome = app
        .apply_held_transactions_to_network_ops(SHAMapHash::new(Uint256::from_u64(101)), |sync| {
            syncs
                .lock()
                .expect("sync mutex must not be poisoned")
                .push(sync);
        })
        .expect("network ops runtime should be attached");

    assert_eq!(
        outcome,
        AppNetworkOpsApplyHeldOutcome {
            drained_count: 2,
            process_outcome: Some(NetworkOpsTransactionSetOutcome::SyncBatch { added_count: 2 }),
        }
    );
    assert_eq!(app.network_ops_pending_transaction_count(), Some(2));
    assert_eq!(app.network_ops_submit_held_count(), Some(0));
    assert_eq!(
        syncs.into_inner().expect("sync mutex must not be poisoned"),
        vec![NetworkOpsProcessSetOwnerSync {
            added_count: 2,
            had_pending_before: false,
            has_applying_after_merge: true,
        }]
    );
}

#[test]
fn application_root_accepts_a_standalone_ledger_and_promotes_live_state() {
    let mut app = ApplicationRoot::with_options(super::ApplicationRootOptions {
        standalone: true,
        ..super::ApplicationRootOptions::default()
    })
    .expect("standalone root shell should build");
    let _runtime = app.attach_default_network_ops_runtime();

    let (source, tx) = signed_payment_tx(
        0x66,
        account("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"),
        1,
        10,
    );
    let mut parent = ledger_view(1, source, 1, &[]);
    // A fee-claiming state commit destroys drops from the ledger header.
    // ../rippled/src/libxrpl/ledger/ApplyViewImpl.cpp applies that fee against
    // a real nonzero total supply; this focused fixture must do the same.
    parent.set_total_drops(1_000_000_000);
    parent.set_accepted(1_111, ledger::LEDGER_DEFAULT_TIME_RESOLUTION, true);
    let parent = Arc::new(parent);
    app.on_closed_ledger(Arc::clone(&parent));
    let _ = app.open_ledger().modify(|view| {
        *view = AppOpenLedgerView::new(2, 10);
        true
    });

    let tx_id = tx.get_transaction_id();
    let mut cached = Arc::new(Mutex::new(Transaction::new(Arc::clone(&tx))));
    app.canonicalize_transaction(&mut cached);
    let transaction = Transaction::new(Arc::clone(&tx));
    assert!(app.add_held_transaction(&transaction));
    assert_eq!(app.held_transaction_count(), Some(1));

    let next_open_index = app
        .accept_standalone_ledger()
        .expect("standalone accept should succeed");

    assert_eq!(next_open_index, 3);
    assert_eq!(app.closed_ledger_seq(), Some(2));
    assert_eq!(app.published_ledger_seq(), Some(2));
    assert_eq!(app.validated_ledger_seq(), Some(2));
    assert_eq!(app.live_current_ledger_index(), Some(3));
    assert_eq!(app.status_rpc_current_ledger_index(), Some(3));
    assert_eq!(app.network_ops_pending_transaction_count(), Some(0));
    assert_eq!(app.held_transaction_count(), Some(0));

    let cached = app
        .fetch_cached_transaction(&tx_id)
        .expect("accepted tx should remain in cache");
    let cached = cached
        .lock()
        .expect("transaction mutex must not be poisoned");
    assert_eq!(cached.get_ledger(), 2);
    assert!(cached.is_validated());
}

#[test]
fn application_root_accept_ledger_builds_from_closed_parent_view() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let parent_account = account("7777777777777777777777777777777777777777");
    let mut parent = ledger_view(1, parent_account, 1, &[]);
    parent.set_accepted(1_111, ledger::LEDGER_DEFAULT_TIME_RESOLUTION, true);
    let parent = Arc::new(parent);

    app.on_closed_ledger(Arc::clone(&parent));

    let next_open = app
        .accept_ledger(2, 1_234, 10)
        .expect("ledger accept should complete");
    let closed = app
        .closed_ledger()
        .expect("closed ledger should be recorded");

    assert_eq!(next_open, 3);
    assert_eq!(closed.header().seq, 2);
    assert_eq!(closed.header().parent_hash, parent.header().hash);
    assert!(
        closed
            .read(account_keylet(raw_account_id(parent_account)))
            .expect("closed ledger read should succeed")
            .is_some()
    );
}

#[test]
fn refresh_validator_trust_propagates_unl_block_and_clear_to_network_ops() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let lcl = Ledger::from_ledger_seq_and_close_time(1, app.current_close_time_seconds(), false);

    app.set_unl_blocked(true);
    app.refresh_validator_trust_for_consensus(&lcl)
        .expect("empty NegativeUNL read should succeed");
    assert!(!app.unl_blocked());

    let publisher_secret = SecretKey::from_bytes([0x5A; 32]);
    let publisher = derive_public_key(KeyType::Ed25519, &publisher_secret).expect("publisher key");
    assert!(
        app.validators()
            .load(None, &[], &[publisher.to_hex()], None)
    );
    app.refresh_validator_trust_for_consensus(&lcl)
        .expect("empty NegativeUNL read should succeed");
    assert!(app.validators().unl_blocked());
    assert!(app.unl_blocked());
}

#[test]
fn refresh_validator_trust_retains_negative_unl_when_parent_node_is_missing() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let validator_secret = SecretKey::from_bytes([0x6B; 32]);
    let validator =
        derive_public_key(KeyType::Ed25519, &validator_secret).expect("validator public key");
    app.validators()
        .set_negative_unl(HashSet::from([validator.clone()]));

    let root = SHAMapTreeNode::new_inner(1);
    let branch = usize::from(negative_unl_keylet().key.data()[0] >> 4);
    let missing = SHAMapHash::new(Uint256::from_array([0xB6; 32]));
    root.set_child_hash(branch, missing);
    root.update_hash();
    let lcl = Ledger::from_maps(
        LedgerHeader {
            seq: 2,
            close_time: app.current_close_time_seconds(),
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(root, SHAMapType::State, true, 2, SyncState::Immutable),
        SyncTree::new_with_type(SHAMapType::Transaction, true, 2),
    );

    assert!(matches!(
        app.refresh_validator_trust_for_consensus(&lcl),
        Err(TraversalError::MissingNode(hash)) if hash == missing
    ));
    assert_eq!(
        app.validators().get_negative_unl(),
        HashSet::from([validator]),
        "a failed parent read must not install an empty NegativeUNL"
    );
}

#[test]
fn application_root_server_okay_matches_current_gate_order() {
    let app = ApplicationRoot::with_options(super::ApplicationRootOptions {
        elb_support: true,
        ..super::ApplicationRootOptions::default()
    })
    .expect("root shell should build");

    assert_eq!(app.server_okay(), Err(crate::SERVER_OKAY_NOT_SYNCED_REASON));

    app.set_need_network_ledger(true);
    assert_eq!(
        app.server_okay(),
        Err(crate::SERVER_OKAY_NEED_NETWORK_LEDGER_REASON)
    );

    app.set_need_network_ledger(false);
    app.set_amendment_blocked(true);
    assert_eq!(
        app.server_okay(),
        Err(crate::SERVER_OKAY_AMENDMENT_BLOCKED_REASON)
    );

    app.set_amendment_blocked(false);
    app.set_unl_blocked(true);
    assert_eq!(
        app.server_okay(),
        Err(crate::SERVER_OKAY_UNL_BLOCKED_REASON)
    );

    app.set_unl_blocked(false);
    app.set_network_ops_operating_mode(NetworkOpsOperatingMode::Full);
    app.on_published_ledger(Arc::new(Ledger::from_ledger_seq_and_close_time(
        1_155, 99, false,
    )));
    let now_close_time = app.time_keeper().close_time().as_seconds();
    app.ledger_master_state()
        .set_published_close_time(now_close_time.saturating_sub(21));
    assert_eq!(app.server_okay(), Err("No published ledger"));

    app.on_validated_ledger(Arc::new(Ledger::from_ledger_seq_and_close_time(
        1_156, 100, false,
    )));
    app.ledger_master_state()
        .set_published_close_time(now_close_time.saturating_sub(21));
    app.ledger_master_state()
        .set_validated_close_time(now_close_time.saturating_sub(20));
    assert_eq!(app.server_okay(), Ok(()));

    use crate::load::load_manager::LoadFeeControl;
    assert!(!app.load_fee_track().raise_local_fee());
    assert!(app.load_fee_track().raise_local_fee());
    assert_eq!(
        app.server_okay(),
        Err(crate::SERVER_OKAY_TOO_MUCH_LOAD_REASON)
    );
}

#[test]
fn application_root_attach_shamap_store_component_builds_service_from_root_time_keeper() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let component = Arc::new(SHAMapStoreComponent::new(
        SHAMapStore::new(256, false, 9),
        Box::new(ServiceRuntime),
        None,
    ));
    let service = app.attach_shamap_store_component(component.clone());

    assert!(app.shamap_store_service().is_some());
    assert!(app.runtime_bindings().shamap_store.is_some());
    assert_eq!(service.component().fd_required(), component.fd_required());
    assert_eq!(service.validated_ledger_seq(), None);
}

#[test]
fn attached_shamap_store_service_reads_root_network_ops_mode() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let component = Arc::new(SHAMapStoreComponent::new(
        SHAMapStore::new(256, false, 9),
        Box::new(ServiceRuntime),
        None,
    ));
    let service = app.attach_shamap_store_component(component);

    assert_eq!(service.operating_mode(), SHAMapStoreOperatingMode::Other);

    app.set_network_ops_operating_mode(NetworkOpsOperatingMode::Tracking);
    assert_eq!(service.operating_mode(), SHAMapStoreOperatingMode::Other);

    app.set_network_ops_operating_mode(NetworkOpsOperatingMode::Full);
    assert_eq!(service.operating_mode(), SHAMapStoreOperatingMode::Full);
}

#[test]
fn attached_shamap_store_service_reads_root_validated_age_from_ledger_master_state() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let component = Arc::new(SHAMapStoreComponent::new(
        SHAMapStore::new(256, false, 9),
        Box::new(ServiceRuntime),
        None,
    ));
    let service = app.attach_shamap_store_component(component);

    app.on_validated_ledger(Arc::new(Ledger::from_ledger_seq_and_close_time(
        1_156, 100, false,
    )));
    let now_close_time = app.time_keeper().close_time().as_seconds();
    app.ledger_master_state()
        .set_validated_close_time(now_close_time.saturating_sub(20));

    assert_eq!(service.validated_ledger_seq(), Some(1_156));
    assert_eq!(
        service.health().validated_ledger_age(),
        app.validated_ledger_age()
    );
}

#[test]
fn consensus_outcome_defers_open_ledger_reset_to_outcome_handoff() {
    use crate::consensus::rcl_consensus::RclConsensusOpenLedgerSource;

    let app = ApplicationRoot::new(0).expect("root shell should build");
    let parent = Arc::new(Ledger::from_ledger_seq_and_close_time(10, 1_000, false));
    app.on_closed_ledger(Arc::clone(&parent));
    let _ = app.open_ledger().modify(|view| {
        *view = AppOpenLedgerView::with_parent_hash(
            11,
            parent.fees().base,
            *parent.header().hash.as_uint256(),
        );
        true
    });

    let outcome = app
        .accept_ledger_with_txns_outcome(11, 1_010, 30, true, parent.fees().base, Vec::new())
        .expect("consensus ledger acceptance should complete");

    assert_eq!(outcome.next_open_index, 12);
    assert_eq!(app.open_ledger().current().ledger_current_index, 11);

    let closed = app
        .closed_ledger()
        .expect("accepted ledger should be available");
    RclConsensusOpenLedgerSource::accept_consensus_ledger(
        app.open_ledger(),
        outcome.next_open_index,
        parent.fees().base,
        closed.header().hash.as_uint256(),
        closed.header().close_time,
        closed.header().close_time_resolution,
        &outcome.completed_transaction_ids,
        &outcome.retry_transactions,
        false,
    );

    let next_open = app.open_ledger().current();
    assert_eq!(next_open.ledger_current_index, 12);
    assert_eq!(next_open.parent_hash, *closed.header().hash.as_uint256());
}

#[test]
fn switched_ledger_consensus_child_can_replace_older_global_lcl() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let old_lcl = {
        let mut ledger = Ledger::from_ledger_seq_and_close_time(10, 1_000, false);
        ledger.set_accepted(1_000, 30, true);
        Arc::new(ledger)
    };
    let switched_parent = {
        let mut ledger = Ledger::from_ledger_seq_and_close_time(20, 1_020, false);
        ledger.set_accepted(1_020, 30, true);
        Arc::new(ledger)
    };
    app.on_closed_ledger(Arc::clone(&old_lcl));

    // Matches rippled WrongLedger/SwitchedLedger recovery: generic Consensus
    // acquired `switched_parent`, so doAccept builds its child even though the
    // global LCL still names `old_lcl`; switchLCL then installs that child
    // without a separate global-parent rejection gate.
    let outcome = app
        .accept_ledger_with_txns_outcome_from_consensus_parent(
            Arc::clone(&switched_parent),
            21,
            1_030,
            30,
            true,
            switched_parent.fees().base,
            Vec::new(),
        )
        .expect("switched parent must be accepted for build");
    app.install_consensus_child(Arc::clone(&outcome.closed));

    let closed = app.closed_ledger().expect("switched child should install");
    assert_eq!(closed.header().hash, outcome.closed.header().hash);
    assert_eq!(closed.header().seq, 21);
}

#[test]
fn consensus_child_payment_creates_account_at_child_sequence() {
    let destination = AccountID::from_array([0xA7; 20]);
    let (source, payment) = signed_payment_tx(0xA6, destination, 1, 10);
    let mut parent = ledger_view(10, source, 1, &[]);
    parent.set_total_drops(1_000_000_000);
    let parent = Arc::new(parent);
    let app = ApplicationRoot::new(0).expect("application root should build");

    let outcome = app
        .accept_ledger_with_txns_outcome_from_consensus_parent(
            Arc::clone(&parent),
            11,
            1_010,
            LEDGER_DEFAULT_TIME_RESOLUTION,
            true,
            parent.fees().base,
            vec![payment],
        )
        .expect("consensus child should build");

    let created = outcome
        .closed
        .read(account_keylet(raw_account_id(destination)))
        .expect("destination read should succeed")
        .expect("payment should create destination account");
    assert_eq!(created.get_field_u32(get_field_by_symbol("sfSequence")), 11);
}

#[test]
fn lcl_transition_gate_serializes_authoritative_promotions() {
    let app = Arc::new(ApplicationRoot::new(0).expect("root shell should build"));
    let parent = Arc::new(Ledger::from_ledger_seq_and_close_time(10, 1_000, false));
    let authoritative = Arc::new(Ledger::from_ledger_seq_and_close_time(11, 1_010, false));
    app.on_closed_ledger(Arc::clone(&parent));

    let gate = app.lcl_transition_gate().lock();
    let (done_tx, done_rx) = std::sync::mpsc::channel();
    let writer_app = Arc::clone(&app);
    let writer = std::thread::spawn(move || {
        writer_app.on_closed_ledger(authoritative);
        done_tx
            .send(())
            .expect("writer completion should be observed");
    });

    assert!(
        done_rx
            .recv_timeout(std::time::Duration::from_millis(50))
            .is_err(),
        "closed-ledger writer must wait for the active LCL transition"
    );
    drop(gate);
    done_rx
        .recv_timeout(std::time::Duration::from_secs(1))
        .expect("closed-ledger writer should proceed after transition completes");
    writer.join().expect("writer thread should not panic");
    assert_eq!(app.closed_ledger_seq(), Some(11));
}

#[test]
fn lcl_transition_gate_serializes_consensus_rebuild_sandbox_publication() {
    let app = Arc::new(ApplicationRoot::new(0).expect("root shell should build"));
    let parent = Arc::new(Ledger::from_ledger_seq_and_close_time(10, 1_000, false));

    // Legacy submit holds this gate from sequence lookup through direct
    // admission. A consensus rebase must wait rather than expose the old
    // sandbox to the signer and later overwrite the submission's sandbox.
    let gate = app.lcl_transition_gate().lock();
    let (done_tx, done_rx) = std::sync::mpsc::channel();
    let rebuild_app = Arc::clone(&app);
    let rebuild_parent = Arc::clone(&parent);
    let worker = std::thread::spawn(move || {
        rebuild_app.rebuild_open_ledger_after_consensus(rebuild_parent, &[], false);
        done_tx
            .send(())
            .expect("rebuild completion should be observed");
    });

    assert!(
        done_rx
            .recv_timeout(std::time::Duration::from_millis(50))
            .is_err(),
        "consensus rebuild must wait for the active sign-and-submit transition"
    );
    drop(gate);
    done_rx
        .recv_timeout(std::time::Duration::from_secs(1))
        .expect("rebuild should proceed after the sign-and-submit transition");
    worker.join().expect("rebuild thread should not panic");

    let open = app.open_ledger().current();
    assert_eq!(open.parent_hash, *parent.header().hash.as_uint256());
    assert_eq!(open.ledger_current_index, 11);
}

#[test]
fn validation_advance_gate_serializes_publication_planning() {
    let mut root = ApplicationRoot::new(0).expect("root shell should build");
    let _ = root.attach_ledger_master_runtime(Arc::new(AppLedgerMasterRuntime::default()));
    let app = Arc::new(root);

    let gate = app.validation_advance_gate().lock();
    let (done_tx, done_rx) = std::sync::mpsc::channel();
    let worker_app = Arc::clone(&app);
    let worker = std::thread::spawn(move || {
        worker_app.try_advance_publication();
        done_tx
            .send(())
            .expect("publication completion should be observed");
    });

    assert!(
        done_rx
            .recv_timeout(std::time::Duration::from_millis(50))
            .is_err(),
        "publication planning must wait for an in-flight validation advance"
    );
    drop(gate);
    done_rx
        .recv_timeout(std::time::Duration::from_secs(1))
        .expect("publication should proceed after validation transition ends");
    worker.join().expect("publication worker should not panic");
}

#[test]
fn live_consensus_accept_runs_consensus_built_lifecycle_before_next_round() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let runtime = Arc::new(AppLedgerMasterRuntime::default());
    let _ = app.attach_ledger_master_runtime(Arc::clone(&runtime));
    let parent = Arc::new(Ledger::from_ledger_seq_and_close_time(10, 1_000, false));
    app.on_closed_ledger(Arc::clone(&parent));
    runtime.set_building_ledger(11);

    let outcome = app
        .accept_ledger_with_txns_outcome_from_consensus_parent(
            Arc::clone(&parent),
            11,
            1_010,
            30,
            true,
            parent.fees().base,
            Vec::new(),
        )
        .expect("live consensus build should complete");
    let built = app.store_consensus_ledger(Arc::clone(&outcome.closed));

    // This is the exact handoff AppConsensus performs after the built child
    // has first been stored for status/local validation: consensusBuilt,
    // OpenLedger::accept, then switchLCL.
    let consensus_hash = Uint256::from_u64(0xCAFE);
    let recorded = app.record_consensus_built_ledger(Arc::clone(&built), consensus_hash);
    assert_eq!(recorded.header().hash, built.header().hash);
    assert_eq!(runtime.building_ledger(), None);
    let entry = runtime
        .ledger_master()
        .ledger_history()
        .consensus_entry(built.header().seq)
        .expect("built-ledger bookkeeping should be retained");
    assert_eq!(entry.built, Some(built.header().hash));
    assert_eq!(entry.built_consensus_hash, Some(consensus_hash));

    use crate::consensus::rcl_consensus::RclConsensusOpenLedgerSource;
    RclConsensusOpenLedgerSource::accept_consensus_ledger(
        app.open_ledger(),
        outcome.next_open_index,
        parent.fees().base,
        built.header().hash.as_uint256(),
        built.header().close_time,
        built.header().close_time_resolution,
        &outcome.completed_transaction_ids,
        &outcome.retry_transactions,
        false,
    );
    assert_eq!(app.open_ledger().current().ledger_current_index, 12);
    app.install_consensus_child(Arc::clone(&built));
    let closed = app.closed_ledger().expect("built LCL should install last");
    assert_eq!(closed.header().hash, built.header().hash);
}

#[test]
fn acquired_lcl_rebase_discards_transactions_already_in_parent() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let source = account("0000000000000000000000000000000000000088");
    let destination = account("0000000000000000000000000000000000000099");
    let current_tx = payment_tx(source, destination, 1, None, 10);
    let tx_id = current_tx.get_transaction_id();

    let mut acquired_lcl = Ledger::from_ledger_seq_and_close_time(11, 1_010, false);
    acquired_lcl
        .raw_tx_insert(
            tx_id,
            Arc::new(protocol::Serializer::from_bytes(
                current_tx.get_serializer().data(),
            )),
            Some(Arc::new(protocol::Serializer::new(0))),
        )
        .expect("acquired parent should contain the transaction");
    acquired_lcl.set_immutable(true);
    assert!(acquired_lcl.tx_exists(tx_id));

    let _ = app.open_ledger().modify(|view| {
        *view = AppOpenLedgerView::with_parent_hash(
            12,
            acquired_lcl.fees().base,
            *acquired_lcl.header().hash.as_uint256(),
        );
        view.push_transaction(Arc::clone(&current_tx));
        true
    });

    let acquired_lcl = Arc::new(acquired_lcl);
    app.rebuild_open_ledger_after_consensus(Arc::clone(&acquired_lcl), &[], false);

    let current = app.open_ledger().current();
    assert_eq!(
        current.parent_hash,
        *acquired_lcl.header().hash.as_uint256()
    );
    assert!(
        !current.tx_ids().contains(&tx_id),
        "an acquired parent must filter transactions it already contains"
    );
}

#[test]
fn consensus_build_discards_transaction_with_consumed_parent_sequence() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let destination = account("00000000000000000000000000000000000000AB");
    let (source, stale_tx) = signed_payment_tx(43, destination, 1, 10);
    let parent = Arc::new(ledger_view(11, source, 2, &[]));
    let stale_id = stale_tx.get_transaction_id();

    let outcome = app
        .accept_ledger_with_txns_outcome_from_consensus_parent(
            Arc::clone(&parent),
            12,
            1_012,
            LEDGER_DEFAULT_TIME_RESOLUTION,
            true,
            parent.fees().base,
            vec![stale_tx],
        )
        .expect("stale consensus transaction must not abort the candidate ledger build");

    assert!(
        !outcome.closed.tx_exists(stale_id),
        "an ancestor-consumed transaction must be rejected before consensus threading"
    );
    assert!(outcome.completed_transaction_ids.contains(&stale_id));
}

#[test]
fn consensus_build_rejects_invalid_signature_before_mutation() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let source = account("00000000000000000000000000000000000000AC");
    let destination = account("00000000000000000000000000000000000000AD");
    let unsigned_tx = payment_tx(source, destination, 1, None, 10);
    let tx_id = unsigned_tx.get_transaction_id();
    let parent = Arc::new(ledger_view(11, source, 1, &[]));

    let outcome = app
        .accept_ledger_with_txns_outcome_from_consensus_parent(
            Arc::clone(&parent),
            12,
            1_012,
            LEDGER_DEFAULT_TIME_RESOLUTION,
            true,
            parent.fees().base,
            vec![unsigned_tx],
        )
        .expect("invalid transaction must not abort the candidate ledger build");

    assert!(!outcome.closed.tx_exists(tx_id));
    assert!(outcome.completed_transaction_ids.contains(&tx_id));
}

#[test]
fn consensus_rebase_discards_transaction_with_consumed_parent_sequence() {
    let app = ApplicationRoot::new(0).expect("root shell should build");
    let destination = account("00000000000000000000000000000000000000AA");
    let (source, stale_tx) = signed_payment_tx(42, destination, 1, 10);
    let parent = Arc::new(ledger_view(11, source, 2, &[]));

    let _ = app.open_ledger().modify(|view| {
        *view = AppOpenLedgerView::with_parent_hash(
            12,
            parent.fees().base,
            *parent.header().hash.as_uint256(),
        );
        view.push_transaction(Arc::clone(&stale_tx));
        true
    });

    app.rebuild_open_ledger_after_consensus(Arc::clone(&parent), &[], false);

    assert!(
        !app.open_ledger()
            .current()
            .tx_ids()
            .contains(&stale_tx.get_transaction_id()),
        "a transaction consumed by an ancestor account sequence must not be reproposed"
    );
}

#[test]
fn consensus_built_switches_lcl_without_promoting_validated_or_published() {
    let mut app = ApplicationRoot::new(0).expect("root shell should build");
    let ledger_master_runtime = Arc::new(AppLedgerMasterRuntime::default());
    let _ = app.attach_ledger_master_runtime(Arc::clone(&ledger_master_runtime));

    let parent = Arc::new(Ledger::from_ledger_seq_and_close_time(10, 1_000, false));
    app.on_closed_ledger(Arc::clone(&parent));
    app.on_published_ledger(Arc::clone(&parent));
    assert!(app.on_validated_ledger(Arc::clone(&parent)));

    let source = account("0000000000000000000000000000000000000044");
    let destination = account("0000000000000000000000000000000000000055");
    let current_tx = payment_tx(source, destination, 1, None, 10);
    let local_tx = payment_tx(
        account("0000000000000000000000000000000000000066"),
        account("0000000000000000000000000000000000000077"),
        1,
        None,
        10,
    );
    let _ = app.open_ledger().modify(|view| {
        *view = AppOpenLedgerView::with_parent_hash(
            11,
            parent.fees().base,
            *parent.header().hash.as_uint256(),
        );
        view.push_transaction(Arc::clone(&current_tx));
        true
    });
    ledger_master_runtime.push_local_tx(10, Arc::clone(&local_tx));

    let mut built = Ledger::from_ledger_seq_and_close_time(11, 1_010, false);
    built.set_immutable(false);
    let built = Arc::new(built);
    app.on_consensus_built_ledger(Arc::clone(&built));

    assert_eq!(app.closed_ledger_seq(), Some(11));
    assert_eq!(app.published_ledger_seq(), Some(10));
    assert_eq!(app.validated_ledger_seq(), Some(10));
    app.set_network_ops_operating_mode(NetworkOpsOperatingMode::Connected);
    app.promote_operating_mode_after_accepted_ledger(built.as_ref());
    assert_ne!(
        app.network_ops_operating_mode(),
        NetworkOpsOperatingMode::Full
    );
    assert_eq!(
        ledger_master_runtime
            .ledger_master()
            .get_ledger_by_hash(built.header().hash)
            .expect("built ledger should be visible through closed-ledger lookup")
            .header()
            .seq,
        11
    );

    let current = app.open_ledger().current();
    assert_eq!(current.ledger_current_index, 12);
    assert_eq!(current.parent_hash, *built.header().hash.as_uint256());
    let tx_ids = current.tx_ids();
    assert!(
        tx_ids.is_empty(),
        "terminally invalid carried transactions must be discarded during rebase"
    );
    assert_eq!(app.status_rpc_current_ledger_index(), Some(12));
}

fn live_batch_preflight_result(sttx: STTx) -> Ter {
    let ctx = tx::PreflightContext {
        registry: crate::state::app_registry::AppPlaceholder,
        tx: AcceptLedgerPendingTransaction {
            transaction: Arc::new(Mutex::new(Transaction::new(Arc::new(sttx)))),
        },
        rules: Rules::default(),
        flags: ApplyFlags::NONE,
        parent_batch_id: None,
        journal: Arc::new(crate::state::app_registry::AppJournal::new(
            "batch-policy-test",
        )),
    };

    AcceptLedgerPendingRuntime
        .dispatch_preflight(&ctx, TxType::BATCH)
        .expect("live preflight should not return a runtime error")
        .0
}

fn batch_policy_inner(account: AccountID, sequence: u32) -> STTx {
    STTx::new(TxType::PAYMENT, move |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), account);
        tx.set_account_id(
            get_field_by_symbol("sfDestination"),
            AccountID::from_array([0xF0; 20]),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(1, false),
        );
        tx.set_field_amount(get_field_by_symbol("sfFee"), STAmount::new_native(0, false));
        tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        tx.set_field_u32(get_field_by_symbol("sfFlags"), INNER_BATCH_TRANSACTION_FLAG);
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), &[]);
    })
}

fn batch_policy_batch(outer: AccountID, inners: &[STTx]) -> STTx {
    let mut raw_transactions = STArray::new(get_field_by_symbol("sfRawTransactions"));
    for inner in inners {
        let mut raw = inner.clone_as_object();
        raw.set_fname(get_field_by_symbol("sfRawTransaction"));
        raw_transactions.push_back(raw);
    }

    STTx::new(TxType::BATCH, move |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), outer);
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            BatchTransactionFlags::ALL_OR_NOTHING.bits(),
        );
        tx.set_field_array(get_field_by_symbol("sfRawTransactions"), raw_transactions);
    })
}

#[test]
fn live_batch_preflight_rejects_sponsorship_before_signature_or_apply() {
    let outer = AccountID::from_array([0x10; 20]);
    let mut reserve_sponsored = batch_policy_batch(
        outer,
        &[
            batch_policy_inner(AccountID::from_array([0x20; 20]), 1),
            batch_policy_inner(outer, 2),
        ],
    );
    reserve_sponsored.set_field_u32(get_field_by_symbol("sfSponsorFlags"), 2);
    assert_eq!(
        live_batch_preflight_result(reserve_sponsored),
        Ter::TEM_DISABLED
    );

    let mut fee_sponsored_inner = batch_policy_inner(AccountID::from_array([0x20; 20]), 1);
    fee_sponsored_inner.set_account_id(
        get_field_by_symbol("sfSponsor"),
        AccountID::from_array([0x30; 20]),
    );
    fee_sponsored_inner.set_field_u32(get_field_by_symbol("sfSponsorFlags"), 1);
    let fee_sponsored =
        batch_policy_batch(outer, &[fee_sponsored_inner, batch_policy_inner(outer, 2)]);
    assert_eq!(
        live_batch_preflight_result(fee_sponsored),
        Ter::TEM_DISABLED
    );
}

fn open_ledger_batch_preflight_result(sttx: STTx) -> Ter {
    let outer = sttx.get_account_id(get_field_by_symbol("sfAccount"));
    let base = Arc::new(ledger_view_with_balance_and_owner_count(
        1,
        outer,
        1,
        2_000_000,
        0,
        &[],
    ));
    let mut open_ledger =
        AppOpenLedgerView::with_parent_hash(2, 10, *base.header().hash.as_uint256());
    let mut submit_view = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);
    let fee_track = crate::load::load_fee_track::SharedLoadFeeTrack::new();
    let mut runtime = AppOpenLedgerTxQApplyRuntime::new(
        &mut open_ledger,
        &mut submit_view,
        Arc::new(sttx),
        ApplyFlags::NONE,
        2,
        &fee_track,
        Arc::new(Mutex::new(std::collections::HashMap::new())),
    );

    runtime.run_preflight().ter
}

#[test]
fn direct_batch_shell_rejects_outer_preflight_before_mutating_ledger_state() {
    let outer = AccountID::from_array([0x10; 20]);
    let mut malformed = batch_policy_batch(
        outer,
        &[
            batch_policy_inner(AccountID::from_array([0x20; 20]), 1),
            batch_policy_inner(outer, 2),
        ],
    );
    malformed.set_field_u32(get_field_by_symbol("sfSponsorFlags"), 2);
    let base = Arc::new(ledger_view_with_balance_and_owner_count(
        1,
        outer,
        1,
        2_000_000,
        0,
        &[],
    ));
    let mut view = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);

    assert_eq!(
        apply_submit_transactor_shell(&mut view, &malformed, TxType::BATCH),
        Ter::TEM_INVALID_FLAG
    );

    let account_root = view
        .read(account_keylet(raw_account_id(outer)))
        .expect("account read should succeed")
        .expect("account should exist");
    assert_eq!(
        account_root.get_field_u32(get_field_by_symbol("sfSequence")),
        1
    );
    assert_eq!(
        account_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        2_000_000
    );
}

#[test]
fn batch_base_fee_uses_account_delete_owner_reserve_increment() {
    let outer = AccountID::from_array([0x10; 20]);
    let destination = AccountID::from_array([0x30; 20]);
    let account_delete = STTx::new(TxType::ACCOUNT_DELETE, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), outer);
        tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
        tx.set_field_amount(get_field_by_symbol("sfFee"), STAmount::new_native(0, false));
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(get_field_by_symbol("sfFlags"), INNER_BATCH_TRANSACTION_FLAG);
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), &[]);
    });
    let batch = batch_policy_batch(outer, &[account_delete, batch_policy_inner(outer, 2)]);
    let mut ledger = ledger_view(1, outer, 1, &[]);
    ledger.set_fees(ledger::Fees {
        base: 10,
        reserve: 10_000,
        increment: 2_000,
    });

    // ledger base + outer Batch + AccountDelete owner-reserve fee + Payment
    assert_eq!(batch_base_fee(&ledger, &batch), Ok(2_030));
}

#[test]
fn batch_base_fee_counts_outer_sponsor_multisigners() {
    // Transactor::calculateBaseFee counts sfSigners nested inside the outer
    // SponsorSignature before Batch adds its processing and inner fees.
    let outer = AccountID::from_array([0x18; 20]);
    let mut batch = batch_policy_batch(
        outer,
        &[batch_policy_inner(outer, 1), batch_policy_inner(outer, 2)],
    );
    let mut sponsor_signature =
        STObject::make_inner_object(get_field_by_symbol("sfSponsorSignature"));
    let mut signers = STArray::new(get_field_by_symbol("sfSigners"));
    signers.push_back(STObject::make_inner_object(get_field_by_symbol("sfSigner")));
    signers.push_back(STObject::make_inner_object(get_field_by_symbol("sfSigner")));
    sponsor_signature.set_field_array(get_field_by_symbol("sfSigners"), signers);
    batch.set_field_object(get_field_by_symbol("sfSponsorSignature"), sponsor_signature);
    let mut ledger = ledger_view(1, outer, 1, &[]);
    ledger.set_fees(ledger::Fees {
        base: 10,
        reserve: 10_000,
        increment: 2_000,
    });

    // 30 outer default fee (base + two sponsor multisigners), 10 Batch
    // processing fee, and 20 for the two inner transactions.
    assert_eq!(batch_base_fee(&ledger, &batch), Ok(60));
}

#[test]
fn live_batch_preclaim_authorizes_master_and_enforces_aggregate_fee_validity() {
    // ../rippled/src/libxrpl/tx/transactors/system/Batch.cpp::Batch::checkSign
    // requires the normal outer signature before BatchSigners and checkFee.
    let secret = SecretKey::from_bytes([0x51; 32]);
    let public = derive_public_key(KeyType::Secp256k1, &secret).expect("public key");
    let outer = calc_account_id(public.as_bytes());
    let ledger = ledger_view(1, outer, 1, &[]);

    let mut authorized = batch_policy_batch(
        outer,
        &[batch_policy_inner(outer, 1), batch_policy_inner(outer, 2)],
    );
    let mut batch_signers = STArray::new(get_field_by_symbol("sfBatchSigners"));
    let mut signer = STObject::make_inner_object(get_field_by_symbol("sfBatchSigner"));
    signer.set_account_id(get_field_by_symbol("sfAccount"), outer);
    signer.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    signer.set_field_vl(get_field_by_symbol("sfTxnSignature"), &[0x01]);
    batch_signers.push_back(signer);
    authorized.set_field_array(get_field_by_symbol("sfBatchSigners"), batch_signers);
    authorized.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    authorized
        .sign(&public, &secret, None)
        .expect("outer Batch signature should be valid");

    let expected_fee = ledger.fees().base * 5;
    assert_eq!(batch_base_fee(&ledger, &authorized), Ok(expected_fee));
    assert_eq!(
        queue_apply_preclaim_ter(&ledger, &authorized, ledger.header().seq, ApplyFlags::NONE,),
        Ter::TES_SUCCESS
    );

    let mut oversized = batch_policy_batch(
        outer,
        &(0..=tx::MAX_BATCH_TX_COUNT)
            .map(|sequence| batch_policy_inner(outer, sequence as u32 + 1))
            .collect::<Vec<_>>(),
    );
    oversized.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    // `STTx::sign` rejects this deliberately malformed oversized Batch before
    // preclaim. The ledger-backed signer gate still sees the master public
    // key; this assertion isolates Batch::calculateBaseFee's sentinel path.
    assert_eq!(
        batch_base_fee(&ledger, &oversized),
        Ok(INVALID_BATCH_BASE_FEE)
    );
    assert_eq!(
        queue_apply_preclaim_ter(&ledger, &oversized, ledger.header().seq, ApplyFlags::NONE,),
        Ter::TEC_INSUFF_FEE
    );
}

#[test]
fn shared_preclaim_gates_reject_before_consensus_sandbox_mutation() {
    let destination = AccountID::from_array([0xD1; 20]);

    // Permission is a pre-sign guard. The absent delegate object must stop the
    // typed tail and leave the consensus/apply sandbox unchanged.
    let (source, delegated) = signed_payment_tx(0xA1, destination, 1, 10);
    let mut delegated = (*delegated).clone();
    delegated.set_account_id(
        get_field_by_symbol("sfDelegate"),
        AccountID::from_array([0xD2; 20]),
    );
    let parent = Arc::new(ledger_view(10, source, 1, &[]));
    let view = Sandbox::new(Arc::clone(&parent), ApplyFlags::NONE);
    assert_eq!(
        queue_apply_preclaim_ter(&view, &delegated, 10, ApplyFlags::NONE),
        Ter::TER_NO_DELEGATE_PERMISSION
    );
    assert_eq!(
        view.read(account_keylet(raw_account_id(source)))
            .expect("read source")
            .expect("source exists")
            .get_field_u32(get_field_by_symbol("sfSequence")),
        1,
        "permission rejection must precede consensus mutation"
    );

    // A cryptographically valid signature from a key other than the account
    // master/regular key reaches the ledger signer authorization gate.
    let owner_secret = SecretKey::from_bytes([0xA2; 32]);
    let owner_public = derive_public_key(KeyType::Secp256k1, &owner_secret).expect("owner key");
    let owner = calc_account_id(owner_public.as_bytes());
    let signer_secret = SecretKey::from_bytes([0xA3; 32]);
    let signer_public = derive_public_key(KeyType::Secp256k1, &signer_secret).expect("signer key");
    let mut unauthorized = STTx::new(TxType::PAYMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), owner);
        tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(1, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_vl(
            get_field_by_symbol("sfSigningPubKey"),
            signer_public.as_bytes(),
        );
    });
    unauthorized
        .sign(&signer_public, &signer_secret, None)
        .expect("signature should be cryptographically valid");
    let parent = Arc::new(ledger_view(10, owner, 1, &[]));
    let view = Sandbox::new(Arc::clone(&parent), ApplyFlags::NONE);
    assert_eq!(
        queue_apply_preclaim_ter(&view, &unauthorized, 10, ApplyFlags::NONE),
        Ter::TEF_BAD_AUTH
    );
    assert_eq!(
        view.read(account_keylet(raw_account_id(owner)))
            .expect("read source")
            .expect("source exists")
            .get_field_u32(get_field_by_symbol("sfSequence")),
        1,
        "ledger signer rejection must precede consensus mutation"
    );

    // Minimum fee is enforced only by an open view, exactly as checkFee does.
    let (source, low_fee) = signed_payment_tx(0xA4, destination, 1, 9);
    let mut ledger = ledger_view(10, source, 1, &[]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 1_000_000,
        increment: 200_000,
    });
    let parent = Arc::new(ledger);
    let open = OpenView::new_open(Arc::clone(&parent), parent.rules().clone());
    assert_eq!(
        queue_apply_preclaim_ter(&open, low_fee.as_ref(), 11, ApplyFlags::NONE),
        Ter::TEL_INSUF_FEE_P
    );
    assert_eq!(
        open.read(account_keylet(raw_account_id(source)))
            .expect("read source")
            .expect("source exists")
            .get_field_u32(get_field_by_symbol("sfSequence")),
        1,
        "minimum-fee rejection must precede consensus mutation"
    );

    // The typed read-only tail is last. Its destination failure therefore
    // cannot consume the sequence or fee in the consensus sandbox.
    let (source, typed_tail) = signed_payment_tx(0xA5, destination, 1, 10);
    let mut ledger = ledger_view(10, source, 1, &[]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 1_000_001,
        increment: 200_000,
    });
    let parent = Arc::new(ledger);
    let view = Sandbox::new(Arc::clone(&parent), ApplyFlags::NONE);
    assert_eq!(
        queue_apply_preclaim_ter(&view, typed_tail.as_ref(), 10, ApplyFlags::NONE),
        Ter::TEC_NO_DST_INSUF_XRP
    );
    assert_eq!(
        view.read(account_keylet(raw_account_id(source)))
            .expect("read source")
            .expect("source exists")
            .get_field_u32(get_field_by_symbol("sfSequence")),
        1,
        "typed tail rejection must precede consensus mutation"
    );
}

#[test]
fn typed_preclaim_routes_credential_types_through_read_view_helpers() {
    let issuer = AccountID::from_array([0x7A; 20]);
    let subject = AccountID::from_array([0x7B; 20]);
    let credential_type = b"kyc";
    let create = STTx::new(TxType::CREDENTIAL_CREATE, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), issuer);
        tx.set_account_id(get_field_by_symbol("sfSubject"), subject);
        tx.set_field_vl(get_field_by_symbol("sfCredentialType"), credential_type);
    });
    let accept = STTx::new(TxType::CREDENTIAL_ACCEPT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), subject);
        tx.set_account_id(get_field_by_symbol("sfIssuer"), issuer);
        tx.set_field_vl(get_field_by_symbol("sfCredentialType"), credential_type);
    });
    let delete = STTx::new(TxType::CREDENTIAL_DELETE, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), issuer);
        tx.set_account_id(get_field_by_symbol("sfSubject"), subject);
        tx.set_field_vl(get_field_by_symbol("sfCredentialType"), credential_type);
    });
    let mut view = Sandbox::new(Arc::new(ledger_view(1, subject, 1, &[])), ApplyFlags::NONE);

    assert_eq!(
        typed_preclaim_ter(&view, &create, ApplyFlags::NONE),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        typed_preclaim_ter(&view, &accept, ApplyFlags::NONE),
        Ter::TEC_NO_ISSUER
    );
    assert_eq!(
        typed_preclaim_ter(&view, &delete, ApplyFlags::NONE),
        Ter::TEC_NO_ENTRY
    );

    let mut issuer_root = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        account_keylet(raw_account_id(issuer)).key,
    );
    issuer_root.set_account_id(get_field_by_symbol("sfAccount"), issuer);
    issuer_root.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    issuer_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(1_000_000, false),
    );
    view.insert(Arc::new(issuer_root))
        .expect("issuer account should insert");
    assert_eq!(
        typed_preclaim_ter(&view, &accept, ApplyFlags::NONE),
        Ter::TEC_NO_ENTRY
    );

    let keylet = protocol::credential_keylet(
        raw_account_id(subject),
        raw_account_id(issuer),
        credential_type,
    );
    let mut credential = STLedgerEntry::new(keylet);
    credential.set_account_id(get_field_by_symbol("sfSubject"), subject);
    credential.set_account_id(get_field_by_symbol("sfIssuer"), issuer);
    credential.set_field_vl(get_field_by_symbol("sfCredentialType"), credential_type);
    view.insert(Arc::new(credential))
        .expect("credential should insert");

    assert_eq!(
        typed_preclaim_ter(&view, &create, ApplyFlags::NONE),
        Ter::TEC_DUPLICATE
    );
    assert_eq!(
        typed_preclaim_ter(&view, &accept, ApplyFlags::NONE),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        typed_preclaim_ter(&view, &delete, ApplyFlags::NONE),
        Ter::TES_SUCCESS
    );
}

#[test]
fn typed_preclaim_routes_payment_and_paychan_create_through_read_only_helpers() {
    let source = AccountID::from_array([0x71; 20]);
    let destination = AccountID::from_array([0x72; 20]);
    let mut ledger = ledger_view(1, source, 1, &[]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 1_000_000,
        increment: 200_000,
    });
    let mut view = Sandbox::new(Arc::new(ledger), ApplyFlags::NONE);

    let payment = STTx::new(TxType::PAYMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), source);
        tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(999_999, false),
        );
    });
    let create = STTx::new(TxType::PAYCHAN_CREATE, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), source);
        tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(1_000, false),
        );
    });

    assert_eq!(
        typed_preclaim_ter(&view, &payment, ApplyFlags::NONE),
        Ter::TEC_NO_DST_INSUF_XRP
    );
    assert_eq!(
        typed_preclaim_ter(&view, &create, ApplyFlags::NONE),
        Ter::TEC_NO_DST
    );

    let mut destination_root = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        account_keylet(raw_account_id(destination)).key,
    );
    destination_root.set_account_id(get_field_by_symbol("sfAccount"), destination);
    destination_root.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    destination_root.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::new_native(1_000_000, false),
    );
    destination_root.set_field_u32(get_field_by_symbol("sfFlags"), protocol::lsfRequireDestTag);
    view.insert(Arc::new(destination_root))
        .expect("destination account should insert");

    assert_eq!(
        typed_preclaim_ter(&view, &payment, ApplyFlags::NONE),
        Ter::TEC_DST_TAG_NEEDED
    );
    assert_eq!(
        typed_preclaim_ter(&view, &create, ApplyFlags::NONE),
        Ter::TEC_DST_TAG_NEEDED
    );

    let mut tagged_create = create.clone();
    tagged_create.set_field_u32(get_field_by_symbol("sfDestinationTag"), 7);
    assert_eq!(
        typed_preclaim_ter(&view, &tagged_create, ApplyFlags::NONE),
        Ter::TES_SUCCESS
    );

    let source_after = view
        .read(account_keylet(raw_account_id(source)))
        .expect("source lookup should succeed")
        .expect("source account should remain present");
    let destination_after = view
        .read(account_keylet(raw_account_id(destination)))
        .expect("destination lookup should succeed")
        .expect("destination account should remain present");
    assert_eq!(
        source_after.get_field_u32(get_field_by_symbol("sfSequence")),
        1,
        "typed preclaim must not consume the source sequence"
    );
    assert_eq!(
        source_after
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000_000_000,
        "typed preclaim must not debit the source balance"
    );
    assert_eq!(
        destination_after.get_field_u32(get_field_by_symbol("sfFlags")),
        protocol::lsfRequireDestTag,
        "typed preclaim must not mutate destination flags"
    );
}

#[test]
fn open_ledger_batch_preflight_rejects_sponsorship_before_direct_apply() {
    let outer = AccountID::from_array([0x10; 20]);
    let mut reserve_sponsored = batch_policy_batch(
        outer,
        &[
            batch_policy_inner(AccountID::from_array([0x20; 20]), 1),
            batch_policy_inner(outer, 2),
        ],
    );
    reserve_sponsored.set_field_u32(get_field_by_symbol("sfSponsorFlags"), 2);
    assert_eq!(
        open_ledger_batch_preflight_result(reserve_sponsored),
        Ter::TEM_DISABLED
    );

    let mut fee_sponsored_inner = batch_policy_inner(AccountID::from_array([0x20; 20]), 1);
    fee_sponsored_inner.set_account_id(
        get_field_by_symbol("sfSponsor"),
        AccountID::from_array([0x30; 20]),
    );
    fee_sponsored_inner.set_field_u32(get_field_by_symbol("sfSponsorFlags"), 1);
    let fee_sponsored =
        batch_policy_batch(outer, &[fee_sponsored_inner, batch_policy_inner(outer, 2)]);
    assert_eq!(
        open_ledger_batch_preflight_result(fee_sponsored),
        Ter::TEM_DISABLED
    );
}

#[test]
fn nftoken_cancel_offer_preflight_rejects_duplicate_offer_ids() {
    let account = AccountID::from_array([0x91; 20]);
    let ledger = ledger_view(10, account, 1, &[]);
    let offer_id = Uint256::from_u64(7);
    let tx = STTx::new(TxType::NFTOKEN_CANCEL_OFFER, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), account);
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_v256(
            get_field_by_symbol("sfNFTokenOffers"),
            protocol::STVector256::from_values(
                get_field_by_symbol("sfNFTokenOffers"),
                vec![offer_id, offer_id],
            ),
        );
    });

    assert_eq!(
        transaction_preflight_ter_with_flags(&tx, &ledger.rules(), ApplyFlags::DRY_RUN),
        Ter::TEM_MALFORMED
    );
}

#[test]
fn escrow_sigbad_precedes_post_signature_credential_validation() {
    let secret = SecretKey::from_bytes([0xA7; 32]);
    let public = derive_public_key(KeyType::Secp256k1, &secret).expect("public key");
    let account = calc_account_id(public.as_bytes());
    let tx = STTx::new(TxType::ESCROW_FINISH, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), account);
        tx.set_account_id(get_field_by_symbol("sfOwner"), account);
        tx.set_field_u32(get_field_by_symbol("sfOfferSequence"), 1);
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
        tx.set_field_vl(get_field_by_symbol("sfTxnSignature"), &[1]);
        tx.set_field_v256(
            get_field_by_symbol("sfCredentialIDs"),
            protocol::STVector256::from_values(
                get_field_by_symbol("sfCredentialIDs"),
                vec![Uint256::zero()],
            ),
        );
    });
    assert_eq!(
        transaction_preflight_ter(
            &tx,
            &Rules::new([
                protocol::feature_id("Credentials"),
                protocol::feature_id("fixCleanup3_4_0"),
            ]),
        ),
        Ter::TEM_INVALID,
        "preflight2 SigBad must return before EscrowFinish::preflightSigValidated"
    );
}

#[test]
fn change_pseudo_preflight_and_fee_dispatch_are_typed_and_zero_cost() {
    let pseudo = STTx::new(TxType::AMENDMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), AccountID::zero());
        tx.set_field_amount(get_field_by_symbol("sfFee"), STAmount::new_native(0, false));
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 0);
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), &[]);
    });
    let source = AccountID::from_array([0x81; 20]);
    let mut ledger = ledger_view(10, source, 1, &[]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 1_000_000,
        increment: 2_000,
    });

    assert_eq!(
        transaction_preflight_ter(&pseudo, &ledger.rules()),
        Ter::TES_SUCCESS
    );
    assert_eq!(calculate_sttx_base_fee(&ledger, &pseudo), Ok(0));
    assert_eq!(
        queue_apply_preclaim_ter(&ledger, &pseudo, ledger.header().seq, ApplyFlags::NONE),
        Ter::TES_SUCCESS,
        "zero-account Change transactions must reach the typed preclaim tail"
    );

    let mut multisigned =
        (*payment_tx(source, AccountID::from_array([0x82; 20]), 1, None, 10)).clone();
    let mut signers = STArray::new(get_field_by_symbol("sfSigners"));
    signers.push_back(STObject::make_inner_object(get_field_by_symbol("sfSigner")));
    signers.push_back(STObject::make_inner_object(get_field_by_symbol("sfSigner")));
    multisigned.set_field_array(get_field_by_symbol("sfSigners"), signers);
    assert_eq!(calculate_sttx_base_fee(&ledger, &multisigned), Ok(30));

    let mut escrow_finish = STTx::new(TxType::ESCROW_FINISH, |_| {});
    escrow_finish.set_field_vl(get_field_by_symbol("sfFulfillment"), &[0_u8; 16]);
    assert_eq!(calculate_sttx_base_fee(&ledger, &escrow_finish), Ok(340));

    let account_delete = STTx::new(TxType::ACCOUNT_DELETE, |_| {});
    let amm_create = STTx::new(TxType::AMM_CREATE, |_| {});
    let ledger_state_fix = STTx::new(TxType::LEDGER_STATE_FIX, |_| {});
    assert_eq!(calculate_sttx_base_fee(&ledger, &account_delete), Ok(2_000));
    assert_eq!(calculate_sttx_base_fee(&ledger, &amm_create), Ok(2_000));
    assert_eq!(
        calculate_sttx_base_fee(&ledger, &ledger_state_fix),
        Ok(2_000)
    );
}

#[test]
fn closed_ledger_txq_fee_metrics_use_specialized_and_default_base_fees() {
    let pseudo = Arc::new(STTx::new(TxType::AMENDMENT, |tx| {
        tx.set_field_amount(get_field_by_symbol("sfFee"), STAmount::new_native(0, false));
    }));
    let amm_create = Arc::new(STTx::new(TxType::AMM_CREATE, |tx| {
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(2_000, false),
        );
    }));

    let mut tx_tree = MutableTree::new(88);
    for (index, tx) in [Arc::clone(&pseudo), Arc::clone(&amm_create)]
        .into_iter()
        .enumerate()
    {
        let mut meta = STObject::new(get_field_by_symbol("sfTransactionMetaData"));
        meta.set_field_u8(get_field_by_symbol("sfTransactionResult"), 0);
        meta.set_field_u32(
            get_field_by_symbol("sfTransactionIndex"),
            u32::try_from(index).expect("test transaction index fits in u32"),
        );
        meta.set_field_array(
            get_field_by_symbol("sfAffectedNodes"),
            STArray::new(get_field_by_symbol("sfAffectedNodes")),
        );
        let mut payload = protocol::Serializer::new(0);
        payload.add_vl(tx.get_serializer().data());
        payload.add_vl(meta.get_serializer().data());
        tx_tree
            .add_item(
                SHAMapNodeType::TransactionMd,
                SHAMapItem::new(tx.get_transaction_id(), payload.data().to_vec()),
            )
            .expect("closed-ledger transaction metadata should insert");
    }

    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq: 88,
            ..LedgerHeader::default()
        },
        SyncTree::new_with_type(SHAMapType::State, false, 88),
        SyncTree::from_root_with_type(
            tx_tree.root(),
            SHAMapType::Transaction,
            false,
            88,
            SyncState::Immutable,
        ),
    );
    ledger.set_fees(Fees {
        base: 10,
        reserve: 1_000_000,
        increment: 2_000,
    });

    let root = ApplicationRoot::new(0).expect("application root should build");
    let mut levels = root.validated_fee_levels_for_closed_ledger(&ledger);
    levels.sort_unstable();

    // Parity: ../rippled/src/xrpld/app/misc/detail/TxQ.cpp::getFeeLevelPaid and TxQ::FeeMetrics::update.
    assert_eq!(levels, vec![tx::TXQ_BASE_LEVEL, tx::TXQ_BASE_LEVEL]);
}

#[test]
fn txq_multitxn_preclaim_uses_an_uncommitted_adjusted_sandbox() {
    // ../rippled/src/xrpld/app/misc/detail/TxQ.cpp::TxQ::apply creates a
    // MultiTxn ApplyView/OpenView, adjusts balance and sequence, and preclaims
    // against it. The adjustment is admission-only and must not commit.
    let destination = AccountID::from_array([0x92; 20]);
    let (source, tx) = signed_payment_tx(0x92, destination, 2, 10);
    let base = Arc::new(ledger_view(10, source, 1, &[]));
    let mut open_ledger =
        AppOpenLedgerView::with_parent_hash(11, 10, *base.header().hash.as_uint256());
    let mut submit_view = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);
    let fee_track = crate::load::load_fee_track::SharedLoadFeeTrack::new();
    let mut runtime = AppOpenLedgerTxQApplyRuntime::new(
        &mut open_ledger,
        &mut submit_view,
        tx,
        ApplyFlags::NONE,
        11,
        &fee_track,
        Arc::new(Mutex::new(std::collections::HashMap::new())),
    );

    assert!(runtime.prepare_multitxn(QueueApplyViewAdjustment {
        potential_total_spend_drops: 10,
        adjusted_balance_drops: 999_990,
        applied_sequence_value: 2,
    }));
    let preclaim = runtime.run_preclaim(QueueApplyPreclaimViewSource::MultiTxnOpenView);
    assert_eq!(preclaim.ter, Ter::TES_SUCCESS);
    drop(runtime);

    let account = submit_view
        .read(account_keylet(raw_account_id(source)))
        .expect("source read")
        .expect("source exists");
    assert_eq!(account.get_field_u32(get_field_by_symbol("sfSequence")), 1);
    assert_eq!(
        account
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000_000_000,
        "MultiTxn preclaim must not commit its temporary balance adjustment"
    );
}

#[test]
fn txq_direct_apply_uses_canonical_shared_preclaim_instead_of_caller_ter() {
    // ../rippled/src/libxrpl/tx/applySteps.cpp::invokePreclaim (lines 177-200): shared admission runs before any application mutation.
    let destination = AccountID::from_array([0x91; 20]);
    let (source, tx) = signed_payment_tx(0x91, destination, 2, 10);
    let base = Arc::new(ledger_view(10, source, 1, &[]));
    let mut open_ledger =
        AppOpenLedgerView::with_parent_hash(11, 10, *base.header().hash.as_uint256());
    let mut submit_view = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);
    let fee_track = crate::load::load_fee_track::SharedLoadFeeTrack::new();
    let mut runtime = AppOpenLedgerTxQApplyRuntime::new(
        &mut open_ledger,
        &mut submit_view,
        tx,
        ApplyFlags::NONE,
        11,
        &fee_track,
        Arc::new(Mutex::new(std::collections::HashMap::new())),
    );

    let result = runtime.direct_apply();
    assert_eq!(
        result,
        ApplyResult::new(Ter::TER_PRE_SEQ, false, false),
        "the runtime must derive the shared preclaim from the live view"
    );
    drop(runtime);
    assert!(
        open_ledger.tx_ids().is_empty(),
        "a rejected canonical preclaim must not be recorded by direct apply"
    );
    assert_eq!(
        submit_view
            .read(account_keylet(raw_account_id(source)))
            .expect("source read")
            .expect("source exists")
            .get_field_u32(get_field_by_symbol("sfSequence")),
        1,
    );
}

#[test]
fn txq_try_clear_applies_predecessors_repreclaims_current_and_reports_cleanup() {
    // Parity: TxQ.cpp:517-609 and 1181-1205. A high-fee sequence transaction
    // clears its queued predecessor in a child sandbox, then applies itself
    // against that advanced state and reports the queue entries to erase.
    let destination = AccountID::from_array([0xD1; 20]);
    let (source, predecessor) = signed_payment_tx(0x75, destination, 1, 100);
    let (_, current) = signed_payment_tx(0x75, destination, 2, 100);
    let base = Arc::new(ledger_view(10, source, 1, &[]));
    let mut open_ledger =
        AppOpenLedgerView::with_parent_hash(11, 10, *base.header().hash.as_uint256());
    // Clear-ahead only runs above the expected open-ledger load threshold.
    open_ledger.push_transaction(payment_tx(source, destination, 90, None, 10));
    open_ledger.push_transaction(payment_tx(source, destination, 91, None, 10));
    let mut submit_view = Sandbox::new(Arc::clone(&base), ApplyFlags::NONE);
    let fee_track = crate::load::load_fee_track::SharedLoadFeeTrack::new();
    let predecessor_details = TxDetails {
        fee_level: tx::TXQ_BASE_LEVEL * 10,
        last_valid: None,
        consequences: TxConsequences::new(100, SeqProxy::sequence(1)),
        account: source,
        seq_proxy: SeqProxy::sequence(1),
        tx: Arc::clone(&predecessor),
        retries_remaining: tx::MAYBE_TX_RETRIES_ALLOWED,
        flags: ApplyFlags::FAIL_HARD,
        preflight_result: Ter::TES_SUCCESS,
        last_result: None,
    };
    let mut runtime = AppOpenLedgerTxQApplyRuntime::new_with_clear_ahead(
        &mut open_ledger,
        &mut submit_view,
        Arc::clone(&current),
        ApplyFlags::NONE,
        11,
        &fee_track,
        Arc::new(Mutex::new(std::collections::HashMap::new())),
        0,
        vec![predecessor_details],
        QueueFeeMetricsSnapshot {
            txns_expected: 1,
            escalation_multiplier: tx::TXQ_BASE_LEVEL,
        },
    );

    assert_eq!(
        runtime.run_try_clear(),
        ApplyResult::new(Ter::TES_SUCCESS, true, false)
    );
    let (attempts, removed) = runtime.take_clear_ahead_effects();
    assert_eq!(
        attempts,
        vec![(
            SeqProxy::sequence(1),
            ApplyResult::new(Ter::TES_SUCCESS, true, false)
        )]
    );
    assert_eq!(removed, vec![SeqProxy::sequence(1)]);
    assert!(
        open_ledger
            .tx_ids()
            .contains(&predecessor.get_transaction_id())
    );
    assert!(open_ledger.tx_ids().contains(&current.get_transaction_id()));
}

#[test]
fn typed_preclaim_dispatcher_covers_all_82_routed_quaxar_types() {
    use TypedPreclaimRoute::{
        AppAuditedNoop, AppReadViewHelper, BatchSpecialPreclaim, BridgeDomainAuditedNoop,
        BridgeDomainReadViewHelper, ChangeReadViewHelper, ConfidentialMptReadViewHelper,
        DexReadViewHelper, LoanReadViewHelper, NfTokenReadViewHelper, SponsorshipReadViewHelper,
        SystemReadViewHelper, TokenAuditedNoop, TokenReadViewHelper, VaultReadViewHelper,
    };

    // Keep this table in protocol dispatch order. It is deliberately explicit:
    // adding a routed TxType requires an audited helper/no-op/fail-closed route.
    let cases = [
        (TxType::PAYMENT, AppReadViewHelper),
        (TxType::ESCROW_CREATE, AppReadViewHelper),
        (TxType::ESCROW_FINISH, AppReadViewHelper),
        (TxType::ACCOUNT_SET, AppReadViewHelper),
        (TxType::ESCROW_CANCEL, AppReadViewHelper),
        (TxType::REGULAR_KEY_SET, AppAuditedNoop),
        (TxType::OFFER_CREATE, DexReadViewHelper),
        (TxType::OFFER_CANCEL, DexReadViewHelper),
        (TxType::TICKET_CREATE, SystemReadViewHelper),
        (TxType::SIGNER_LIST_SET, AppAuditedNoop),
        (TxType::PAYCHAN_CREATE, AppReadViewHelper),
        (TxType::PAYCHAN_FUND, AppAuditedNoop),
        (TxType::PAYCHAN_CLAIM, AppReadViewHelper),
        (TxType::CHECK_CREATE, AppReadViewHelper),
        (TxType::CHECK_CASH, AppReadViewHelper),
        (TxType::CHECK_CANCEL, AppReadViewHelper),
        (TxType::DEPOSIT_PREAUTH, AppReadViewHelper),
        (TxType::TRUST_SET, TokenReadViewHelper),
        (TxType::ACCOUNT_DELETE, AppReadViewHelper),
        (TxType::NFTOKEN_MINT, NfTokenReadViewHelper),
        (TxType::NFTOKEN_BURN, NfTokenReadViewHelper),
        (TxType::NFTOKEN_CREATE_OFFER, NfTokenReadViewHelper),
        (TxType::NFTOKEN_CANCEL_OFFER, NfTokenReadViewHelper),
        (TxType::NFTOKEN_ACCEPT_OFFER, NfTokenReadViewHelper),
        (TxType::CLAWBACK, TokenReadViewHelper),
        (TxType::AMM_CLAWBACK, DexReadViewHelper),
        (TxType::AMM_CREATE, DexReadViewHelper),
        (TxType::AMM_DEPOSIT, DexReadViewHelper),
        (TxType::AMM_WITHDRAW, DexReadViewHelper),
        (TxType::AMM_VOTE, DexReadViewHelper),
        (TxType::AMM_BID, DexReadViewHelper),
        (TxType::AMM_DELETE, DexReadViewHelper),
        (TxType::XCHAIN_CREATE_CLAIM_ID, BridgeDomainReadViewHelper),
        (TxType::XCHAIN_COMMIT, BridgeDomainReadViewHelper),
        (TxType::XCHAIN_CLAIM, BridgeDomainReadViewHelper),
        (
            TxType::XCHAIN_ACCOUNT_CREATE_COMMIT,
            BridgeDomainReadViewHelper,
        ),
        (
            TxType::XCHAIN_ADD_CLAIM_ATTESTATION,
            BridgeDomainReadViewHelper,
        ),
        (
            TxType::XCHAIN_ADD_ACCOUNT_CREATE_ATTESTATION,
            BridgeDomainReadViewHelper,
        ),
        (TxType::XCHAIN_MODIFY_BRIDGE, BridgeDomainReadViewHelper),
        (TxType::XCHAIN_CREATE_BRIDGE, BridgeDomainReadViewHelper),
        (TxType::DID_SET, BridgeDomainAuditedNoop),
        (TxType::DID_DELETE, BridgeDomainAuditedNoop),
        (TxType::ORACLE_SET, BridgeDomainReadViewHelper),
        (TxType::ORACLE_DELETE, BridgeDomainReadViewHelper),
        (TxType::LEDGER_STATE_FIX, SystemReadViewHelper),
        (TxType::MPTOKEN_ISSUANCE_CREATE, TokenAuditedNoop),
        (TxType::MPTOKEN_ISSUANCE_DESTROY, TokenReadViewHelper),
        (TxType::MPTOKEN_ISSUANCE_SET, TokenReadViewHelper),
        (TxType::MPTOKEN_AUTHORIZE, TokenReadViewHelper),
        (TxType::CREDENTIAL_CREATE, BridgeDomainReadViewHelper),
        (TxType::CREDENTIAL_ACCEPT, BridgeDomainReadViewHelper),
        (TxType::CREDENTIAL_DELETE, BridgeDomainReadViewHelper),
        (TxType::NFTOKEN_MODIFY, NfTokenReadViewHelper),
        (TxType::PERMISSIONED_DOMAIN_SET, BridgeDomainReadViewHelper),
        (
            TxType::PERMISSIONED_DOMAIN_DELETE,
            BridgeDomainReadViewHelper,
        ),
        (TxType::DELEGATE_SET, AppReadViewHelper),
        (TxType::VAULT_CREATE, VaultReadViewHelper),
        (TxType::VAULT_SET, VaultReadViewHelper),
        (TxType::VAULT_DELETE, VaultReadViewHelper),
        (TxType::VAULT_DEPOSIT, VaultReadViewHelper),
        (TxType::VAULT_WITHDRAW, VaultReadViewHelper),
        (TxType::VAULT_CLAWBACK, VaultReadViewHelper),
        (TxType::BATCH, BatchSpecialPreclaim),
        (TxType::LOAN_BROKER_SET, LoanReadViewHelper),
        (TxType::LOAN_BROKER_DELETE, LoanReadViewHelper),
        (TxType::LOAN_BROKER_COVER_DEPOSIT, LoanReadViewHelper),
        (TxType::LOAN_BROKER_COVER_WITHDRAW, LoanReadViewHelper),
        (TxType::LOAN_BROKER_COVER_CLAWBACK, LoanReadViewHelper),
        (TxType::LOAN_SET, LoanReadViewHelper),
        (TxType::LOAN_DELETE, LoanReadViewHelper),
        (TxType::LOAN_MANAGE, LoanReadViewHelper),
        (TxType::LOAN_PAY, LoanReadViewHelper),
        (
            TxType::CONFIDENTIAL_MPT_CONVERT,
            ConfidentialMptReadViewHelper,
        ),
        (
            TxType::CONFIDENTIAL_MPT_MERGE_INBOX,
            ConfidentialMptReadViewHelper,
        ),
        (
            TxType::CONFIDENTIAL_MPT_CONVERT_BACK,
            ConfidentialMptReadViewHelper,
        ),
        (TxType::CONFIDENTIAL_MPT_SEND, ConfidentialMptReadViewHelper),
        (
            TxType::CONFIDENTIAL_MPT_CLAWBACK,
            ConfidentialMptReadViewHelper,
        ),
        (TxType::SPONSORSHIP_TRANSFER, SponsorshipReadViewHelper),
        (TxType::SPONSORSHIP_SET, SponsorshipReadViewHelper),
        (TxType::AMENDMENT, ChangeReadViewHelper),
        (TxType::FEE, ChangeReadViewHelper),
        (TxType::UNL_MODIFY, ChangeReadViewHelper),
    ];

    let routed = cases
        .iter()
        .map(|(txn_type, _)| *txn_type)
        .collect::<std::collections::BTreeSet<_>>();
    let registered = protocol::dispatchable_tx_types().collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        cases.len(),
        routed.len(),
        "each routed type must appear exactly once"
    );
    assert_eq!(
        routed, registered,
        "typed preclaim coverage must exactly equal the protocol dispatch catalog"
    );

    for (txn_type, expected_route) in cases {
        assert_eq!(
            typed_preclaim_route(txn_type),
            expected_route,
            "{}",
            txn_type.format_name().unwrap_or("unknown")
        );
    }

    // Every listed route is an upstream transaction type with a concrete
    // helper, audited inherited no-op, or Batch special preclaim. Unknown
    // numeric transaction types remain fail-closed through the default arm.
    let view = Ledger::from_ledger_seq_and_close_time(1, 0, false);
    for txn_type in [
        TxType::AMM_DEPOSIT,
        TxType::AMM_WITHDRAW,
        TxType::TICKET_CREATE,
        TxType::LEDGER_STATE_FIX,
    ] {
        let tx = STTx::new(txn_type, |_| {});
        let expected = match txn_type {
            TxType::AMM_DEPOSIT | TxType::AMM_WITHDRAW => {
                tx::run_dex_read_view_preclaim_with_flags(&view, &tx, txn_type, ApplyFlags::NONE)
                    .expect("AMM typed helper must own its route")
            }
            TxType::TICKET_CREATE => tx::run_ticket_create_read_view_preclaim(&view, &tx, txn_type)
                .expect("TicketCreate typed helper must own its route"),
            TxType::LEDGER_STATE_FIX => {
                tx::run_ledger_state_fix_read_view_preclaim(&view, &tx, txn_type)
                    .expect("LedgerStateFix typed helper must own its route")
            }
            _ => unreachable!(),
        };
        assert_eq!(
            typed_preclaim_ter(&view, &tx, ApplyFlags::NONE),
            expected,
            "{txn_type:?} must use its immutable ReadView helper"
        );
    }

    let amendment = STTx::new(TxType::AMENDMENT, |_| {});
    let malformed_fee = STTx::new(TxType::FEE, |_| {});
    assert_eq!(
        typed_preclaim_ter(&view, &amendment, ApplyFlags::NONE),
        Ter::TES_SUCCESS,
        "Amendment must use its explicit Change-family immutable preclaim"
    );
    assert_eq!(
        typed_preclaim_ter(&view, &malformed_fee, ApplyFlags::NONE),
        Ter::TEM_MALFORMED,
        "Fee must use its exact Change-family field-shape preclaim"
    );
}

#[test]
fn apply_dispatcher_covers_exact_protocol_catalog_and_rejects_non_dispatchable_types() {
    let registered = protocol::dispatchable_tx_types().collect::<std::collections::BTreeSet<_>>();
    let classified = (0..=u16::MAX)
        .map(TxType::from_u16)
        .filter(|txn_type| apply_dispatch_route(*txn_type).is_some())
        .collect::<std::collections::BTreeSet<_>>();

    assert_eq!(classified, registered);
    for txn_type in [
        TxType::NICKNAME_SET,
        TxType::CONTRACT,
        TxType::SPINAL_TAP,
        TxType::HOOK_SET,
        TxType::from_u16(999),
    ] {
        assert_eq!(apply_dispatch_route(txn_type), None);
    }
}

#[test]
fn batch_inner_transactions_retain_parent_context_and_metadata() {
    // ../rippled/src/libxrpl/tx/transactors/system/Batch.cpp::Batch::preflight
    // (lines 203-382) sends each inner through `preflight(..., parentBatchId,
    // stx, TapBatch, ...)`; ../rippled/src/libxrpl/tx/apply.cpp::applyBatchTransactions
    // (lines 162-191) applies that same parent and TapBatch context in its own
    // per-transaction view. ../rippled/src/test/app/Batch_test.cpp::validateInnerTxn
    // (lines 116-122) then requires `sfParentBatchID` in every inner metadata.
    let secret = SecretKey::from_bytes([0xB1; 32]);
    let public = derive_public_key(KeyType::Secp256k1, &secret).expect("batch outer public key");
    let source = calc_account_id(public.as_bytes());
    let mut parent = ledger_view(10, source, 1, &[]);
    parent.set_rules(Rules::new([protocol::feature_batch()]));
    let parent = Arc::new(parent);
    let app = ApplicationRoot::new(0).expect("application root should build");

    let inners = [batch_policy_inner(source, 2), batch_policy_inner(source, 3)];
    let mut batch = batch_policy_batch(source, &inners);
    let batch_fee = batch_base_fee(parent.as_ref(), &batch).expect("valid Batch fee");
    batch.set_field_amount(
        get_field_by_symbol("sfFee"),
        STAmount::new_native(batch_fee, false),
    );
    batch.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    batch
        .sign(&public, &secret, None)
        .expect("outer Batch signature should be valid");
    let batch = Arc::new(batch);
    let batch_id = batch.get_transaction_id();

    let outcome = app
        .accept_ledger_with_txns_outcome_from_consensus_parent(
            Arc::clone(&parent),
            11,
            1_010,
            LEDGER_DEFAULT_TIME_RESOLUTION,
            true,
            parent.fees().base,
            vec![Arc::clone(&batch)],
        )
        .expect("Batch candidate construction should complete");
    let transactions = outcome
        .closed
        .tx_snapshot()
        .expect("closed Batch ledger metadata should decode");

    assert_eq!(
        transactions.len(),
        3,
        "the outer Batch and both successfully applied inner transactions must be recorded"
    );
    let source_key = account_keylet(raw_account_id(source)).key;
    let destination = AccountID::from_array([0xF0; 20]);
    let destination_key = account_keylet(raw_account_id(destination)).key;
    let (_, outer_metadata) = transactions
        .iter()
        .find(|(transaction, _)| transaction.get_transaction_id() == batch_id)
        .expect("outer Batch metadata must be recorded");
    assert_eq!(outer_metadata.get_result_ter(), Ter::TES_SUCCESS);
    assert_eq!(outer_metadata.get_index(), 0);
    assert_eq!(
        outer_metadata.get_nodes().len(),
        1,
        "outer Batch metadata must exclude every inner-only state delta"
    );
    assert_eq!(
        outer_metadata
            .get_nodes()
            .iter()
            .next()
            .expect("outer Batch has one affected node")
            .get_field_h256(get_field_by_symbol("sfLedgerIndex")),
        source_key,
        "outer Batch metadata contains only its own source preamble mutation"
    );

    for (position, inner) in inners.iter().enumerate() {
        let (_, metadata) = transactions
            .iter()
            .find(|(transaction, _)| transaction.get_transaction_id() == inner.get_transaction_id())
            .expect("applied inner transaction must retain its own ledger metadata");
        assert_eq!(metadata.get_result_ter(), Ter::TES_SUCCESS);
        assert_eq!(metadata.get_index(), position as u32 + 1);
        assert_eq!(
            metadata
                .get_as_object()
                .get_field_h256(get_field_by_symbol("sfParentBatchID")),
            batch_id,
            "inner metadata must retain the canonical parent Batch id"
        );
        assert_eq!(
            metadata.get_nodes().len(),
            2,
            "each inner Payment metadata must be isolated to source and destination"
        );
        let source_node = metadata
            .get_nodes()
            .iter()
            .find(|node| node.get_field_h256(get_field_by_symbol("sfLedgerIndex")) == source_key)
            .expect("inner Payment metadata must modify its source AccountRoot");
        assert_eq!(source_node.fname(), get_field_by_symbol("sfModifiedNode"));
        let destination_node = metadata
            .get_nodes()
            .iter()
            .find(|node| {
                node.get_field_h256(get_field_by_symbol("sfLedgerIndex")) == destination_key
            })
            .expect("inner Payment metadata must contain its destination AccountRoot");
        assert_eq!(
            destination_node.fname(),
            if position == 0 {
                get_field_by_symbol("sfCreatedNode")
            } else {
                get_field_by_symbol("sfModifiedNode")
            },
            "the first inner creates the destination and the second modifies it"
        );
    }

    let last_inner_id = inners[1].get_transaction_id();
    for account in [source, destination] {
        let sle = outcome
            .closed
            .read(account_keylet(raw_account_id(account)))
            .expect("final Batch account read must succeed")
            .expect("final Batch account must exist");
        assert_eq!(
            sle.get_field_h256(get_field_by_symbol("sfPreviousTxnID")),
            last_inner_id,
            "the last inner transaction, not the outer Batch, must own the final SLE thread"
        );
        assert_eq!(
            sle.get_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq")),
            11
        );
    }
}

#[test]
fn open_batch_applies_only_the_outer_transaction() {
    let secret = SecretKey::from_bytes([0xB5; 32]);
    let public = derive_public_key(KeyType::Secp256k1, &secret).expect("batch outer public key");
    let source = calc_account_id(public.as_bytes());
    let mut parent = ledger_view(10, source, 1, &[]);
    parent.set_rules(Rules::new([protocol::feature_batch()]));
    let parent = Arc::new(parent);
    let inners = [batch_policy_inner(source, 2), batch_policy_inner(source, 3)];
    let mut batch = batch_policy_batch(source, &inners);
    let fee = batch_base_fee(parent.as_ref(), &batch).expect("valid Batch fee");
    batch.set_field_amount(
        get_field_by_symbol("sfFee"),
        STAmount::new_native(fee, false),
    );
    batch.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    batch
        .sign(&public, &secret, None)
        .expect("outer Batch signature should be valid");
    let batch = Arc::new(batch);

    let open_base = Arc::new(OpenView::new_open(
        Arc::clone(&parent),
        parent.rules().clone(),
    ));
    let mut open = Sandbox::new(open_base, ApplyFlags::NONE);
    let preflight = transaction_preflight_ter(&batch, &open.rules());
    assert_eq!(preflight, Ter::TES_SUCCESS);
    let preclaim = queue_apply_preclaim_ter(&open, &batch, open.seq(), ApplyFlags::NONE);
    let outcome = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim(
        &mut open,
        &batch,
        TxType::BATCH,
        ApplyFlags::NONE,
        preclaim,
    );
    assert!(outcome.applied);
    assert!(outcome.prebuilt_outer_metadata.is_none());
    assert!(outcome.applied_batch_inner_transactions.is_empty());

    let source_after = open
        .read(account_keylet(raw_account_id(source)))
        .expect("read open Batch source")
        .expect("open Batch source exists");
    assert_eq!(
        source_after.get_field_u32(get_field_by_symbol("sfSequence")),
        2,
        "xrpl::apply applies only the outer Batch in the open ledger"
    );
    assert_eq!(
        source_after.get_field_h256(get_field_by_symbol("sfPreviousTxnID")),
        Uint256::zero(),
        "normal open-ledger Batch application must not install closed-ledger threads"
    );

    let mut inventory = AppOpenLedgerView::new(open.seq(), parent.fees().base);
    record_applied_open_transactions(
        &mut inventory,
        Arc::clone(&batch),
        &outcome.applied_batch_inner_transactions,
    );
    assert_eq!(
        inventory.tx_ids(),
        vec![batch.get_transaction_id()],
        "only the outer Batch enters rippled's proposed open transaction set"
    );
}

#[test]
fn dry_run_batch_simulates_only_the_outer_transaction() {
    let secret = SecretKey::from_bytes([0xB6; 32]);
    let public = derive_public_key(KeyType::Secp256k1, &secret).expect("batch outer public key");
    let source = calc_account_id(public.as_bytes());
    let mut parent = ledger_view(10, source, 1, &[]);
    parent.set_rules(Rules::new([protocol::feature_batch()]));
    let parent = Arc::new(parent);
    let inners = [batch_policy_inner(source, 2), batch_policy_inner(source, 3)];
    let mut batch = batch_policy_batch(source, &inners);
    let fee = batch_base_fee(parent.as_ref(), &batch).expect("valid Batch fee");
    batch.set_field_amount(
        get_field_by_symbol("sfFee"),
        STAmount::new_native(fee, false),
    );
    batch.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    batch
        .sign(&public, &secret, None)
        .expect("outer Batch signature should be valid");

    let open_base = Arc::new(OpenView::new_open(
        Arc::clone(&parent),
        parent.rules().clone(),
    ));
    let mut open = Sandbox::new(open_base, ApplyFlags::DRY_RUN);
    let mut simulation = FlowSandbox::new_with_flags(&mut open, ApplyFlags::DRY_RUN);
    let preflight =
        transaction_preflight_ter_with_flags(&batch, &simulation.rules(), ApplyFlags::DRY_RUN);
    let preclaim =
        queue_apply_preclaim_ter(&simulation, &batch, simulation.seq(), ApplyFlags::DRY_RUN);
    let outcome = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim(
        &mut simulation,
        &batch,
        TxType::BATCH,
        ApplyFlags::DRY_RUN,
        if preflight == Ter::TES_SUCCESS {
            preclaim
        } else {
            preflight
        },
    );
    assert_eq!(outcome.result, Ter::TES_SUCCESS);
    assert!(
        !outcome.applied,
        "TapDryRun must never publish an applied result"
    );
    assert!(outcome.applied_batch_inner_transactions.is_empty());
    assert_eq!(
        simulation
            .read(account_keylet(raw_account_id(source)))
            .expect("read simulated source")
            .expect("simulated source exists")
            .get_field_u32(get_field_by_symbol("sfSequence")),
        2,
        "TxQ::apply(TapDryRun) simulates only the outer Batch"
    );
    drop(simulation);
    assert_eq!(
        open.read(account_keylet(raw_account_id(source)))
            .expect("read real open source")
            .expect("real open source exists")
            .get_field_u32(get_field_by_symbol("sfSequence")),
        1,
        "dropping the dry-run sandbox must leave the real open ledger unchanged"
    );
}

#[test]
fn batch_all_or_nothing_discards_inner_metadata_with_the_whole_batch_view() {
    // ../rippled/src/libxrpl/tx/apply.cpp::applyBatchTransactions applies each
    // eligible inner view to `wholeBatchView`, but returns false for
    // tfAllOrNothing on the first non-tes result and never applies that whole
    // view. ../rippled/src/libxrpl/tx/applySteps.cpp::preclaim is the required
    // shared admission step for the second, pre-sequence inner transaction.
    let secret = SecretKey::from_bytes([0xB4; 32]);
    let public = derive_public_key(KeyType::Secp256k1, &secret).expect("batch outer public key");
    let source = calc_account_id(public.as_bytes());
    let mut parent = ledger_view(10, source, 1, &[]);
    parent.set_rules(Rules::new([protocol::feature_batch()]));
    let parent = Arc::new(parent);
    let app = ApplicationRoot::new(0).expect("application root should build");

    // The outer Batch consumes sequence 1. The first inner can apply at 2,
    // while the second is a shared-preclaim terPRE_SEQ at 5, forcing the
    // all-or-nothing whole-batch view to be discarded.
    let inners = [batch_policy_inner(source, 2), batch_policy_inner(source, 5)];
    let mut batch = batch_policy_batch(source, &inners);
    let batch_fee = batch_base_fee(parent.as_ref(), &batch).expect("valid Batch fee");
    batch.set_field_amount(
        get_field_by_symbol("sfFee"),
        STAmount::new_native(batch_fee, false),
    );
    batch.set_field_vl(get_field_by_symbol("sfSigningPubKey"), public.as_bytes());
    batch
        .sign(&public, &secret, None)
        .expect("outer Batch signature should be valid");

    let outcome = app
        .accept_ledger_with_txns_outcome_from_consensus_parent(
            Arc::clone(&parent),
            11,
            1_010,
            LEDGER_DEFAULT_TIME_RESOLUTION,
            true,
            parent.fees().base,
            vec![Arc::new(batch)],
        )
        .expect("Batch candidate construction should complete");
    let transactions = outcome
        .closed
        .tx_snapshot()
        .expect("closed Batch ledger metadata should decode");

    assert_eq!(
        transactions.len(),
        1,
        "only the outer Batch may remain when its all-or-nothing inner view is discarded"
    );
    for inner in inners {
        assert!(
            transactions
                .iter()
                .all(|(transaction, _)| transaction.get_transaction_id()
                    != inner.get_transaction_id()),
            "discarded inner Batch transactions must not receive metadata entries"
        );
    }
    let source_after = outcome
        .closed
        .read(account_keylet(raw_account_id(source)))
        .expect("read source after all-or-nothing Batch")
        .expect("outer Batch source remains");
    assert_eq!(
        source_after.get_field_u32(get_field_by_symbol("sfSequence")),
        2,
        "only the outer Batch sequence increment may survive inner rollback"
    );
    let inner_destination = AccountID::from_array([0xF0; 20]);
    assert!(
        outcome
            .closed
            .read(account_keylet(raw_account_id(inner_destination)))
            .expect("read discarded inner destination")
            .is_none(),
        "the first inner Payment's created destination must roll back with wholeBatchView"
    );
}

#[test]
fn standalone_accept_rejects_bad_signature_and_pre_sequence_before_mutation() {
    // ../rippled/src/libxrpl/tx/apply.cpp::apply (lines 132-158) always
    // executes preflight and preclaim before doApply. The standalone close
    // path must retain that ordering so rejected input produces neither a
    // transaction record nor an account-sequence mutation.
    let mut app = ApplicationRoot::with_options(super::ApplicationRootOptions {
        standalone: true,
        ..super::ApplicationRootOptions::default()
    })
    .expect("standalone root shell should build");
    let _runtime = app.attach_default_network_ops_runtime();

    let destination = AccountID::from_array([0xD2; 20]);
    let (source, signed_first) = signed_payment_tx(0xB2, destination, 1, 10);
    let mut bad_signature = (*signed_first).clone();
    bad_signature.set_field_vl(get_field_by_symbol("sfTxnSignature"), &[0x00]);
    let bad_signature = Arc::new(bad_signature);
    let (_, pre_sequence) = signed_payment_tx(0xB2, destination, 2, 10);
    let parent = Arc::new(ledger_view(10, source, 1, &[]));
    app.on_closed_ledger(Arc::clone(&parent));
    let _ = app.open_ledger().modify(|view| {
        *view = AppOpenLedgerView::with_parent_hash(
            11,
            parent.fees().base,
            *parent.header().hash.as_uint256(),
        );
        view.push_transaction(Arc::clone(&bad_signature));
        view.push_transaction(Arc::clone(&pre_sequence));
        true
    });

    app.accept_standalone_ledger()
        .expect("invalid standalone input must not abort ledger closure");
    let closed = app.closed_ledger().expect("standalone child should close");
    assert!(
        !closed.tx_exists(bad_signature.get_transaction_id()),
        "an invalid signature must be rejected before standalone metadata insertion"
    );
    assert!(
        !closed.tx_exists(pre_sequence.get_transaction_id()),
        "a sequence that is only valid after rejected input must remain a preclaim failure"
    );
    let source_after = closed
        .read(account_keylet(raw_account_id(source)))
        .expect("source lookup should succeed")
        .expect("source account should remain present");
    assert_eq!(
        source_after.get_field_u32(get_field_by_symbol("sfSequence")),
        1,
        "rejected standalone transactions must not consume the source sequence"
    );
}

#[test]
fn publication_gap_routes_to_owned_ledger_replayer() {
    // ../rippled/src/xrpld/app/ledger/detail/LedgerMaster.cpp::findNewLedgersToPublish
    // (lines 1307-1335) narrows a contiguous publication gap and calls
    // `app_.getLedgerReplayer().replay(InboundLedger::Reason::GENERIC, ...)`.
    // It must supplement, not replace, normal contiguous publication/history
    // acquisition; the bounded replayer owns its own duplicate and shutdown
    // safety checks in ../rippled/src/xrpld/app/ledger/detail/LedgerReplayer.cpp::replay.
    let mut app = ApplicationRoot::new(0).expect("application root should build");
    let runtime = Arc::new(AppLedgerMasterRuntime::default());
    let _ = app.attach_ledger_master_runtime(Arc::clone(&runtime));

    let source = AccountID::from_array([0xB3; 20]);
    let mut first = ledger_view(1, source, 1, &[]);
    first.set_immutable(true);
    let first = Arc::new(first);
    let mut second = Ledger::from_previous(&first, 900);
    second.set_immutable(true);
    let second = Arc::new(second);
    let mut third = Ledger::from_previous(&second, 930);
    third.set_immutable(true);
    let third = Arc::new(third);

    runtime.ledger_master().set_pub_ledger(Arc::clone(&first));
    runtime
        .ledger_master()
        .set_valid_ledger(Arc::clone(&third), None, None)
        .expect("validated child should establish the publication gap");
    let report = runtime.plan_advance_publication();
    assert_eq!(
        report.missing.map(|missing| (missing.seq, missing.hash)),
        Some((2, *second.header().hash.as_uint256())),
        "the gap must be narrowed to the first missing contiguous ledger"
    );

    app.try_advance_publication();
    assert_eq!(
        app.registry
            .ledger_replayer
            .lock()
            .expect("ledger replayer lock")
            .tasks_len(),
        1,
        "a bounded replay task must be scheduled for the narrowed history gap"
    );
}

#[test]
fn authoritative_publication_clears_network_startup_latch() {
    let mut app = ApplicationRoot::new(0).expect("application root should build");
    let runtime = Arc::new(AppLedgerMasterRuntime::default());
    let _ = app.attach_ledger_master_runtime(Arc::clone(&runtime));
    let mut ledger = Ledger::from_ledger_seq_and_close_time(1, 1_000, false);
    ledger.set_immutable(true);
    let ledger = Arc::new(ledger);
    runtime
        .ledger_master()
        .set_valid_ledger(Arc::clone(&ledger), None, None)
        .expect("validated ledger should be accepted");
    app.set_need_network_ledger(true);

    app.try_advance_publication();

    assert!(runtime.ledger_master().published_ledger().is_some());
    assert!(
        !app.need_network_ledger(),
        "the publication commit itself must clear the startup latch"
    );
}

#[test]
fn consensus_status_event_uses_lost_sync_for_a_wrong_lcl() {
    assert_eq!(consensus_status_event(2, true), 2); // neACCEPTED_LEDGER
    assert_eq!(consensus_status_event(1, false), 4); // neLOST_SYNC
}

#[test]
fn live_base_fee_dispatch_includes_multisign_and_specialized_owners() {
    let source = AccountID::from_array([0xC1; 20]);
    let mut ledger = ledger_view(10, source, 1, &[]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 1_000_000,
        increment: 200_000,
    });
    let mut multisigned = STTx::new(TxType::ESCROW_FINISH, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), source);
        tx.set_field_vl(get_field_by_symbol("sfFulfillment"), &[0; 16]);
    });
    let mut signers = STArray::new(get_field_by_symbol("sfSigners"));
    signers.push_back(STObject::make_inner_object(get_field_by_symbol("sfSigner")));
    signers.push_back(STObject::make_inner_object(get_field_by_symbol("sfSigner")));
    multisigned.set_field_array(get_field_by_symbol("sfSigners"), signers);

    assert_eq!(calculate_default_sttx_base_fee(&ledger, &multisigned), 30);
    assert_eq!(
        calculate_sttx_base_fee(&ledger, &multisigned),
        Ok(30 + ledger.fees().base * 33),
        "EscrowFinish extends the generic two-multisigner fee"
    );

    for txn_type in [
        TxType::ACCOUNT_DELETE,
        TxType::AMM_CREATE,
        TxType::LEDGER_STATE_FIX,
    ] {
        let tx = STTx::new(txn_type, |tx| {
            tx.set_account_id(get_field_by_symbol("sfAccount"), source);
        });
        assert_eq!(
            calculate_sttx_base_fee(&ledger, &tx),
            Ok(ledger.fees().increment),
            "{txn_type:?} replaces the generic fee with the owner reserve"
        );
    }

    let mut loan_set = STTx::new(TxType::LOAN_SET, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), source);
    });
    let mut counterparty =
        STObject::make_inner_object(get_field_by_symbol("sfCounterpartySignature"));
    counterparty.set_field_vl(get_field_by_symbol("sfTxnSignature"), &[1]);
    loan_set.set_field_object(get_field_by_symbol("sfCounterpartySignature"), counterparty);
    assert_eq!(
        calculate_sttx_base_fee(&ledger, &loan_set),
        Ok(ledger.fees().base * 2),
        "LoanSet charges the generic fee plus its counterparty signature"
    );
}

#[test]
fn loan_set_counterparty_preflight_requires_signature_and_known_signing_key() {
    // ../rippled/src/libxrpl/tx/transactors/lending/LoanSet.cpp::LoanSet::preflight: rejects a missing CounterpartySignature before numeric validation.
    let account = AccountID::from_array([0xC4; 20]);
    let rules = Rules::default();
    let missing_signature = STTx::new(TxType::LOAN_SET, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), account);
    });
    assert_eq!(
        loan_set_counterparty_preflight_ter(&missing_signature, &rules),
        Ter::TEM_BAD_SIGNER
    );

    let mut unknown_key = STTx::new(TxType::LOAN_SET, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), account);
    });
    let mut counterparty_signature =
        STObject::make_inner_object(get_field_by_symbol("sfCounterpartySignature"));
    counterparty_signature.set_field_vl(get_field_by_symbol("sfSigningPubKey"), &[0xFF]);
    unknown_key.set_field_object(
        get_field_by_symbol("sfCounterpartySignature"),
        counterparty_signature,
    );
    assert_eq!(
        loan_set_counterparty_preflight_ter(&unknown_key, &rules),
        Ter::TEM_BAD_SIGNATURE
    );
}

#[test]
fn zero_account_change_transactions_reach_their_typed_preclaim_tail() {
    let source = AccountID::from_array([0xC2; 20]);
    let ledger = ledger_view(10, source, 1, &[]);
    let zero = AccountID::from_array([0; 20]);
    let mut amendment = STTx::new(TxType::AMENDMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), zero);
        tx.set_field_amount(get_field_by_symbol("sfFee"), STAmount::new_native(0, false));
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 0);
    });
    amendment.set_field_h256(get_field_by_symbol("sfAmendment"), Uint256::from_u64(1));

    assert_eq!(
        transaction_preflight_ter(&amendment, &ledger.rules()),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        queue_apply_preclaim_ter(&ledger, &amendment, ledger.header().seq, ApplyFlags::NONE),
        Ter::TES_SUCCESS
    );

    let fee = STTx::new(TxType::FEE, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), zero);
        tx.set_field_amount(get_field_by_symbol("sfFee"), STAmount::new_native(0, false));
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 0);
    });
    assert_eq!(
        transaction_preflight_ter(&fee, &ledger.rules()),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        queue_apply_preclaim_ter(&ledger, &fee, ledger.header().seq, ApplyFlags::NONE),
        Ter::TEM_MALFORMED,
        "the zero account must reach Change::preclaim rather than generic rejection"
    );

    let unl_modify = STTx::new(TxType::UNL_MODIFY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), zero);
        tx.set_field_amount(get_field_by_symbol("sfFee"), STAmount::new_native(0, false));
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 0);
    });
    assert_eq!(
        transaction_preflight_ter(&unl_modify, &ledger.rules()),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        queue_apply_preclaim_ter(&ledger, &unl_modify, ledger.header().seq, ApplyFlags::NONE),
        Ter::TES_SUCCESS,
        "UNLModify must use its Change-family typed preclaim tail"
    );
}

#[test]
fn modern_network_change_preflight_is_preserved_through_apply() {
    let source = AccountID::from_array([0xC5; 20]);
    let ledger = Arc::new(ledger_view(10, source, 1, &[]));
    let zero = AccountID::from_array([0; 20]);
    let mut amendment = STTx::new(TxType::AMENDMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), zero);
        tx.set_field_amount(get_field_by_symbol("sfFee"), STAmount::new_native(0, false));
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 0);
        tx.set_field_u32(get_field_by_symbol("sfNetworkID"), 1025);
    });
    amendment.set_field_h256(get_field_by_symbol("sfAmendment"), Uint256::from_u64(1));

    assert_eq!(
        transaction_preflight_ter_with_network_id(&amendment, &ledger.rules(), 1025),
        Ter::TES_SUCCESS,
    );
    let mut view = ledger::ApplyViewImpl::new(ledger, ApplyFlags::NONE);
    let outcome =
        apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim_and_network_id(
            &mut view,
            &amendment,
            TxType::AMENDMENT,
            ApplyFlags::NONE,
            Ter::TES_SUCCESS,
            1025,
        );
    assert_eq!(outcome.result, Ter::TES_SUCCESS);
    assert!(outcome.applied);
}

#[test]
fn persistent_submit_sandbox_is_restored_during_unwind() {
    let source = AccountID::from_array([0xC3; 20]);
    let base = Arc::new(ledger_view(10, source, 1, &[]));
    let holder = Arc::new(Mutex::new(Some(Sandbox::new(
        Arc::new(OpenView::new_open(Arc::clone(&base), base.rules().clone())),
        ApplyFlags::NONE,
    ))));

    let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe({
        let holder = Arc::clone(&holder);
        let base = Arc::clone(&base);
        move || {
            let _guard = PersistentSubmitSandbox::take_or_new(holder, base);
            panic!("forced submit batch panic");
        }
    }));

    assert!(unwind.is_err());
    assert!(
        holder.lock().expect("sandbox holder mutex").is_some(),
        "a caught batch panic must not discard the persistent open-ledger sandbox"
    );
}

#[test]
fn xchain_commit_queue_consequences_include_native_amount_only() {
    for (amount, expected) in [
        (STAmount::new_native(1234, false), 1234),
        (STAmount::new_native(0, false), 0),
        (STAmount::new_native(1234, true), 0),
    ] {
        let tx = STTx::new(TxType::XCHAIN_COMMIT, |tx| {
            tx.set_field_amount(
                get_field_by_symbol("sfFee"),
                STAmount::new_native(10, false),
            );
            tx.set_field_u32(get_field_by_symbol("sfSequence"), 7);
            tx.set_field_amount(get_field_by_symbol("sfAmount"), amount.clone());
        });
        let consequences = canonical_sttx_consequences(&tx);
        assert_eq!(consequences.potential_spend(), expected);
        assert_eq!(consequences.fee(), 10);
    }
}

#[test]
fn metadata_oversize_boundary_matches_pinned_rippled_protocol_cap() {
    assert_eq!(protocol::OVERSIZE_METADATA_CAP, 5_200);
    assert_eq!(protocol::UNFUNDED_OFFER_REMOVE_LIMIT, 1_000);
    assert_eq!(protocol::EXPIRED_OFFER_REMOVE_LIMIT, 256);
    assert!(!super::exceeds_oversize_metadata_cap(5_200));
    assert!(super::exceeds_oversize_metadata_cap(5_201));
}
