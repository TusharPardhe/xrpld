use std::sync::Arc;

use app::state::application_root::{
    apply_simulated_transaction, apply_submit_transactor_shell,
    apply_submit_transactor_shell_with_delivered_amount,
};
use app::state::lending::calculate_loan_pay_base_fee;
use app::state::transactor_dispatcher::handle_real_dispatch;
use basics::base_uint::{Uint160, Uint192, Uint256};
use basics::number::NumberParts as RuntimeNumber;
use basics::string_utilities::str_unhex;
use ledger::{
    ApplyView, ApplyViewImpl, CanonicalTXSet, Fees, Ledger, LedgerConfig, LedgerHeader, ReadView,
    Sandbox, TxsRawView, pseudo_account_address,
};
use protocol::{
    AccountID, ApplyFlags, Asset, Currency, FeatureSet, IOUAmount, Issue, Keylet, LedgerEntryType,
    MPTAmount, MPTIssue, STAmount, STArray, STIssue, STLedgerEntry, STNumber, STObject, STTx,
    SerialIter, Serializer, StBase, Ter, TxMeta, TxType, XRPAmount, account_keylet,
    amm_lpt_currency, currency_from_string, get_field_by_symbol, line, lsfAllowTrustLineClawback,
    lsfDefaultRipple, lsfDisableMaster, lsfLoanImpaired, lsfLowDeepFreeze, owner_dir_keylet,
    parse_base58_account_id, permissioned_domain_keylet, sf_generic, signers_keylet, tfLoanDefault,
    tfLoanImpair, tfLoanUnimpair, xrp_issue,
};
use shamap::item::SHAMapItem;
use shamap::mutation::MutableTree;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::SHAMapNodeType;
use tx::{
    LSF_ONE_OWNER_COUNT, MPT_CAN_ESCROW_FLAG, MPT_CAN_TRADE_FLAG, MPT_CAN_TRANSFER_FLAG,
    MPTokenIssuanceCreatePreflightFacts, VAULT_PRIVATE_FLAG,
    run_mp_token_issuance_create_preflight,
};

use sha2::{Digest, Sha256};

fn sample_account(fill: u8) -> AccountID {
    AccountID::from_array([fill; 20])
}

fn dispatch_with_pre_fee_balance<V: ApplyView>(view: &mut V, tx: &STTx, tx_type: TxType) -> Ter {
    let account = tx.get_account_id(sf("sfAccount"));
    let balance = view
        .read(account_keylet(raw_account_id(account)))
        .expect("fixture AccountRoot read")
        .expect("fixture source AccountRoot")
        .get_field_amount(sf("sfBalance"))
        .xrp()
        .drops();
    handle_real_dispatch(view, tx, tx_type, Some(balance))
}

#[test]
fn account_set_production_apply_matches_legacy_flag_mutations() {
    let account = sample_account(0x31);
    let ledger = empty_ledger(vec![account_root(account, 0, 0)]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let set = STTx::new(TxType::ACCOUNT_SET, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_u32(
            sf("sfFlags"),
            protocol::tfRequireDestTag | protocol::tfRequireAuth | protocol::tfDisallowXRP,
        );
    });
    assert_eq!(
        handle_real_dispatch(&mut view, &set, TxType::ACCOUNT_SET, None),
        Ter::TES_SUCCESS
    );
    let flags = view
        .read(account_keylet(raw_account_id(account)))
        .expect("read")
        .expect("account")
        .get_field_u32(sf("sfFlags"));
    assert_eq!(
        flags & (protocol::lsfRequireDestTag | protocol::lsfRequireAuth | protocol::lsfDisallowXRP),
        protocol::lsfRequireDestTag | protocol::lsfRequireAuth | protocol::lsfDisallowXRP
    );

    let clear = STTx::new(TxType::ACCOUNT_SET, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_u32(
            sf("sfFlags"),
            protocol::tfOptionalDestTag | protocol::tfOptionalAuth | protocol::tfAllowXRP,
        );
    });
    assert_eq!(
        handle_real_dispatch(&mut view, &clear, TxType::ACCOUNT_SET, None),
        Ter::TES_SUCCESS
    );
    let flags = view
        .read(account_keylet(raw_account_id(account)))
        .expect("read")
        .expect("account")
        .get_field_u32(sf("sfFlags"));
    assert_eq!(
        flags & (protocol::lsfRequireDestTag | protocol::lsfRequireAuth | protocol::lsfDisallowXRP),
        0
    );
}

#[test]
fn account_set_production_apply_matches_canonical_field_and_irreversible_flag_rules() {
    let account = sample_account(0x32);
    let minter = sample_account(0x33);
    let mut root = account_root(
        account,
        0,
        protocol::lsfNoFreeze | protocol::lsfGlobalFreeze,
    );
    root.set_field_u8(sf("sfTickSize"), 7);
    root.set_field_vl(sf("sfDomain"), b"old.example");
    let ledger = empty_ledger(vec![root]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let clear_canonical_fields = STTx::new(TxType::ACCOUNT_SET, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_u8(sf("sfTickSize"), 16);
        tx.set_field_vl(sf("sfDomain"), b"");
        tx.set_field_u32(sf("sfClearFlag"), 7);
    });
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &clear_canonical_fields,
            TxType::ACCOUNT_SET,
            None,
        ),
        Ter::TES_SUCCESS
    );
    let root = view
        .read(account_keylet(raw_account_id(account)))
        .expect("read")
        .expect("account");
    assert!(!root.is_field_present(sf("sfTickSize")));
    assert!(!root.is_field_present(sf("sfDomain")));
    assert!(root.is_flag(protocol::lsfGlobalFreeze));

    let set_minter = STTx::new(TxType::ACCOUNT_SET, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_u32(sf("sfSetFlag"), 10);
        tx.set_account_id(sf("sfNFTokenMinter"), minter);
    });
    assert_eq!(
        handle_real_dispatch(&mut view, &set_minter, TxType::ACCOUNT_SET, None),
        Ter::TES_SUCCESS
    );
    let root = view
        .read(account_keylet(raw_account_id(account)))
        .expect("read")
        .expect("account");
    assert_eq!(root.get_account_id(sf("sfNFTokenMinter")), minter);
}

#[test]
fn did_set_reserve_uses_sponsored_account_base() {
    let account = sample_account(0x34);
    let sponsor = sample_account(0x35);
    let mut root = account_root_with_balance(account, 0, 0, 100);
    root.set_account_id(sf("sfSponsor"), sponsor);

    let mut ledger = empty_ledger(vec![root]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 200,
        increment: 50,
    });
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("fixEmptyDID")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::DID_SET, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_vl(sf("sfURI"), b"did:quaxar:sponsored");
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::DID_SET, Some(100)),
        Ter::TES_SUCCESS,
        "a sponsored AccountRoot owes one owner increment (50), not an account base plus increment (250)"
    );
}

fn sample_uint256(fill: u8) -> Uint256 {
    Uint256::from_array([fill; 32])
}

fn raw_account_id(account: AccountID) -> Uint160 {
    Uint160::from_slice(account.data()).expect("account width")
}

fn sf(name: &str) -> &'static protocol::SField {
    get_field_by_symbol(name)
}

fn test_xrp(drops: i64) -> STAmount {
    STAmount::from_xrp_amount(XRPAmount::from_drops(drops))
}

fn owner_count(view: &impl ReadView, account: AccountID) -> u32 {
    view.read(account_keylet(raw_account_id(account)))
        .expect("account root read")
        .expect("account root")
        .get_field_u32(sf("sfOwnerCount"))
}

fn account_root(account: AccountID, owner_count: u32, flags: u32) -> STLedgerEntry {
    account_root_with_balance(account, owner_count, flags, 1_000_000)
}

fn account_root_with_balance(
    account: AccountID,
    owner_count: u32,
    flags: u32,
    balance_drops: i64,
) -> STLedgerEntry {
    let mut entry = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        account_keylet(raw_account_id(account)).key,
    );
    entry.set_account_id(get_field_by_symbol("sfAccount"), account);
    entry.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    entry.set_field_amount(
        get_field_by_symbol("sfBalance"),
        STAmount::from_xrp_amount(XRPAmount::from_drops(balance_drops)),
    );
    entry.set_field_u32(get_field_by_symbol("sfOwnerCount"), owner_count);
    entry.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), sample_uint256(0xA1));
    entry.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 1);
    if flags != 0 {
        entry.set_field_u32(get_field_by_symbol("sfFlags"), flags);
    }
    entry
}

fn owner_dir_root(page_owner: AccountID, child: Uint256) -> STLedgerEntry {
    let root = owner_dir_keylet(raw_account_id(page_owner));
    let mut entry = STLedgerEntry::new(root);
    entry.set_field_h256(get_field_by_symbol("sfRootIndex"), root.key);
    entry.set_field_v256(
        get_field_by_symbol("sfIndexes"),
        protocol::STVector256::from_values(get_field_by_symbol("sfIndexes"), vec![child]),
    );
    entry
}

fn owner_dir_root_with_children(page_owner: AccountID, children: Vec<Uint256>) -> STLedgerEntry {
    let root = owner_dir_keylet(raw_account_id(page_owner));
    let mut entry = STLedgerEntry::new(root);
    entry.set_field_h256(get_field_by_symbol("sfRootIndex"), root.key);
    entry.set_field_v256(
        get_field_by_symbol("sfIndexes"),
        protocol::STVector256::from_values(get_field_by_symbol("sfIndexes"), children),
    );
    entry
}

fn signer_list_entry(account: AccountID, owner_node: u64, flags: u32) -> STLedgerEntry {
    let keylet = signers_keylet(raw_account_id(account));
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::SignerList, keylet.key);
    entry.set_field_u32(get_field_by_symbol("sfSignerQuorum"), 2);
    entry.set_field_u32(get_field_by_symbol("sfSignerListID"), 0);
    entry.set_field_u64(get_field_by_symbol("sfOwnerNode"), owner_node);
    if flags != 0 {
        entry.set_field_u32(get_field_by_symbol("sfFlags"), flags);
    }

    let mut signer_entries = STArray::new(get_field_by_symbol("sfSignerEntries"));
    let mut signer_entry = STObject::make_inner_object(get_field_by_symbol("sfSignerEntry"));
    signer_entry.set_account_id(get_field_by_symbol("sfAccount"), sample_account(0x66));
    signer_entry.set_field_u16(get_field_by_symbol("sfSignerWeight"), 1);
    signer_entries.push_back(signer_entry);
    entry.set_field_array(get_field_by_symbol("sfSignerEntries"), signer_entries);
    entry
}

fn empty_ledger(entries: Vec<STLedgerEntry>) -> Ledger {
    ledger_with_header(
        LedgerHeader {
            seq: 1,
            ..LedgerHeader::default()
        },
        entries,
    )
}

fn ledger_with_header(header: LedgerHeader, entries: Vec<STLedgerEntry>) -> Ledger {
    let mut tree = MutableTree::new(1);
    for entry in entries {
        tree.add_item(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(*entry.key(), entry.get_serializer().data().to_vec()),
        )
        .expect("state insert should succeed");
    }

    Ledger::from_maps(
        header,
        SyncTree::from_root_with_type(
            tree.root(),
            SHAMapType::State,
            false,
            1,
            SyncState::Immutable,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, false, 1),
    )
}

fn asset_number(asset: Asset, value: i64) -> STNumber {
    let mut number = STNumber::from(RuntimeNumber::from_i64(value));
    number.associate_asset(asset);
    number
}

fn asset_number_parts(asset: Asset, mantissa: i64, exponent: i32) -> STNumber {
    let value = RuntimeNumber::try_from_external_parts(
        mantissa,
        exponent,
        basics::number::get_mantissa_scale(),
    )
    .expect("number parts should be valid");
    let mut number = STNumber::from(value);
    number.associate_asset(asset);
    number
}

fn trust_line_entry(
    low: AccountID,
    high: AccountID,
    currency: Currency,
    balance: i64,
) -> STLedgerEntry {
    let keylet = line(low, high, currency);
    let mut sle = STLedgerEntry::from_type_and_key(LedgerEntryType::RippleState, keylet.key);
    sle.set_field_amount(
        sf("sfBalance"),
        STAmount::from_iou_amount(
            sf_generic(),
            IOUAmount::from_parts(balance, 0).expect("trustline balance"),
            Issue::new(currency, low),
        ),
    );
    sle.set_field_amount(
        sf("sfLowLimit"),
        STAmount::from_iou_amount(
            sf_generic(),
            IOUAmount::from_parts(1_000_000, 0).expect("low limit"),
            Issue::new(currency, low),
        ),
    );
    sle.set_field_amount(
        sf("sfHighLimit"),
        STAmount::from_iou_amount(
            sf_generic(),
            IOUAmount::from_parts(1_000_000, 0).expect("high limit"),
            Issue::new(currency, high),
        ),
    );
    sle.set_field_u32(sf("sfFlags"), 0);
    sle
}

fn trust_line_entry_iou(
    low: AccountID,
    high: AccountID,
    currency: Currency,
    balance: IOUAmount,
) -> STLedgerEntry {
    let keylet = line(low, high, currency);
    let mut sle = STLedgerEntry::from_type_and_key(LedgerEntryType::RippleState, keylet.key);
    sle.set_field_amount(
        sf("sfBalance"),
        STAmount::from_iou_amount(sf_generic(), balance, Issue::new(currency, low)),
    );
    sle.set_field_amount(
        sf("sfLowLimit"),
        STAmount::from_iou_amount(
            sf_generic(),
            IOUAmount::from_parts(1_000_000, 0).expect("low limit"),
            Issue::new(currency, low),
        ),
    );
    sle.set_field_amount(
        sf("sfHighLimit"),
        STAmount::from_iou_amount(
            sf_generic(),
            IOUAmount::from_parts(1_000_000, 0).expect("high limit"),
            Issue::new(currency, high),
        ),
    );
    sle.set_field_u32(sf("sfFlags"), 0);
    sle
}

fn amm_vote_entry(account: AccountID, trading_fee: u16, vote_weight: u32) -> STObject {
    let mut vote = STObject::make_inner_object(sf("sfVoteEntry"));
    vote.set_account_id(sf("sfAccount"), account);
    vote.set_field_u16(sf("sfTradingFee"), trading_fee);
    vote.set_field_u32(sf("sfVoteWeight"), vote_weight);
    vote
}

fn amm_slot(account: AccountID, discounted_fee: u16) -> STObject {
    let mut slot = STObject::make_inner_object(sf("sfAuctionSlot"));
    slot.set_account_id(sf("sfAccount"), account);
    slot.set_field_u32(sf("sfExpiration"), 1_000);
    slot.set_field_u16(sf("sfDiscountedFee"), discounted_fee);
    slot
}

fn amm_entry(
    amm_account: AccountID,
    issue1: Issue,
    issue2: Issue,
    lp_balance: i64,
    vote_entries: Vec<STObject>,
    discounted_fee: u16,
) -> STLedgerEntry {
    let keylet = protocol::keylet::amm(Asset::Issue(issue1), Asset::Issue(issue2));
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::AMM, keylet.key);
    entry.set_account_id(sf("sfAccount"), amm_account);
    entry.set_field_u16(sf("sfTradingFee"), 17);
    entry.set_field_amount(
        sf("sfLPTokenBalance"),
        STAmount::from_iou_amount(
            sf_generic(),
            IOUAmount::from_parts(lp_balance, 0).expect("lp balance"),
            Issue::new(
                amm_lpt_currency(issue1.currency, issue2.currency),
                amm_account,
            ),
        ),
    );
    entry.set_field_issue(
        sf("sfAsset"),
        STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(issue1)),
    );
    entry.set_field_issue(
        sf("sfAsset2"),
        STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(issue2)),
    );
    let mut votes = STArray::new(sf("sfVoteSlots"));
    for vote in vote_entries {
        votes.push_back(vote);
    }
    entry.set_field_array(sf("sfVoteSlots"), votes);
    entry.set_field_object(sf("sfAuctionSlot"), amm_slot(amm_account, discounted_fee));
    entry
}

fn amm_mpt_xrp_entry(
    amm_account: AccountID,
    mpt_issue: MPTIssue,
    mpt_pool_balance: i64,
    lp_balance: i64,
) -> STLedgerEntry {
    let xrp = xrp_issue();
    let keylet = protocol::keylet::amm(Asset::MPTIssue(mpt_issue), Asset::Issue(xrp));
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::AMM, keylet.key);
    entry.set_account_id(sf("sfAccount"), amm_account);
    entry.set_field_u16(sf("sfTradingFee"), 17);
    entry.set_field_amount(
        sf("sfAmount"),
        STAmount::from_mpt_amount(
            sf("sfAmount"),
            MPTAmount::from_value(mpt_pool_balance),
            mpt_issue,
        ),
    );
    entry.set_field_amount(
        sf("sfLPTokenBalance"),
        STAmount::from_iou_amount(
            sf_generic(),
            IOUAmount::from_parts(lp_balance, 0).expect("lp balance"),
            Issue::new(currency_from_string("LPT"), amm_account),
        ),
    );
    entry.set_field_issue(
        sf("sfAsset"),
        STIssue::new_with_asset(sf("sfAsset"), Asset::MPTIssue(mpt_issue)),
    );
    entry.set_field_issue(
        sf("sfAsset2"),
        STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(xrp)),
    );
    entry.set_field_array(sf("sfVoteSlots"), STArray::new(sf("sfVoteSlots")));
    entry.set_field_object(sf("sfAuctionSlot"), amm_slot(amm_account, 0));
    entry
}

fn iou_amount(field: &'static protocol::SField, issue: Issue, value: i64) -> STAmount {
    STAmount::from_iou_amount(
        field,
        IOUAmount::from_parts(value, 0).expect("iou amount"),
        issue,
    )
}

fn signer_list_set_tx(account: AccountID, quorum: u32, signers: &[(AccountID, u16)]) -> STTx {
    let mut signer_entries = STArray::new(get_field_by_symbol("sfSignerEntries"));
    for (signer_account, weight) in signers {
        let mut signer_entry = STObject::make_inner_object(get_field_by_symbol("sfSignerEntry"));
        signer_entry.set_account_id(get_field_by_symbol("sfAccount"), *signer_account);
        signer_entry.set_field_u16(get_field_by_symbol("sfSignerWeight"), *weight);
        signer_entries.push_back(signer_entry);
    }

    STTx::new(TxType::SIGNER_LIST_SET, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_u32(get_field_by_symbol("sfSignerQuorum"), quorum);
        if !signers.is_empty() {
            object.set_field_array(get_field_by_symbol("sfSignerEntries"), signer_entries);
        }
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn ticket_create_tx(account: AccountID, sequence: u32, ticket_count: u32) -> STTx {
    STTx::new(TxType::TICKET_CREATE, move |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_field_u32(sf("sfSequence"), sequence);
        object.set_field_u32(sf("sfTicketCount"), ticket_count);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn escrow_create_tx(account: AccountID, destination: AccountID, sequence: u32) -> STTx {
    STTx::new(TxType::ESCROW_CREATE, move |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(1_000)),
        );
        object.set_field_u32(sf("sfFinishAfter"), 1001);
        object.set_field_u32(sf("sfSequence"), sequence);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn paychan_create_ticket_tx(
    account: AccountID,
    destination: AccountID,
    ticket_sequence: u32,
) -> STTx {
    STTx::new(TxType::PAYCHAN_CREATE, move |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(1_000)),
        );
        object.set_field_u32(sf("sfSettleDelay"), 60);
        object.set_field_vl(sf("sfPublicKey"), &[3; 33]);
        object.set_field_u32(sf("sfSequence"), 0);
        object.set_field_u32(sf("sfTicketSequence"), ticket_sequence);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn oracle_price_data_with_currencies(
    base: Currency,
    quote: Currency,
    price: u64,
    scale: u8,
) -> STObject {
    let mut entry = STObject::make_inner_object(sf("sfPriceData"));
    entry.set_field_currency(
        sf("sfBaseAsset"),
        protocol::STCurrency::new_with_currency(sf("sfBaseAsset"), base),
    );
    entry.set_field_currency(
        sf("sfQuoteAsset"),
        protocol::STCurrency::new_with_currency(sf("sfQuoteAsset"), quote),
    );
    entry.set_field_u64(sf("sfAssetPrice"), price);
    entry.set_field_u8(sf("sfScale"), scale);
    entry
}

fn oracle_price_data(base: &str, quote: &str, price: u64, scale: u8) -> STObject {
    oracle_price_data_with_currencies(
        currency_from_string(base),
        currency_from_string(quote),
        price,
        scale,
    )
}

fn oracle_set_tx(
    account: AccountID,
    document_id: u32,
    last_update_time: u32,
    entries: &[STObject],
    include_create_fields: bool,
) -> STTx {
    let mut series = STArray::new(sf("sfPriceDataSeries"));
    for entry in entries {
        series.push_back(entry.clone());
    }
    STTx::new(TxType::ORACLE_SET, move |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_field_u32(sf("sfOracleDocumentID"), document_id);
        object.set_field_u32(sf("sfLastUpdateTime"), last_update_time);
        object.set_field_array(sf("sfPriceDataSeries"), series);
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        if include_create_fields {
            object.set_field_vl(sf("sfProvider"), b"provider");
            object.set_field_vl(sf("sfAssetClass"), b"currency");
        }
    })
}

fn oracle_pair(entry: &STObject) -> (String, String) {
    (
        protocol::currency_to_string(entry.get_field_currency(sf("sfBaseAsset")).currency()),
        protocol::currency_to_string(entry.get_field_currency(sf("sfQuoteAsset")).currency()),
    )
}

fn delegate_permissions(permissions: &[u32]) -> STArray {
    let mut permission_entries = STArray::new(get_field_by_symbol("sfPermissions"));
    for permission in permissions {
        let mut entry = STObject::make_inner_object(get_field_by_symbol("sfPermission"));
        entry.set_field_u32(get_field_by_symbol("sfPermissionValue"), *permission);
        permission_entries.push_back(entry);
    }
    permission_entries
}

fn delegate_set_tx(account: AccountID, authorize: AccountID, permissions: &[u32]) -> STTx {
    let permission_entries = delegate_permissions(permissions);
    STTx::new(TxType::DELEGATE_SET, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_account_id(get_field_by_symbol("sfAuthorize"), authorize);
        object.set_field_array(
            get_field_by_symbol("sfPermissions"),
            permission_entries.clone(),
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    })
}

fn delegate_entry(
    account: AccountID,
    authorize: AccountID,
    permissions: &[u32],
    owner_node: u64,
    destination_node: u64,
) -> STLedgerEntry {
    let keylet = protocol::delegate_keylet(raw_account_id(account), raw_account_id(authorize));
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::Delegate, keylet.key);
    entry.set_account_id(get_field_by_symbol("sfAccount"), account);
    entry.set_account_id(get_field_by_symbol("sfAuthorize"), authorize);
    entry.set_field_array(
        get_field_by_symbol("sfPermissions"),
        delegate_permissions(permissions),
    );
    entry.set_field_u64(get_field_by_symbol("sfOwnerNode"), owner_node);
    entry.set_field_u64(get_field_by_symbol("sfDestinationNode"), destination_node);
    entry
}

fn payment_tx(sequence: u32) -> STTx {
    STTx::new(TxType::PAYMENT, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), sample_account(0x71));
        tx.set_account_id(get_field_by_symbol("sfDestination"), sample_account(0x72));
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(1_000)),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
    })
}

fn direct_xrp_payment_tx(
    source: AccountID,
    destination: AccountID,
    amount_drops: i64,
    fee_drops: i64,
) -> STTx {
    STTx::new(TxType::PAYMENT, move |tx| {
        tx.set_account_id(sf("sfAccount"), source);
        tx.set_account_id(sf("sfDestination"), destination);
        tx.set_field_amount(sf("sfAmount"), test_xrp(amount_drops));
        tx.set_field_amount(sf("sfFee"), test_xrp(fee_drops));
        tx.set_field_u32(sf("sfSequence"), 1);
    })
}

fn inner_batch_payment_tx(
    account: AccountID,
    destination: AccountID,
    sequence: u32,
    amount_drops: i64,
) -> STTx {
    STTx::new(TxType::PAYMENT, move |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), account);
        tx.set_account_id(get_field_by_symbol("sfDestination"), destination);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(amount_drops)),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(0)),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::INNER_BATCH_TRANSACTION_FLAG,
        );
        tx.set_field_vl(get_field_by_symbol("sfSigningPubKey"), &[]);
    })
}

fn batch_raw_transaction(tx: &STTx) -> STObject {
    let mut raw = tx.clone_as_object();
    raw.set_fname(get_field_by_symbol("sfRawTransaction"));
    raw
}

fn batch_tx_with_inner(account: AccountID, flags: u32, inner: &[STTx]) -> STTx {
    let mut raw_transactions = STArray::new(get_field_by_symbol("sfRawTransactions"));
    for tx in inner {
        raw_transactions.push_back(batch_raw_transaction(tx));
    }

    STTx::new(TxType::BATCH, move |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), account);
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(get_field_by_symbol("sfFlags"), flags);
        tx.set_field_array(
            get_field_by_symbol("sfRawTransactions"),
            raw_transactions.clone(),
        );
    })
}

fn batch_tx(account: AccountID) -> STTx {
    let first = payment_tx(3);
    let second = payment_tx(4);
    batch_tx_with_inner(account, protocol::tfAllOrNothing, &[first, second])
}

fn permissioned_domain_credentials(entries: &[(AccountID, &[u8])]) -> STArray {
    let mut credentials = STArray::new(get_field_by_symbol("sfAcceptedCredentials"));
    for (issuer, credential_type) in entries {
        let mut credential = STObject::make_inner_object(get_field_by_symbol("sfCredential"));
        credential.set_account_id(get_field_by_symbol("sfIssuer"), *issuer);
        credential.set_field_vl(get_field_by_symbol("sfCredentialType"), credential_type);
        credentials.push_back(credential);
    }
    credentials
}

fn permissioned_domain_entry(
    owner: AccountID,
    seq: u32,
    owner_node: u64,
    credentials: &[(AccountID, &[u8])],
) -> STLedgerEntry {
    let mut entry = STLedgerEntry::new(permissioned_domain_keylet(raw_account_id(owner), seq));
    entry.set_account_id(get_field_by_symbol("sfOwner"), owner);
    entry.set_field_u32(get_field_by_symbol("sfSequence"), seq);
    entry.set_field_array(
        get_field_by_symbol("sfAcceptedCredentials"),
        permissioned_domain_credentials(credentials),
    );
    entry.set_field_u64(get_field_by_symbol("sfOwnerNode"), owner_node);
    entry
}

fn permissioned_domain_set_tx(
    account: AccountID,
    sequence: u32,
    domain_id: Option<Uint256>,
    credentials: &[(AccountID, &[u8])],
) -> STTx {
    let accepted_credentials = permissioned_domain_credentials(credentials);
    STTx::new(TxType::PERMISSIONED_DOMAIN_SET, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        object.set_field_array(
            get_field_by_symbol("sfAcceptedCredentials"),
            accepted_credentials,
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        if let Some(domain_id) = domain_id {
            object.set_field_h256(get_field_by_symbol("sfDomainID"), domain_id);
        }
    })
}

fn permissioned_domain_delete_tx(account: AccountID, domain_id: Uint256) -> STTx {
    STTx::new(TxType::PERMISSIONED_DOMAIN_DELETE, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfDomainID"), domain_id);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn credential_keylet(subject: AccountID, issuer: AccountID, credential_type: &[u8]) -> Keylet {
    protocol::credential_keylet(
        raw_account_id(subject),
        raw_account_id(issuer),
        credential_type,
    )
}

fn credential_entry(
    subject: AccountID,
    issuer: AccountID,
    credential_type: &[u8],
    issuer_node: u64,
    subject_node: Option<u64>,
    flags: u32,
    expiration: Option<u32>,
) -> STLedgerEntry {
    let keylet = credential_keylet(subject, issuer, credential_type);
    let mut entry = STLedgerEntry::new(keylet);
    entry.set_account_id(get_field_by_symbol("sfSubject"), subject);
    entry.set_account_id(get_field_by_symbol("sfIssuer"), issuer);
    entry.set_stbase(protocol::STBlob::from_buffer(
        get_field_by_symbol("sfCredentialType"),
        basics::buffer::Buffer::from(credential_type),
    ));
    entry.set_field_u64(get_field_by_symbol("sfIssuerNode"), issuer_node);
    if let Some(subject_node) = subject_node {
        entry.set_field_u64(get_field_by_symbol("sfSubjectNode"), subject_node);
    }
    if flags != 0 {
        entry.set_field_u32(get_field_by_symbol("sfFlags"), flags);
    }
    if let Some(expiration) = expiration {
        entry.set_field_u32(get_field_by_symbol("sfExpiration"), expiration);
    }
    entry
}

fn credential_create_tx(account: AccountID, subject: AccountID, credential_type: &[u8]) -> STTx {
    let credential_type = credential_type.to_vec();
    STTx::new(TxType::CREDENTIAL_CREATE, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_account_id(get_field_by_symbol("sfSubject"), subject);
        object.set_field_vl(get_field_by_symbol("sfCredentialType"), &credential_type);
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn credential_accept_tx(subject: AccountID, issuer: AccountID, credential_type: &[u8]) -> STTx {
    let credential_type = credential_type.to_vec();
    STTx::new(TxType::CREDENTIAL_ACCEPT, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), subject);
        object.set_account_id(get_field_by_symbol("sfIssuer"), issuer);
        object.set_field_vl(get_field_by_symbol("sfCredentialType"), &credential_type);
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn credential_delete_tx(
    account: AccountID,
    subject: Option<AccountID>,
    issuer: Option<AccountID>,
    credential_type: &[u8],
) -> STTx {
    let credential_type = credential_type.to_vec();
    STTx::new(TxType::CREDENTIAL_DELETE, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        if let Some(subject) = subject {
            object.set_account_id(get_field_by_symbol("sfSubject"), subject);
        }
        if let Some(issuer) = issuer {
            object.set_account_id(get_field_by_symbol("sfIssuer"), issuer);
        }
        object.set_field_vl(get_field_by_symbol("sfCredentialType"), &credential_type);
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn nft_page_token(token_id: Uint256) -> STObject {
    let mut token = STObject::new(get_field_by_symbol("sfNFToken"));
    token.set_field_h256(get_field_by_symbol("sfNFTokenID"), token_id);
    token
}

fn nft_page_entry(
    keylet: protocol::Keylet,
    token_id: Uint256,
    previous: Option<Uint256>,
    next: Option<Uint256>,
) -> STLedgerEntry {
    let mut entry = STLedgerEntry::new(keylet);
    let mut tokens = STArray::new(get_field_by_symbol("sfNFTokens"));
    tokens.push_back(nft_page_token(token_id));
    entry.set_field_array(get_field_by_symbol("sfNFTokens"), tokens);
    if let Some(previous) = previous {
        entry.set_field_h256(get_field_by_symbol("sfPreviousPageMin"), previous);
    }
    if let Some(next) = next {
        entry.set_field_h256(get_field_by_symbol("sfNextPageMin"), next);
    }
    entry
}

fn nftoken_mint_tx(account: AccountID, taxon: u32, amount: Option<STAmount>) -> STTx {
    STTx::new(TxType::NFTOKEN_MINT, move |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_field_u32(sf("sfNFTokenTaxon"), taxon);
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_field_amount(sf("sfFee"), test_xrp(10));
        if let Some(amount) = amount {
            object.set_field_amount(sf("sfAmount"), amount);
        }
    })
}

fn nftoken_burn_tx(account: AccountID, nftoken_id: Uint256) -> STTx {
    STTx::new(TxType::NFTOKEN_BURN, move |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_field_h256(sf("sfNFTokenID"), nftoken_id);
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_field_amount(sf("sfFee"), test_xrp(10));
    })
}

fn nftoken_accept_sell_offer_tx(account: AccountID, offer_id: Uint256) -> STTx {
    STTx::new(TxType::NFTOKEN_ACCEPT_OFFER, move |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_field_h256(sf("sfNFTokenSellOffer"), offer_id);
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_field_amount(sf("sfFee"), test_xrp(10));
    })
}

fn ledger_state_fix_tx(account: AccountID, owner: Option<AccountID>, fix_type: u16) -> STTx {
    STTx::new(TxType::LEDGER_STATE_FIX, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_u16(get_field_by_symbol("sfLedgerFixType"), fix_type);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        if let Some(owner) = owner {
            object.set_account_id(get_field_by_symbol("sfOwner"), owner);
        }
    })
}

fn ledger_state_fix_book_tx(account: AccountID, book_directory: Uint256) -> STTx {
    STTx::new(TxType::LEDGER_STATE_FIX, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_u16(get_field_by_symbol("sfLedgerFixType"), 2);
        object.set_field_h256(get_field_by_symbol("sfBookDirectory"), book_directory);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    })
}

fn book_directory_entry(key: Uint256, exchange_rate: Option<u64>) -> STLedgerEntry {
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::DirectoryNode, key);
    entry.set_field_h256(get_field_by_symbol("sfRootIndex"), key);
    if let Some(exchange_rate) = exchange_rate {
        entry.set_field_u64(get_field_by_symbol("sfExchangeRate"), exchange_rate);
    }
    entry
}

fn offer_create_tx(
    account: AccountID,
    sequence: u32,
    taker_pays: STAmount,
    taker_gets: STAmount,
    flags: u32,
    domain_id: Option<Uint256>,
) -> STTx {
    STTx::new(TxType::OFFER_CREATE, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        object.set_field_u32(get_field_by_symbol("sfFlags"), flags);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_amount(get_field_by_symbol("sfTakerPays"), taker_pays);
        object.set_field_amount(get_field_by_symbol("sfTakerGets"), taker_gets);
        if let Some(domain_id) = domain_id {
            object.set_field_h256(get_field_by_symbol("sfDomainID"), domain_id);
        }
    })
}

fn offer_create_cancel_tx(
    account: AccountID,
    sequence: u32,
    offer_sequence: u32,
    taker_pays: STAmount,
    taker_gets: STAmount,
    flags: u32,
) -> STTx {
    STTx::new(TxType::OFFER_CREATE, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        object.set_field_u32(get_field_by_symbol("sfOfferSequence"), offer_sequence);
        object.set_field_u32(get_field_by_symbol("sfFlags"), flags);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_amount(get_field_by_symbol("sfTakerPays"), taker_pays);
        object.set_field_amount(get_field_by_symbol("sfTakerGets"), taker_gets);
    })
}

fn vault_entry(owner: AccountID, pseudo: AccountID, seq: u32, asset: Asset) -> STLedgerEntry {
    let keylet = protocol::vault_keylet(raw_account_id(owner), seq);
    let mut entry = STLedgerEntry::from_type_and_key(LedgerEntryType::Vault, keylet.key);
    entry.set_field_u32(get_field_by_symbol("sfFlags"), 0);
    entry.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), sample_uint256(0xB1));
    entry.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 1);
    entry.set_field_u32(get_field_by_symbol("sfSequence"), seq);
    entry.set_field_u64(get_field_by_symbol("sfOwnerNode"), 0);
    entry.set_account_id(get_field_by_symbol("sfOwner"), owner);
    entry.set_account_id(get_field_by_symbol("sfAccount"), pseudo);
    entry.set_field_issue(
        get_field_by_symbol("sfAsset"),
        STIssue::new_with_asset(get_field_by_symbol("sfAsset"), asset),
    );
    entry.set_field_number(get_field_by_symbol("sfAssetsTotal"), asset_number(asset, 0));
    entry.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 0),
    );
    entry.set_field_number(
        get_field_by_symbol("sfLossUnrealized"),
        asset_number(asset, 0),
    );
    entry
}

fn share_id_for(account: AccountID, sequence: u32) -> Uint192 {
    let mut bytes = [0u8; 24];
    bytes[..4].copy_from_slice(&sequence.to_be_bytes());
    bytes[4..].copy_from_slice(account.data());
    Uint192::from_slice(&bytes).expect("share id width")
}

fn vault_entry_with_share(
    owner: AccountID,
    pseudo: AccountID,
    seq: u32,
    asset: Asset,
    share_id: Uint192,
) -> STLedgerEntry {
    let mut entry = vault_entry(owner, pseudo, seq, asset);
    entry.set_field_h192(get_field_by_symbol("sfShareMPTID"), share_id);
    entry
}

fn mpt_issuance_entry(
    issuer: AccountID,
    sequence: u32,
    outstanding_amount: u64,
    flags: u32,
) -> STLedgerEntry {
    let keylet = protocol::mpt_issuance_keylet(sequence, raw_account_id(issuer));
    let mut entry = STLedgerEntry::new(keylet);
    entry.set_account_id(get_field_by_symbol("sfIssuer"), issuer);
    entry.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
    entry.set_field_u64(
        get_field_by_symbol("sfOutstandingAmount"),
        outstanding_amount,
    );
    entry.set_field_u32(get_field_by_symbol("sfFlags"), flags);
    entry.set_field_u64(get_field_by_symbol("sfOwnerNode"), 0);
    entry
}

fn mpt_issuance_entry_with_transfer_fee(
    issuer: AccountID,
    sequence: u32,
    outstanding_amount: u64,
    flags: u32,
    transfer_fee: u16,
) -> STLedgerEntry {
    let mut entry = mpt_issuance_entry(issuer, sequence, outstanding_amount, flags);
    entry.set_field_u16(get_field_by_symbol("sfTransferFee"), transfer_fee);
    entry
}

fn mptoken_entry(account: AccountID, share_id: Uint192, amount: u64) -> STLedgerEntry {
    let keylet = protocol::mptoken_keylet_from_mptid(share_id, raw_account_id(account));
    let mut entry = STLedgerEntry::new(keylet);
    entry.set_account_id(get_field_by_symbol("sfAccount"), account);
    entry.set_field_h192(get_field_by_symbol("sfMPTokenIssuanceID"), share_id);
    entry.set_field_u64(get_field_by_symbol("sfMPTAmount"), amount);
    entry.set_field_u32(get_field_by_symbol("sfFlags"), 0);
    entry.set_field_u64(get_field_by_symbol("sfOwnerNode"), 0);
    entry
}

#[test]
fn escrow_finish_mpt_token_escrow_v1_tracks_gross_lock_and_transfer_fee() {
    let owner = sample_account(0xB1);
    let destination = sample_account(0xB2);
    let issuer = sample_account(0xB3);
    let issuance_id = share_id_for(issuer, 1);
    let amount = STAmount::from_mpt_amount(
        sf("sfAmount"),
        MPTAmount::from_value(125),
        MPTIssue::new(issuance_id),
    );

    let apply = |amended| {
        let mut issuance =
            mpt_issuance_entry_with_transfer_fee(issuer, 1, 1_000, MPT_CAN_TRANSFER_FLAG, 25_000);
        issuance.set_field_u64(sf("sfLockedAmount"), 125);
        let mut owner_token = mptoken_entry(owner, issuance_id, 875);
        owner_token.set_field_u64(sf("sfLockedAmount"), 125);
        let mut escrow = STLedgerEntry::from_type_and_key(
            LedgerEntryType::Escrow,
            protocol::escrow_keylet(raw_account_id(owner), 1).key,
        );
        escrow.set_account_id(sf("sfAccount"), owner);
        escrow.set_account_id(sf("sfDestination"), destination);
        escrow.set_field_amount(sf("sfAmount"), amount.clone());
        escrow.set_field_u32(sf("sfCancelAfter"), 0);
        escrow.set_field_u32(sf("sfTransferRate"), 1_250_000_000);
        escrow.set_field_u64(sf("sfOwnerNode"), 0);

        let mut ledger = ledger_with_header(
            LedgerHeader {
                seq: 1,
                drops: 100_000_000_000,
                ..LedgerHeader::default()
            },
            vec![
                account_root(owner, 1, 0),
                account_root(destination, 0, 0),
                account_root(issuer, 0, 0),
                issuance,
                owner_token,
                mptoken_entry(destination, issuance_id, 0),
                owner_dir_root(owner, protocol::escrow_keylet(raw_account_id(owner), 1).key),
                escrow,
            ],
        );
        ledger.set_rules(protocol::Rules::new([]));
        if amended {
            ledger.set_rules(protocol::Rules::new([protocol::feature_id(
                "fixTokenEscrowV1",
            )]));
        }

        let tx = STTx::new(TxType::ESCROW_FINISH, |object| {
            object.set_account_id(sf("sfAccount"), destination);
            object.set_account_id(sf("sfOwner"), owner);
            object.set_field_u32(sf("sfOfferSequence"), 1);
            object.set_field_amount(
                sf("sfFee"),
                STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
            );
            object.set_field_u32(sf("sfSequence"), 1);
        });

        let base = Arc::new(ledger.clone());
        let mut view = Sandbox::new(base, ApplyFlags::NONE);
        assert_eq!(
            apply_submit_transactor_shell(&mut view, &tx, TxType::ESCROW_FINISH),
            Ter::TES_SUCCESS
        );
        view.apply(&mut ledger)
            .expect("sandbox apply should succeed");
        ledger
    };

    for amended in [false, true] {
        let ledger = apply(amended);
        let destination_token = ledger
            .peek(protocol::mptoken_keylet_from_mptid(
                issuance_id,
                raw_account_id(destination),
            ))
            .expect("destination token read should succeed")
            .expect("destination token should exist");
        assert_eq!(destination_token.get_field_u64(sf("sfMPTAmount")), 100);

        let owner_token = ledger
            .peek(protocol::mptoken_keylet_from_mptid(
                issuance_id,
                raw_account_id(owner),
            ))
            .expect("owner token read should succeed")
            .expect("owner token should exist");
        let issuance = ledger
            .peek(protocol::mpt_issuance_keylet_from_mptid(issuance_id))
            .expect("issuance read should succeed")
            .expect("issuance should exist");

        if amended {
            assert!(!owner_token.is_field_present(sf("sfLockedAmount")));
            assert!(!issuance.is_field_present(sf("sfLockedAmount")));
            assert_eq!(issuance.get_field_u64(sf("sfOutstandingAmount")), 975);
        } else {
            assert_eq!(owner_token.get_field_u64(sf("sfLockedAmount")), 25);
            assert_eq!(issuance.get_field_u64(sf("sfLockedAmount")), 25);
            assert_eq!(issuance.get_field_u64(sf("sfOutstandingAmount")), 1_000);
        }
    }
}

#[test]
fn escrow_finish_mpt_cleanup_3_4_rounds_transfer_fee_down() {
    let owner = sample_account(0xB4);
    let destination = sample_account(0xB5);
    let issuer = sample_account(0xB6);
    let issuance_id = share_id_for(issuer, 1);
    let amount = STAmount::from_mpt_amount(
        sf("sfAmount"),
        MPTAmount::from_value(10_011),
        MPTIssue::new(issuance_id),
    );

    let mut issuance =
        mpt_issuance_entry_with_transfer_fee(issuer, 1, 100_000, MPT_CAN_TRANSFER_FLAG, 100);
    issuance.set_field_u64(sf("sfLockedAmount"), 10_011);
    let mut owner_token = mptoken_entry(owner, issuance_id, 89_989);
    owner_token.set_field_u64(sf("sfLockedAmount"), 10_011);
    let escrow_keylet = protocol::escrow_keylet(raw_account_id(owner), 1);
    let mut escrow = STLedgerEntry::from_type_and_key(LedgerEntryType::Escrow, escrow_keylet.key);
    escrow.set_account_id(sf("sfAccount"), owner);
    escrow.set_account_id(sf("sfDestination"), destination);
    escrow.set_field_amount(sf("sfAmount"), amount);
    escrow.set_field_u32(sf("sfTransferRate"), 1_001_000_000);
    escrow.set_field_u64(sf("sfOwnerNode"), 0);

    for (cleanup_3_4, expected_delivered, expected_outstanding) in
        [(false, 10_001, 99_990), (true, 10_000, 99_989)]
    {
        let mut ledger = ledger_with_header(
            LedgerHeader {
                seq: 1,
                drops: 100_000_000_000,
                ..LedgerHeader::default()
            },
            vec![
                account_root(owner, 1, 0),
                account_root(destination, 0, 0),
                account_root(issuer, 0, 0),
                issuance.clone(),
                owner_token.clone(),
                mptoken_entry(destination, issuance_id, 0),
                owner_dir_root(owner, escrow_keylet.key),
                escrow.clone(),
            ],
        );
        let mut features = vec![protocol::feature_id("fixTokenEscrowV1")];
        if cleanup_3_4 {
            features.push(protocol::feature_id("fixCleanup3_4_0"));
        }
        ledger.set_rules(protocol::Rules::new(features));
        let tx = STTx::new(TxType::ESCROW_FINISH, |object| {
            object.set_account_id(sf("sfAccount"), destination);
            object.set_account_id(sf("sfOwner"), owner);
            object.set_field_u32(sf("sfOfferSequence"), 1);
            object.set_field_amount(sf("sfFee"), test_xrp(10));
            object.set_field_u32(sf("sfSequence"), 1);
        });

        let mut view = Sandbox::new(Arc::new(ledger.clone()), ApplyFlags::NONE);
        assert_eq!(
            apply_submit_transactor_shell(&mut view, &tx, TxType::ESCROW_FINISH),
            Ter::TES_SUCCESS
        );
        view.apply(&mut ledger).expect("escrow finish applies");

        let destination_token = ledger
            .peek(protocol::mptoken_keylet_from_mptid(
                issuance_id,
                raw_account_id(destination),
            ))
            .expect("destination token read")
            .expect("destination token");
        assert_eq!(
            destination_token.get_field_u64(sf("sfMPTAmount")),
            expected_delivered
        );
        let owner_token = ledger
            .peek(protocol::mptoken_keylet_from_mptid(
                issuance_id,
                raw_account_id(owner),
            ))
            .expect("owner token read")
            .expect("owner token");
        assert!(!owner_token.is_field_present(sf("sfLockedAmount")));
        let issuance = ledger
            .peek(protocol::mpt_issuance_keylet_from_mptid(issuance_id))
            .expect("issuance read")
            .expect("issuance");
        assert!(!issuance.is_field_present(sf("sfLockedAmount")));
        assert_eq!(
            issuance.get_field_u64(sf("sfOutstandingAmount")),
            expected_outstanding
        );
        assert!(ledger.peek(escrow_keylet).expect("escrow read").is_none());
    }
}

#[test]
fn escrow_finish_created_mpt_records_its_issuance_id() {
    let owner = sample_account(0xC4);
    let destination = sample_account(0xC5);
    let issuer = sample_account(0xC6);
    let issuance_id = share_id_for(issuer, 1);
    let amount = STAmount::from_mpt_amount(
        sf("sfAmount"),
        MPTAmount::from_value(10_000),
        MPTIssue::new(issuance_id),
    );

    let mut issuance =
        mpt_issuance_entry_with_transfer_fee(issuer, 1, 100_000, MPT_CAN_TRANSFER_FLAG, 100);
    issuance.set_field_u64(sf("sfLockedAmount"), 10_000);
    let mut owner_token = mptoken_entry(owner, issuance_id, 90_000);
    owner_token.set_field_u64(sf("sfLockedAmount"), 10_000);
    let escrow_keylet = protocol::escrow_keylet(raw_account_id(owner), 1);
    let mut escrow = STLedgerEntry::from_type_and_key(LedgerEntryType::Escrow, escrow_keylet.key);
    escrow.set_account_id(sf("sfAccount"), owner);
    escrow.set_account_id(sf("sfDestination"), destination);
    escrow.set_field_amount(sf("sfAmount"), amount);
    escrow.set_field_u32(sf("sfTransferRate"), 1_001_000_000);
    escrow.set_field_u64(sf("sfOwnerNode"), 0);
    escrow.set_field_u64(sf("sfDestinationNode"), 0);

    let mut ledger = ledger_with_header(
        LedgerHeader {
            seq: 1,
            drops: 100_000_000_000,
            ..LedgerHeader::default()
        },
        vec![
            account_root(owner, 1, 0),
            account_root(destination, 0, 0),
            account_root(issuer, 0, 0),
            issuance,
            owner_token,
            owner_dir_root(owner, escrow_keylet.key),
            owner_dir_root(destination, escrow_keylet.key),
            escrow,
        ],
    );
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("fixTokenEscrowV1"),
        protocol::feature_id("fixCleanup3_4_0"),
        protocol::feature_id("TokenEscrow"),
        protocol::feature_id("MPTokensV2"),
    ]));
    let tx = STTx::new(TxType::ESCROW_FINISH, |object| {
        object.set_account_id(sf("sfAccount"), destination);
        object.set_account_id(sf("sfOwner"), owner);
        object.set_field_u32(sf("sfOfferSequence"), 1);
        object.set_field_amount(sf("sfFee"), test_xrp(10));
        object.set_field_u32(sf("sfSequence"), 1);
    });

    let mut view = Sandbox::new(Arc::new(ledger.clone()), ApplyFlags::NONE);
    assert_eq!(
        apply_submit_transactor_shell(&mut view, &tx, TxType::ESCROW_FINISH),
        Ter::TES_SUCCESS
    );
    view.apply(&mut ledger).expect("escrow finish applies");

    let destination_token = ledger
        .peek(protocol::mptoken_keylet_from_mptid(
            issuance_id,
            raw_account_id(destination),
        ))
        .expect("destination token read")
        .expect("destination token");
    assert_eq!(
        destination_token.get_field_h192(sf("sfMPTokenIssuanceID")),
        issuance_id
    );
    assert_eq!(destination_token.get_field_u64(sf("sfMPTAmount")), 9_990);
}

fn canonical_sle(index: &str, blob: &str) -> STLedgerEntry {
    let mut key = Uint256::default();
    assert!(key.parse_hex(index), "canonical ledger index");
    let bytes = str_unhex(blob).expect("canonical SLE hex");
    STLedgerEntry::from_serial_iter(&mut SerialIter::new(&bytes), key)
}

#[test]
fn testnet_20214054_clawback_and_account_set_match_canonical_metadata_bytes() {
    // Exact parent objects, consensus salt, transactions, and metadata from
    // Testnet ledger 20,214,054. The node produced an incompatible child at
    // this boundary, so pin both canonical application order and leaf bytes.
    let entries = [
        ("BABED78B2E77358D608B70AC304E7C83FD91D62DA4C2FF63979EC2CA98A09A84", "1100612200000000240134712425013471242D00000000559BBA13F867B7CCBDB66CCA303E68D0FBB4ECB7CBF569E7F49608E440C7C3717E624000000005F5E10081146E26A037E5F3C80945C4765A025AFFAA0BFEABFB"),
        ("1768F3A001B093B3453688DA92EC06148D0698BD1ED9E58A95903CC65C4E8E11", "1100612280800000240134711F25013471242D0000000055EA8B2C8C220C6C2399309D2A38274D89A24DD4BBDFD6976583AB5D94D4190C90624000000005F5E0DC8114D2F10EA6BAFAA38115E8180EF471241AF9DE8884"),
        ("F6637C95924A6B0C16E971A5083456EB46E88C5C4A2F3919BCCC843FD916C383", "1100722200010000250134712437000000000000000038000000000000000055EA8B2C8C220C6C2399309D2A38274D89A24DD4BBDFD6976583AB5D94D4190C9062D4D1C37937E080000000000000000000000000005553440000000000000000000000000000000000000000000000000166D82386F26FC0FFF60000000000000000000000005553440000000000309A81C25988CA31DE41B2F84ECF7008C24A95456780000000000000000000000000000000000000005553440000000000D2F10EA6BAFAA38115E8180EF471241AF9DE8884"),
        ("BADB94DC96DB2957AF0877A988A26E91B96036B6441226A8DAE48FE396F9715C", "1100612200000000240134711D25013471222D0000000155163B56DE54A554E09A31E6004CFAD5F77C794DE9F734F88F62EB74F13405A044624000000005F5E0F48114309A81C25988CA31DE41B2F84ECF7008C24A9545"),
    ]
    .into_iter()
    .map(|(index, blob)| canonical_sle(index, blob))
    .collect();
    let mut ledger = ledger_with_header(
        LedgerHeader {
            seq: 20_214_053,
            close_time: 840_995_000,
            parent_close_time: 840_994_992,
            close_time_resolution: 10,
            drops: 99_999_892_391_774_847,
            ..LedgerHeader::default()
        },
        entries,
    );
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("Clawback"),
        protocol::fix_previous_txn_id(),
    ]));

    let transaction_fixtures = [
        (
            TxType::CLAWBACK,
            0,
            "12001E2200000000240134711F201B0134713861D4D1C37937E080000000000000000000000000005553440000000000309A81C25988CA31DE41B2F84ECF7008C24A954568400000000000000C7321EDB5882D02C4F0B42905044A532B55D5114F43BFBB4A9D9E29777C68759A64F8B87440A6B86C331A1AB27EF3C42EFFE57596EA2E973F6F81B1D5FC0B45548DF0F81B2B224C8BA9F93A2B8FB313F44CC76E5B7DB1143AA4BC767DD4636B161D27C9610F8114D2F10EA6BAFAA38115E8180EF471241AF9DE8884",
            "201C00000000F8E5110061250134712455EA8B2C8C220C6C2399309D2A38274D89A24DD4BBDFD6976583AB5D94D4190C90561768F3A001B093B3453688DA92EC06148D0698BD1ED9E58A95903CC65C4E8E11E6240134711F624000000005F5E0DCE1E7228080000024013471202D00000000624000000005F5E0D08114D2F10EA6BAFAA38115E8180EF471241AF9DE8884E1E1E5110072250134712455EA8B2C8C220C6C2399309D2A38274D89A24DD4BBDFD6976583AB5D94D4190C9056F6637C95924A6B0C16E971A5083456EB46E88C5C4A2F3919BCCC843FD916C383E662D4D1C37937E0800000000000000000000000000055534400000000000000000000000000000000000000000000000001E1E722000100003700000000000000003800000000000000006280000000000000000000000000000000000000005553440000000000000000000000000000000000000000000000000166D82386F26FC0FFF60000000000000000000000005553440000000000309A81C25988CA31DE41B2F84ECF7008C24A95456780000000000000000000000000000000000000005553440000000000D2F10EA6BAFAA38115E8180EF471241AF9DE8884E1E1F1031000",
        ),
        (
            TxType::ACCOUNT_SET,
            1,
            "12000322000000002401347124201B0134713820210000000868400000000000000C7321ED6FD85AA4F87A1D6AC1E07EFAC8B71E2969C939AA3937B5275C3846B6340B8F717440E2B2E1B51F4FA5F97C59AF51E69170DEEB1C7B5EA1624C0761E45101BC44EBF8DB53CB6A845B18547F79F99CB32503C1E7FDFE169A6F0278965BDBF68A32F90681146E26A037E5F3C80945C4765A025AFFAA0BFEABFB",
            "201C00000001F8E51100612501347124559BBA13F867B7CCBDB66CCA303E68D0FBB4ECB7CBF569E7F49608E440C7C3717E56BABED78B2E77358D608B70AC304E7C83FD91D62DA4C2FF63979EC2CA98A09A84E622000000002401347124624000000005F5E100E1E7220080000024013471252D00000000624000000005F5E0F481146E26A037E5F3C80945C4765A025AFFAA0BFEABFBE1E1F1031000",
        ),
    ];

    let mut consensus_set = CanonicalTXSet::new(
        Uint256::from_hex("B92A28C0FC4EFC0AFDE393433767CE38706845907C251659F98819EEA0C7C60F")
            .expect("consensus salt"),
    );
    for (_, _, tx_blob, _) in transaction_fixtures {
        let bytes = str_unhex(tx_blob).expect("canonical transaction hex");
        consensus_set.insert(Arc::new(STTx::from_serial_iter(&mut SerialIter::new(
            &bytes,
        ))));
    }
    let ordered_consensus = consensus_set.drain_ordered();
    assert_eq!(
        ordered_consensus
            .iter()
            .map(|tx| tx.get_transaction_id().to_string())
            .collect::<Vec<_>>(),
        vec![
            "94242075DCF7A53C4E18BC77E0D9BFDCAE8A3E44DC8B1D69C9BCC5E89F053948",
            "04C55F5F2E4A36BFAB72C5E40DFB0E045B85DA38DE415A48500D66CAE87FA652",
        ],
    );

    let consensus_items = ordered_consensus
        .iter()
        .map(|tx| (tx.get_serializer().data().to_vec(), tx.get_transaction_id()))
        .collect::<Vec<_>>();
    let built = app::build_ledger_from_consensus(
        &ledger,
        LedgerHeader {
            seq: 20_214_054,
            close_time: 840_995_001,
            parent_close_time: 840_995_000,
            close_time_resolution: 10,
            // Consensus applies the set using its salted CanonicalTXSet key.
            // This is the captured set hash, not the finished ledger's
            // TransactionMd root (which the builder computes below).
            tx_hash: basics::sha_map_hash::SHAMapHash::new(
                Uint256::from_hex(
                    "B92A28C0FC4EFC0AFDE393433767CE38706845907C251659F98819EEA0C7C60F",
                )
                .expect("consensus set hash"),
            ),
            ..LedgerHeader::default()
        },
        &consensus_items,
        None,
    )
    .expect("the real consensus builder must accept the ordered canonical transaction set");
    assert_eq!(
        built.header().tx_hash.to_string(),
        "31124D868654B96DE2C2736388543436A0E1BEDFACBF8E6BB08CF9650083D71C",
        "the real builder must preserve rippled metadata and multi-transaction ordering"
    );

    let mut parent = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let rules = parent.rules();
    for (tx_type, index, tx_blob, expected_meta) in transaction_fixtures {
        let tx_bytes = str_unhex(tx_blob).expect("canonical transaction hex");
        let tx = STTx::from_serial_iter(&mut SerialIter::new(&tx_bytes));
        let tx_id = tx.get_transaction_id();
        let source = tx.get_account_id(get_field_by_symbol("sfAccount"));
        assert!(
            parent
                .read(account_keylet(raw_account_id(source)))
                .expect("read canonical source")
                .is_some(),
            "canonical parent is missing transaction source {source}"
        );
        let mut delta = ledger::FlowSandbox::new(&mut parent);
        let (result, delivered) =
            apply_submit_transactor_shell_with_delivered_amount(&mut delta, &tx, tx_type);
        assert_eq!(result, Ter::TES_SUCCESS);
        let mut meta = delta
            .apply_with_tx_meta(tx_id, 20_214_054, delivered, None, &rules)
            .expect("canonical metadata");
        let mut serializer = Serializer::default();
        meta.add_raw(&mut serializer, result, index);
        assert_eq!(
            serializer.data(),
            str_unhex(expected_meta).expect("canonical metadata hex")
        );
    }

    let mut canonical_tx_map = Ledger::new(LedgerHeader::default(), false);
    for (_, index, tx_blob, canonical_meta) in transaction_fixtures {
        let tx_bytes = str_unhex(tx_blob).expect("canonical transaction hex");
        let tx = STTx::from_serial_iter(&mut SerialIter::new(&tx_bytes));
        let tx_id = tx.get_transaction_id();
        let meta_bytes = str_unhex(canonical_meta).expect("canonical metadata hex");
        let mut meta = TxMeta::from_raw(tx_id, 20_214_054, &meta_bytes);
        let mut serializer = Serializer::default();
        meta.add_raw(&mut serializer, Ter::TES_SUCCESS, index);
        canonical_tx_map
            .raw_tx_insert(
                tx_id,
                Arc::new(Serializer::from_bytes(&tx_bytes)),
                Some(Arc::new(serializer)),
            )
            .expect("insert canonical transaction");
    }
    assert_eq!(
        canonical_tx_map
            .tx_map_mut()
            .hash()
            .as_uint256()
            .to_string(),
        "31124D868654B96DE2C2736388543436A0E1BEDFACBF8E6BB08CF9650083D71C",
        "canonical transaction leaves must reproduce rippled's transaction root"
    );
}

#[test]
fn testnet_20219759_clawback_matches_canonical_metadata_bytes() {
    let issuer = parse_base58_account_id("raM3BbP2mc6tJYcFR3GoteRFFGgnjr8nML").unwrap();
    let holder = parse_base58_account_id("rNPLnWXmPyFbreFqyqeRNUjeotVz8nLHhb").unwrap();
    let previous_tx =
        Uint256::from_hex("68A1453266C33CE029204BFAF1C666FC1C5530398E5DF967B3BE204F50824136")
            .unwrap();

    let mut issuer_root = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        account_keylet(raw_account_id(issuer)).key,
    );
    issuer_root.set_account_id(sf("sfAccount"), issuer);
    issuer_root.set_field_amount(sf("sfBalance"), test_xrp(99_999_964));
    issuer_root.set_field_u32(sf("sfFlags"), 2_155_872_256);
    issuer_root.set_field_u32(sf("sfOwnerCount"), 0);
    issuer_root.set_field_u32(sf("sfSequence"), 20_219_756);
    issuer_root.set_field_h256(sf("sfPreviousTxnID"), previous_tx);
    issuer_root.set_field_u32(sf("sfPreviousTxnLgrSeq"), 20_219_758);

    let mut holder_root = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        account_keylet(raw_account_id(holder)).key,
    );
    holder_root.set_account_id(sf("sfAccount"), holder);
    holder_root.set_field_amount(sf("sfBalance"), test_xrp(100_000_000));
    holder_root.set_field_u32(sf("sfOwnerCount"), 1);
    holder_root.set_field_u32(sf("sfSequence"), 20_219_700);

    let currency = currency_from_string("USD");
    let line_keylet = line(issuer, holder, currency);
    let iou = |mantissa, exponent, account| {
        STAmount::from_iou_amount(
            sf_generic(),
            IOUAmount::from_parts(mantissa, exponent).unwrap(),
            Issue::new(currency, account),
        )
    };
    let mut trust = STLedgerEntry::from_type_and_key(LedgerEntryType::RippleState, line_keylet.key);
    trust.set_field_amount(sf("sfBalance"), iou(-50, 0, protocol::no_account()));
    trust.set_field_amount(sf("sfLowLimit"), iou(0, 0, issuer));
    trust.set_field_amount(sf("sfHighLimit"), iou(9_999_999_999_999_990, -1, holder));
    trust.set_field_u64(sf("sfLowNode"), 0);
    trust.set_field_u64(sf("sfHighNode"), 0);
    trust.set_field_u32(sf("sfFlags"), 131_072);
    trust.set_field_h256(sf("sfPreviousTxnID"), previous_tx);
    trust.set_field_u32(sf("sfPreviousTxnLgrSeq"), 20_219_758);

    let mut ledger = ledger_with_header(
        LedgerHeader {
            seq: 20_219_758,
            close_time: 841_013_010,
            parent_close_time: 841_013_003,
            close_time_resolution: 10,
            drops: 99_999_892_353_005_477,
            ..LedgerHeader::default()
        },
        vec![issuer_root, holder_root, trust],
    );
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("Clawback"),
        protocol::fix_previous_txn_id(),
    ]));

    let tx_bytes = str_unhex("12001E2200000000240134876C201B0134878261D4D1C37937E08000000000000000000000000000555344000000000092D2B62E80BEFDD73B03638F7B722B7578C1453368400000000000000C7321ED01CF43D87AE5694196F7F21C4EF71675CB820AD687EB40685F4FCCA623D2C6907440D313567184810DEE900C439254C9E57C7AC4FE022EE76EB6A0137C54A8620339DC064121D45788B222EC44D9CAAC63B8577E1DEE74B2CA08405C198FD1C0330181143AA6F1A49777A27F91A46566E18D1B89B4D08EDE").unwrap();
    let tx = STTx::from_serial_iter(&mut SerialIter::new(&tx_bytes));
    let tx_id = tx.get_transaction_id();
    let built = app::build_ledger_from_consensus(
        &ledger,
        LedgerHeader {
            seq: 20_219_759,
            close_time: 841_013_011,
            parent_close_time: 841_013_010,
            close_time_resolution: 10,
            ..LedgerHeader::default()
        },
        &[(tx_bytes.clone(), tx_id)],
        None,
    )
    .expect("the real consensus builder must accept the canonical Clawback fixture");
    assert_eq!(
        built.header().tx_hash.to_string(),
        "1DFAEFEE57042B2B8C427D1AC975FD298BB187E6C4967E7A5263CE2A14616EB7",
        "the real consensus builder must reproduce rippled's canonical TransactionMd root"
    );
    let mut parent = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let rules = parent.rules();
    let mut delta = ledger::FlowSandbox::new(&mut parent);
    let (result, delivered) =
        apply_submit_transactor_shell_with_delivered_amount(&mut delta, &tx, TxType::CLAWBACK);
    assert_eq!(result, Ter::TES_SUCCESS);
    let mut meta = delta
        .apply_with_tx_meta(tx_id, 20_219_759, delivered, None, &rules)
        .expect("canonical metadata");
    let mut serializer = Serializer::default();
    meta.add_raw(&mut serializer, result, 0);
    assert_eq!(
        serializer.data(),
        str_unhex("201C00000000F8E5110072250134876E5568A1453266C33CE029204BFAF1C666FC1C5530398E5DF967B3BE204F508241365650B6E988397060423A07F149EECC15B3D08BDDB37FA037B4550CC55BFA49141AE66294D1C37937E0800000000000000000000000000055534400000000000000000000000000000000000000000000000001E1E722000200003700000000000000003800000000000000006280000000000000000000000000000000000000005553440000000000000000000000000000000000000000000000000166800000000000000000000000000000000000000055534400000000003AA6F1A49777A27F91A46566E18D1B89B4D08EDE67D82386F26FC0FFF6000000000000000000000000555344000000000092D2B62E80BEFDD73B03638F7B722B7578C14533E1E1E5110061250134876E5568A1453266C33CE029204BFAF1C666FC1C5530398E5DF967B3BE204F50824136568BC96739F2D895D760BB26775D8049A1D6EFEF583A7390DAD39050F569DF5E81E6240134876C624000000005F5E0DCE1E72280800000240134876D2D00000000624000000005F5E0D081143AA6F1A49777A27F91A46566E18D1B89B4D08EDEE1E1F1031000").unwrap()
    );
}

#[test]
fn testnet_20208302_ticket_create_matches_canonical_metadata_bytes() {
    // Exact parent objects and transaction from Testnet ledger 20,208,302.
    // This fixture pins the transaction arithmetic and complete metadata
    // independently of the online-delete MissingNode regression observed at
    // the same transaction.
    let entries = [
        ("A1E4CAF1CA3C39F01702F3169EC3DC5A5A3D0F135C7EC45C1812E0EEC81E4B68", "1100612200000000240128BFCA2501345AAC2D0000001A2028000000145505051553864DE1BB81231C4E214013FB72E06AFB217B28B049D5B3BF1495314A62400000032636C9978114F73367B0DE7D54EAAA2A121E5AC3A4C2DC384A31"),
        ("86EFD02B1D338D777E4ED6905985D1DDFDEE645EE969A8FDB5355DA57BE83D1A", "11006422000000002501345A9C310000000000002B28320000000000002B29553A2C40E948214AD7C115F1C0064DC8A5EA23EC86123A78F813BB1849BDE9928C5886EFD02B1D338D777E4ED6905985D1DDFDEE645EE969A8FDB5355DA57BE83D1A8214F73367B0DE7D54EAAA2A121E5AC3A4C2DC384A310113406CCF3EA6A7CA4EDD8ED289987EA0436DBF210B7EC978B8D3D169F75410E629C9AD0D156226831E98AA23CC43FB0EB5EEEAC8B524F4DBA03D0D0E2906D800596E"),
        ("DE409FDF9131EEDBB93AB574E9403200A718FE5985FCF0C331454F603A0BB2FD", "11006422000000002501345AAC320000000000002B285505051553864DE1BB81231C4E214013FB72E06AFB217B28B049D5B3BF1495314A5886EFD02B1D338D777E4ED6905985D1DDFDEE645EE969A8FDB5355DA57BE83D1A8214F73367B0DE7D54EAAA2A121E5AC3A4C2DC384A310113C19F143F1A334651ABB3CD0E019A291BE16723C43A31835002B548C5E992CCDA749219755F42E55BC2AE62A007D67A0A32C550E64B664BF598DCD1313DEB2ECA1A172F29FB2C37CAEC83F82003FD945455F210E0490DCE379F0295789A8112D8DF6A30B0B3C2F7F6FAB5A98DFE3A956CE619D97BA392CC68E9CB5BF2B46B93C382553E9FE2E628BD38ECB9439FCE877F4C3C99C9684C6E0644554FE87FC54DA4306D5B2A9D293D5604A0AA679488336317E80217DF76E6E3C9E15BDC72834CF12799697A47E9D54C13E96DAC9B4805DB7B49A40EAFF545F935B876A691A370333ADB8ED4C1F15E3479979C8E376AF5570E27153A75BF7FBF9A46D7478AF0F8090BD4A0C92FF052004B5AF250B51A7E666A264344A37DE26F16F960BA1DF5B889925CBC23C2746BE85260385F4480B84FF838C3BA2BEB68F19C63802E9FAB8CAC31FFECEFF2D4AF9E44050F23A1CBE10B682ECA23D43CCC9FDD8C906C6BABA37B41DC"),
    ]
    .into_iter()
    .map(|(index, blob)| canonical_sle(index, blob))
    .collect();
    let mut ledger = ledger_with_header(
        LedgerHeader {
            seq: 20_208_301,
            parent_close_time: 840_976_700,
            drops: 100_000_000_000,
            ..LedgerHeader::default()
        },
        entries,
    );
    ledger.set_rules(protocol::Rules::new([protocol::fix_previous_txn_id()]));
    let tx_bytes = str_unhex("12000A23012347EC240128BFCA201B01345AC020280000001268400000000000001E7321ED3978DE2D2BC69F2D22E0277CB7812909AB240EA40BBFAAFEC92252438AE4CFBD7440238450A4BBD8C3AF16344ECAF93F93E4A20F2EBF4F8F73486E7C2B26DAAA2CAA292C25B6EEF394B7274478EB0D2E930999797B6C2E09DB03CF1279FCEE8B26048114F73367B0DE7D54EAAA2A121E5AC3A4C2DC384A31").expect("canonical transaction hex");
    let tx = STTx::from_serial_iter(&mut SerialIter::new(&tx_bytes));
    let tx_id = tx.get_transaction_id();
    let mut expected_tx_id = Uint256::default();
    assert!(
        expected_tx_id
            .parse_hex("9618EBEC428A45CC3E3A48E961C4BF1458AF1728D21E1C52C72EC680F9A6DD5F")
    );
    assert_eq!(tx_id, expected_tx_id);
    let mut parent = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let rules = parent.rules();
    let mut delta = ledger::FlowSandbox::new(&mut parent);
    let (result, delivered) =
        apply_submit_transactor_shell_with_delivered_amount(&mut delta, &tx, TxType::TICKET_CREATE);
    assert_eq!(result, Ter::TES_SUCCESS);
    let mut meta = delta
        .apply_with_tx_meta(tx_id, 20_208_302, delivered, None, &rules)
        .expect("canonical metadata");
    let mut serializer = Serializer::default();
    meta.add_raw(&mut serializer, result, 2);
    assert_eq!(
        format!("{:x}", Sha256::digest(serializer.data())),
        "69b2017f526b83600a78aabc8e91257428f3a29fa57380affc91215dfdf37849"
    );
}

#[test]
fn testnet_20207451_mpt_escrow_finish_matches_canonical_metadata_bytes() {
    // Exact parent objects and transaction from Testnet ledger 20,207,451.
    // This pins the complete MPT EscrowFinish state/metadata path that caused
    // an incompatible local child, including both owner directories, reserve
    // transfer, MPToken creation, transfer-fee rounding and threading.
    let entries = [
        ("09C1997589E8DF4F873B9C5D40016DC1974B56CC85294D22E2F521C7BF09A185", "1100642200000000250134575655125ED416F011D2E422D9F74FD3547D882D41177B35B8A2CF6DE0DC4E149BFE3F5809C1997589E8DF4F873B9C5D40016DC1974B56CC85294D22E2F521C7BF09A1858214D60941EB40688B0398EFED931713B28D82014DD501132068880A429021D50B75CEDBD18D2F4668B2EB820F47A115F256ED6E61492246B4"),
        ("2CF863A234B6C0CD2D2C7925590A7BC6A0C33EA7FD8E1E0466BCD82B58B59E71", "1100612200000000240134575425013457562D0000000255125ED416F011D2E422D9F74FD3547D882D41177B35B8A2CF6DE0DC4E149BFE3F624000000005F5E0E78114928D967C63DBF9CE168429A33A371940E19007F0"),
        ("3B50FDFC525FCBE0957F5FD1EF58DB93EE0E3834EC9505B6130D3A0FC623FEA3", "1100642200000000250134575655125ED416F011D2E422D9F74FD3547D882D41177B35B8A2CF6DE0DC4E149BFE3F583B50FDFC525FCBE0957F5FD1EF58DB93EE0E3834EC9505B6130D3A0FC623FEA38214928D967C63DBF9CE168429A33A371940E19007F001134068880A429021D50B75CEDBD18D2F4668B2EB820F47A115F256ED6E61492246B4C1DE342956EDF26FAF3BD37FA7651F3F72ECE4DAED2B0F744247D0B5A84D15E9"),
        ("58B06B27D5BC0247468D409B34A4AAD355C7A80709DBC1E5DA7B3A5D7EB79356", "1100612200000000240134575225013457562D0000000055125ED416F011D2E422D9F74FD3547D882D41177B35B8A2CF6DE0DC4E149BFE3F624000000005F5E1008114D60941EB40688B0398EFED931713B28D82014DD5"),
        ("68880A429021D50B75CEDBD18D2F4668B2EB820F47A115F256ED6E61492246B4", "1100752200000000240134575325013457562B3BAA0C40202432203E79202532203E1A34000000000000000039000000000000000055125ED416F011D2E422D9F74FD3547D882D41177B35B8A2CF6DE0DC4E149BFE3F616000000000000027100134575206B21C54497DF487B71A779F8953A5020D0853AD8114928D967C63DBF9CE168429A33A371940E19007F08314D60941EB40688B0398EFED931713B28D82014DD5"),
        ("717291784C050956DE8657E039D6A20140C038FE910F4BD2CCECFB77B71C5D72", "11007E14006422000000282401345752250134575634000000000000000030187FFFFFFFFFFFFFFF301900000000000186A0301D000000000000271055125ED416F011D2E422D9F74FD3547D882D41177B35B8A2CF6DE0DC4E149BFE3F701E02ABCD841406B21C54497DF487B71A779F8953A5020D0853AD051002"),
        ("C1DE342956EDF26FAF3BD37FA7651F3F72ECE4DAED2B0F744247D0B5A84D15E9", "11007F22000000002501345756340000000000000000301A0000000000015F90301D000000000000271055125ED416F011D2E422D9F74FD3547D882D41177B35B8A2CF6DE0DC4E149BFE3F8114928D967C63DBF9CE168429A33A371940E19007F001150134575206B21C54497DF487B71A779F8953A5020D0853AD"),
    ]
    .into_iter()
    .map(|(index, blob)| canonical_sle(index, blob))
    .collect::<Vec<_>>();

    let mut ledger = ledger_with_header(
        LedgerHeader {
            seq: 20_207_450,
            parent_close_time: 840_973_860,
            drops: 100_000_000_000,
            ..LedgerHeader::default()
        },
        entries,
    );
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("TokenEscrow"),
        protocol::feature_id("Sponsor"),
        protocol::fix_previous_txn_id(),
        protocol::feature_id("fixTokenEscrowV1"),
        protocol::feature_id("fixCleanup3_1_3"),
        protocol::feature_id("fixCleanup3_4_0"),
    ]));
    let tx_bytes = str_unhex("120002240134575220190134575368400000000000000A7321EDE4CF89B3718B1A57E4CB53E990B7693995EB551CB72038EF00A334351D7169EF74407EFB1AB1610919818E45CC601C936E6A02165DF42DE909ACAB4CB4FF21937CE98E10F4BB203931D3A07ABD40267E58CAFA363C76DA5490982A6BE3E625D2DF048114D60941EB40688B0398EFED931713B28D82014DD58214928D967C63DBF9CE168429A33A371940E19007F0").expect("canonical transaction hex");
    let tx = STTx::from_serial_iter(&mut SerialIter::new(&tx_bytes));
    let tx_id = tx.get_transaction_id();
    let mut parent = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let rules = parent.rules();
    let mut delta = ledger::FlowSandbox::new(&mut parent);
    let (result, delivered) =
        apply_submit_transactor_shell_with_delivered_amount(&mut delta, &tx, TxType::ESCROW_FINISH);
    assert_eq!(result, Ter::TES_SUCCESS);
    let mut meta = delta
        .apply_with_tx_meta(tx_id, 20_207_451, delivered, None, &rules)
        .expect("canonical metadata");
    let mut serializer = Serializer::default();
    meta.add_raw(&mut serializer, result, 3);
    assert_eq!(
        format!("{:x}", Sha256::digest(serializer.data())),
        "2eb437973fba87ed6981e8dd3eee37c0561928ed5906741738197e118b90ea5f"
    );
}

#[test]
fn testnet_20207451_ticket_payment_matches_canonical_metadata_bytes() {
    let entries = [
        ("30863A1FA4C1F456E94EBDFEBA293AEF1BD89FA5A7C5A8AAD3538BB1A87D61BA", "11006122200000002400B18B72250134575A2D000000B32028000000B355C46E21A762B248C3ED5793417077E71CD3E305CDACE949E3D89A70D6AA54ECB062402C49E43197D8F38114C2796AE9913E1229D03ED885A85B5AA2AA88CC8F"),
        ("4A4833D6A2F3B81576E16115C5728F312A66564C62B7B9987DEEBA04535F87FA", "11006122000000002400ED3806250134575A2D0000000055C46E21A762B248C3ED5793417077E71CD3E305CDACE949E3D89A70D6AA54ECB062400002F66F8C192C811429F2FD277133712E9566EDE23FF5EBC6B5D1117A"),
        ("688815D03089EDD2DC7F52AAA8EE71F4177047BB693EB6C2220FF0FFD48255AC", "1100642200000000250134575831000000000001AC6632000000000001AC645554A3C699351617B9E04029BBCDB70E570D0338D6A8603B941919CDD86F48A014585B4DA4491AB798C0D44E6FB1BA332CBBDCD572141F6FF184A21CE2E6EBA78F548214C2796AE9913E1229D03ED885A85B5AA2AA88CC8F0113C23FBC4E8EA3F5859FE28F965FBC9D7921A50CC32283B847AB1B0BB4D42D3F9E3DEEC45FA2CB67ADD89AF678285837E31AC67817D3B719DA2C5F2D2B01322D36B936C8E79AF4B3EDF254524DC55C7D8E049BE1B47CD5F77AF50DB081D5AA76286A52CB0FA0559CC7ED398A1852E4389518F39FEBC187D09141A9BEA292D9B714D010D031F8C87BE01C0A092028C99B916C5B863762CC56001274BE4EC3EA4A2620F3D1FBC955ACC03C7F0A2F2153F4E404EC3BB0B6660A2C72D529460AD12D807CDFD2E4E99BECDA1611D59D3CFAD720F4A94A84583946CB95DEB4D3955184E96142D6666970B8B701C3618A9EC66533B7E1A23D395B8908966AE3D90DA06D5E0A12E209D21F98EC184136CAC546D74B3B27D5353E38CFE67F3DB2C0F55502EE339CE34CE577B7A3D973B5E4FC851FBC1F9FA6BDED46669449A0671EE56B93AF4F4BE3D610688B6DF9B889B3423614BC5A4069A399083EA1C8D134FA28068E0543D9EA42F6D4710CFD52752CF84BB92F66FFECE1CB6AE1E01D044529A7908FA333F4F72EF94AC490F90713F214F7DB4CFBEEF7C004333A5A5C6A81DFA22243D9FFABF8698C5CA2905F7D7D9D10E55AF19DF079659E44B01C90BE021CF33446C71FABFD28FEB20588362325408793836C7F43860A23C77EF6A06BC911F27D0A25C2C1FE7BC07159634ADB206A8D4810BAA6F6A9F3C1B162E221E986043F4A2ECD67DA"),
        ("BC4E8EA3F5859FE28F965FBC9D7921A50CC32283B847AB1B0BB4D42D3F9E3DEE", "11005422000000002501345693202900B18A9734000000000001AC655512B430F4BAC937B9975D9DA2856837750BB988AC376BDB4B1715CF6F3B5A6C9E8114C2796AE9913E1229D03ED885A85B5AA2AA88CC8F"),
    ]
    .into_iter()
    .map(|(index, blob)| canonical_sle(index, blob))
    .collect();
    let mut ledger = ledger_with_header(
        LedgerHeader {
            seq: 20_207_450,
            parent_close_time: 840_973_860,
            drops: 100_000_000_000,
            ..LedgerHeader::default()
        },
        entries,
    );
    ledger.set_rules(protocol::Rules::new([protocol::fix_previous_txn_id()]));
    let tx_bytes = str_unhex("12000022000000002400000000201B0134576D202900B18A97614000000005F5E10068400000000000000C7321EDA3952ACD931CCA26CC02AEA89037FCFD69821C428C8C3B6AB7A8E73C13E6926E7440D0E8F47229FE9794DEE827098DDA03009A803EFA6808C2E3426827E0DE90928DFD297C1CE10A7C9810F18A802A185278ED6DEB0BA8A778F6BF0BF9AEFDAA52088114C2796AE9913E1229D03ED885A85B5AA2AA88CC8F831429F2FD277133712E9566EDE23FF5EBC6B5D1117A").expect("canonical transaction hex");
    let tx = STTx::from_serial_iter(&mut SerialIter::new(&tx_bytes));
    let tx_id = tx.get_transaction_id();
    let mut parent = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let rules = parent.rules();
    let mut delta = ledger::FlowSandbox::new(&mut parent);
    let (result, delivered) =
        apply_submit_transactor_shell_with_delivered_amount(&mut delta, &tx, TxType::PAYMENT);
    assert_eq!(result, Ter::TES_SUCCESS);
    let mut meta = delta
        .apply_with_tx_meta(tx_id, 20_207_451, delivered, None, &rules)
        .expect("canonical metadata");
    let mut serializer = Serializer::default();
    meta.add_raw(&mut serializer, result, 2);
    assert_eq!(
        format!("{:x}", Sha256::digest(serializer.data())),
        "8cb82ed3e21b02c7bc0057c8f8fbe4c96d84c1430c197390f720d2778800e1e0"
    );
}

#[test]
fn testnet_20207451_offer_cancel_matches_canonical_metadata_bytes() {
    let entries = [
        ("2EA77F69A44AF96749727D300D45F78E2C4E8F648A59161B5017C79CA7B2F0BE", "110064220000000025013456F2365017C79CA7B2F0BE5586D749BB64D5301C3AD8FBBD4EE83BC375FE324A9A62FF430A174FF7C5ACA6CC582EA77F69A44AF96749727D300D45F78E2C4E8F648A59161B5017C79CA7B2F0BE011100000000000000000000000055414800000000000211EDD6165952C4DFE6E73AE99FAB2D8C4BAA261D6A0311000000000000000000000000000000000000000004110000000000000000000000000000000000000000011320DDCF138E2EB432D54D95FBA1B7AA732E64F56F1D2004D7DE238653A9D6692772"),
        ("6F5B8631CB9B4B884B8FAD6DAB7E11D3188DC6DDF039855C328664E49902ED10", "1100642200000000250134575955DE4E919CCE8A089DC06BB6AB3DA2BE972DE769BC742E08A843F5327B2F9A2AA7586F5B8631CB9B4B884B8FAD6DAB7E11D3188DC6DDF039855C328664E49902ED1082147CCA603AD1D6A0558536E3C35DC3ADD7F8E33D0A0113A01C635B6813FD5040B7815B10A426F75757ED65A280C4C0A3D99C11D2DC5025DC874FD21D489AD7AD3829F5725349283568872E8DF2E47C8391D2E4CA3B14E1849A718A813C8A801BE9741558308DD6F47313582D3CC9DB10ACB56D4C55F80220DDCF138E2EB432D54D95FBA1B7AA732E64F56F1D2004D7DE238653A9D6692772E221A56D7DF2D15E7A258C502F4D3A5080A2803DF647C86B57B54D0186EA478A"),
        ("DDCF138E2EB432D54D95FBA1B7AA732E64F56F1D2004D7DE238653A9D6692772", "11006F220000000024011E979425013456F23300000000000000003400000000000000005586D749BB64D5301C3AD8FBBD4EE83BC375FE324A9A62FF430A174FF7C5ACA6CC50102EA77F69A44AF96749727D300D45F78E2C4E8F648A59161B5017C79CA7B2F0BE64D511C37937E080000000000000000000000000005541480000000000EDD6165952C4DFE6E73AE99FAB2D8C4BAA261D6A65400000000071FBDD81147CCA603AD1D6A0558536E3C35DC3ADD7F8E33D0A"),
        ("FC1FDB3493E58C6324E5898BEA1B09F1857FC5C6745D9157CD896D27F2ACBD01", "110061220000000024011E979B25013457592D0000000555DE4E919CCE8A089DC06BB6AB3DA2BE972DE769BC742E08A843F5327B2F9A2AA762400000000FFC9B4781147CCA603AD1D6A0558536E3C35DC3ADD7F8E33D0A"),
    ]
    .into_iter()
    .map(|(index, blob)| canonical_sle(index, blob))
    .collect();
    let mut ledger = ledger_with_header(
        LedgerHeader {
            seq: 20_207_450,
            parent_close_time: 840_973_860,
            drops: 100_000_000_000,
            ..LedgerHeader::default()
        },
        entries,
    );
    ledger.set_rules(protocol::Rules::new([protocol::fix_previous_txn_id()]));
    let tx_bytes = str_unhex("120008220000000024011E979B2019011E9794201B0134576D68400000000000000C7321EDEC6E407C5B9FE4D4270A49B960B14C6DD27A939F16EE3F189DAF43268E2476277440F1919473E8FFF6BA3126B5516EAEB3FCCBCE1069292E1AD6592C1948B443C0FCC79D1CED3C09399FF771700C5F99077CA16EAAFA73654D2E041C924EFEF4630081147CCA603AD1D6A0558536E3C35DC3ADD7F8E33D0A").expect("canonical transaction hex");
    let tx = STTx::from_serial_iter(&mut SerialIter::new(&tx_bytes));
    let tx_id = tx.get_transaction_id();
    let mut parent = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let rules = parent.rules();
    let mut delta = ledger::FlowSandbox::new(&mut parent);
    let (result, delivered) =
        apply_submit_transactor_shell_with_delivered_amount(&mut delta, &tx, TxType::OFFER_CANCEL);
    assert_eq!(result, Ter::TES_SUCCESS);
    let mut meta = delta
        .apply_with_tx_meta(tx_id, 20_207_451, delivered, None, &rules)
        .expect("canonical metadata");
    let mut serializer = Serializer::default();
    meta.add_raw(&mut serializer, result, 0);
    assert_eq!(
        format!("{:x}", Sha256::digest(serializer.data())),
        "3ddd6e05bd6143831a08c479ef903e17d7bd9cb849d56c93895b81d3da26e78c"
    );
}

#[test]
fn escrow_finish_iou_unlocks_live_path_with_receiver_line_rules() {
    let owner = sample_account(0x71);
    let destination = sample_account(0x72);
    let issuer = sample_account(0x73);
    let currency = currency_from_string("USD");
    let amount = STAmount::from_iou_amount(
        sf("sfAmount"),
        IOUAmount::from_parts(100, 0).expect("escrow amount"),
        Issue::new(currency, issuer),
    );
    let escrow_keylet = protocol::escrow_keylet(raw_account_id(owner), 1);
    let escrow = || {
        let mut entry =
            STLedgerEntry::from_type_and_key(LedgerEntryType::Escrow, escrow_keylet.key);
        entry.set_account_id(sf("sfAccount"), owner);
        entry.set_account_id(sf("sfDestination"), destination);
        entry.set_field_amount(sf("sfAmount"), amount.clone());
        entry.set_field_u64(sf("sfOwnerNode"), 0);
        entry
    };
    let finish = |submitter| {
        STTx::new(TxType::ESCROW_FINISH, |tx| {
            tx.set_account_id(sf("sfAccount"), submitter);
            tx.set_account_id(sf("sfOwner"), owner);
            tx.set_field_u32(sf("sfOfferSequence"), 1);
            tx.set_field_amount(
                sf("sfFee"),
                STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
            );
            tx.set_field_u32(sf("sfSequence"), 1);
        })
    };

    let receiver_ledger = empty_ledger(vec![
        account_root(owner, 1, 0),
        account_root(destination, 0, 0),
        account_root(issuer, 0, 0),
        owner_dir_root(owner, escrow_keylet.key),
        escrow(),
    ]);
    let mut receiver_view = ApplyViewImpl::new(Arc::new(receiver_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut receiver_view,
            &finish(destination),
            TxType::ESCROW_FINISH,
            Some(1_000_000),
        ),
        Ter::TES_SUCCESS
    );
    let receiver_line = receiver_view
        .read(protocol::line(destination, issuer, currency))
        .expect("receiver line read")
        .expect("the destination may create its zero-limit line while finishing the escrow");
    // Destination sorts low and issuer sorts high. Canonical trustCreate
    // reserves the destination's low side and applies both accounts' default
    // NoRipple setting. This is the exact metadata field that diverged in the
    // live incompatible child at ledger 20,189,822.
    assert_eq!(receiver_line.get_field_u32(sf("sfFlags")), 0x0031_0000);
    assert_eq!(
        receiver_line.get_field_amount(sf("sfBalance")).iou(),
        amount.iou()
    );
    assert_eq!(
        receiver_line
            .get_field_amount(sf("sfBalance"))
            .issue()
            .account,
        protocol::no_account(),
        "payment-created RippleState balances use rippled's neutral issuer"
    );
    assert_eq!(
        receiver_view
            .read(account_keylet(raw_account_id(destination)))
            .expect("destination account read")
            .expect("destination account exists")
            .get_field_u32(sf("sfOwnerCount")),
        1
    );

    let owner_no_line_ledger = empty_ledger(vec![
        account_root(owner, 1, 0),
        account_root(destination, 0, 0),
        account_root(issuer, 0, 0),
        owner_dir_root(owner, escrow_keylet.key),
        escrow(),
    ]);
    let mut owner_no_line_view =
        ApplyViewImpl::new(Arc::new(owner_no_line_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut owner_no_line_view,
            &finish(owner),
            TxType::ESCROW_FINISH,
            Some(1_000_000),
        ),
        Ter::TEC_NO_LINE
    );

    let mut limited_line = trust_line_entry_iou(
        destination,
        issuer,
        currency,
        IOUAmount::from_parts(0, 0).expect("line balance"),
    );
    limited_line.set_field_amount(
        sf("sfLowLimit"),
        STAmount::from_iou_amount(
            sf("sfLowLimit"),
            IOUAmount::from_parts(50, 0).expect("receiver limit"),
            Issue::new(currency, destination),
        ),
    );
    let limited_ledger = empty_ledger(vec![
        account_root(owner, 1, 0),
        account_root(destination, 1, 0),
        account_root(issuer, 0, 0),
        owner_dir_root(owner, escrow_keylet.key),
        escrow(),
        limited_line,
    ]);
    let mut limited_view = ApplyViewImpl::new(Arc::new(limited_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut limited_view,
            &finish(owner),
            TxType::ESCROW_FINISH,
            Some(1_000_000),
        ),
        Ter::TEC_LIMIT_EXCEEDED
    );
}

fn check_entry(
    source: AccountID,
    destination: AccountID,
    sequence: u32,
    send_max: STAmount,
) -> STLedgerEntry {
    let keylet = protocol::check_keylet(raw_account_id(source), sequence);
    let mut entry = STLedgerEntry::new(keylet);
    entry.set_account_id(get_field_by_symbol("sfAccount"), source);
    entry.set_account_id(get_field_by_symbol("sfDestination"), destination);
    entry.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
    entry.set_field_amount(get_field_by_symbol("sfSendMax"), send_max);
    entry.set_field_u64(get_field_by_symbol("sfOwnerNode"), 0);
    entry.set_field_u64(get_field_by_symbol("sfDestinationNode"), 0);
    entry
}

#[test]
fn amm_clawback_last_lp_reconciliation_tracks_fix_amm_clawback_rounding() {
    let issuer = sample_account(0x11);
    let holder = sample_account(0x22);
    let amm_account = sample_account(0x33);
    let usd = Issue::new(currency_from_string("USD"), issuer);
    let eur = Issue::new(currency_from_string("EUR"), issuer);
    let lp_currency = amm_lpt_currency(usd.currency, eur.currency);

    let build = |holder_lp: i64, rounding_enabled: bool| {
        let amm = amm_entry(amm_account, usd, eur, 1_000_000, Vec::new(), 0);
        let lp_line = trust_line_entry_iou(
            holder,
            amm_account,
            lp_currency,
            IOUAmount::from_parts(holder_lp, 0).expect("LP balance"),
        );
        let usd_pool_line = trust_line_entry_iou(
            issuer,
            amm_account,
            usd.currency,
            IOUAmount::from_parts(-1_000_000, 0).expect("USD pool balance"),
        );
        let eur_pool_line = trust_line_entry_iou(
            issuer,
            amm_account,
            eur.currency,
            IOUAmount::from_parts(-1_000_000, 0).expect("EUR pool balance"),
        );
        let mut ledger = empty_ledger(vec![
            account_root(issuer, 0, lsfAllowTrustLineClawback),
            account_root(holder, 0, 0),
            account_root(amm_account, 0, 0),
            owner_dir_root_with_children(
                amm_account,
                vec![
                    *amm.key(),
                    *lp_line.key(),
                    *usd_pool_line.key(),
                    *eur_pool_line.key(),
                ],
            ),
            owner_dir_root(holder, *lp_line.key()),
            owner_dir_root_with_children(issuer, vec![*usd_pool_line.key(), *eur_pool_line.key()]),
            amm,
            lp_line,
            usd_pool_line,
            eur_pool_line,
            trust_line_entry_iou(
                issuer,
                holder,
                usd.currency,
                IOUAmount::from_parts(0, 0).expect("USD holder balance"),
            ),
            trust_line_entry_iou(
                issuer,
                holder,
                eur.currency,
                IOUAmount::from_parts(0, 0).expect("EUR holder balance"),
            ),
        ]);
        let mut features = vec![protocol::feature_id("fixAMMv1_3")];
        if rounding_enabled {
            features.push(protocol::feature_id("fixAMMClawbackRounding"));
        }
        ledger.set_rules(protocol::Rules::new(features));
        ledger
    };

    let clawback = || {
        STTx::new(TxType::AMM_CLAWBACK, |tx| {
            tx.set_account_id(sf("sfAccount"), issuer);
            tx.set_account_id(sf("sfHolder"), holder);
            tx.set_field_issue(
                sf("sfAsset"),
                STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(usd)),
            );
            tx.set_field_issue(
                sf("sfAsset2"),
                STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(eur)),
            );
            tx.set_field_amount(
                sf("sfFee"),
                STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
            );
            tx.set_field_u32(sf("sfSequence"), 1);
        })
    };

    let amm_keylet = protocol::keylet::amm(Asset::Issue(usd), Asset::Issue(eur));

    // Before the amendment, the AMM's rounded LP total wins and a one-token
    // dust balance survives even though this is the only liquidity provider.
    let mut legacy_view = ApplyViewImpl::new(Arc::new(build(999_999, false)), ApplyFlags::NONE);
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut legacy_view, &clawback(), TxType::AMM_CLAWBACK),
        Ter::TES_SUCCESS
    );
    let legacy_amm = legacy_view
        .read(amm_keylet)
        .expect("legacy AMM read")
        .expect("legacy AMM survives");
    assert_eq!(
        legacy_amm.get_field_amount(sf("sfLPTokenBalance")).iou(),
        IOUAmount::from_parts(1, 0).expect("one LP dust token")
    );

    // With the fix, a mismatch strictly below 0.1% is reconciled to the
    // holder's LP trust-line balance before withdrawal, so the AMM is empty.
    let mut fixed_view = ApplyViewImpl::new(Arc::new(build(999_999, true)), ApplyFlags::NONE);
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut fixed_view, &clawback(), TxType::AMM_CLAWBACK),
        Ter::TES_SUCCESS
    );
    assert!(
        fixed_view
            .read(amm_keylet)
            .expect("fixed AMM read")
            .is_none(),
        "the reconciled last-provider clawback must delete the empty AMM"
    );

    // Larger discrepancies are invalid rather than silently reconciling.
    let mut invalid_view = ApplyViewImpl::new(Arc::new(build(990_000, true)), ApplyFlags::NONE);
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut invalid_view, &clawback(), TxType::AMM_CLAWBACK),
        Ter::TEC_AMM_INVALID_TOKENS
    );
}

#[test]
fn amm_clawback_matching_amount_rounds_only_with_fix_amm_clawback_rounding() {
    let issuer = sample_account(0x41);
    let holder = sample_account(0x42);
    let amm_account = sample_account(0x43);
    let usd = Issue::new(currency_from_string("USD"), issuer);
    let eur = Issue::new(currency_from_string("EUR"), issuer);
    let lp_currency = amm_lpt_currency(usd.currency, eur.currency);
    let lp_before = IOUAmount::from_parts(2_795_084_971_874_737, -12).expect("LP before");

    let build = |rounding_enabled: bool| {
        let mut amm = amm_entry(amm_account, usd, eur, 1, Vec::new(), 0);
        amm.set_field_amount(
            sf("sfLPTokenBalance"),
            STAmount::from_iou_amount(
                sf("sfLPTokenBalance"),
                lp_before,
                Issue::new(lp_currency, amm_account),
            ),
        );
        let lp_line = trust_line_entry_iou(holder, amm_account, lp_currency, lp_before);
        let usd_pool_line = trust_line_entry_iou(
            issuer,
            amm_account,
            usd.currency,
            IOUAmount::from_parts(-2_500, 0).expect("USD pool balance"),
        );
        let eur_pool_line = trust_line_entry_iou(
            issuer,
            amm_account,
            eur.currency,
            IOUAmount::from_parts(-3_125, 0).expect("EUR pool balance"),
        );
        let mut ledger = empty_ledger(vec![
            account_root(issuer, 0, lsfAllowTrustLineClawback),
            account_root(holder, 0, 0),
            account_root(amm_account, 0, 0),
            owner_dir_root_with_children(
                amm_account,
                vec![
                    *amm.key(),
                    *lp_line.key(),
                    *usd_pool_line.key(),
                    *eur_pool_line.key(),
                ],
            ),
            amm,
            lp_line,
            usd_pool_line,
            eur_pool_line,
            trust_line_entry_iou(
                issuer,
                holder,
                usd.currency,
                IOUAmount::from_parts(0, 0).expect("USD holder balance"),
            ),
            trust_line_entry_iou(
                issuer,
                holder,
                eur.currency,
                IOUAmount::from_parts(0, 0).expect("EUR holder balance"),
            ),
        ]);
        let mut features = vec![protocol::feature_id("fixAMMv1_3")];
        if rounding_enabled {
            features.push(protocol::feature_id("fixAMMClawbackRounding"));
        }
        ledger.set_rules(protocol::Rules::new(features));
        ledger
    };

    let clawback = STTx::new(TxType::AMM_CLAWBACK, |tx| {
        tx.set_account_id(sf("sfAccount"), issuer);
        tx.set_account_id(sf("sfHolder"), holder);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(usd)),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(eur)),
        );
        tx.set_field_amount(
            sf("sfAmount"),
            STAmount::from_iou_amount(
                sf("sfAmount"),
                IOUAmount::from_parts(1, 0).expect("one USD"),
                usd,
            ),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });
    let amm_keylet = protocol::keylet::amm(Asset::Issue(usd), Asset::Issue(eur));

    for (rounding_enabled, expected_lp) in [
        (
            false,
            IOUAmount::from_parts(2_793_966_937_885_987, -12).expect("legacy LP"),
        ),
        (
            true,
            IOUAmount::from_parts(2_793_966_937_885_988, -12).expect("amended LP"),
        ),
    ] {
        let mut view = ApplyViewImpl::new(Arc::new(build(rounding_enabled)), ApplyFlags::NONE);
        assert_eq!(
            dispatch_with_pre_fee_balance(&mut view, &clawback, TxType::AMM_CLAWBACK),
            Ter::TES_SUCCESS
        );
        let amm = view
            .read(amm_keylet)
            .expect("AMM read")
            .expect("AMM remains after partial clawback");
        assert_eq!(
            amm.get_field_amount(sf("sfLPTokenBalance")).iou(),
            expected_lp
        );
    }
}

#[test]
fn mptoken_authorize_dispatch_uses_h192_id_and_sets_token_issuance_id() {
    let issuer = sample_account(0xC1);
    let holder = sample_account(0xC2);
    let mpt_id = share_id_for(issuer, 1);
    let ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        account_root_with_balance(holder, 0, 0, 1_000_000),
        mpt_issuance_entry(issuer, 1, 0, protocol::lsfMPTCanTransfer),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_AUTHORIZE, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), holder);
        object.set_field_h192(get_field_by_symbol("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = dispatch_with_pre_fee_balance(&mut view, &tx, TxType::MPTOKEN_AUTHORIZE);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(holder),
        ))
        .expect("token read should succeed")
        .expect("holder token should exist");
    assert_eq!(
        token.get_field_h192(get_field_by_symbol("sfMPTokenIssuanceID")),
        mpt_id
    );
    assert_eq!(token.get_field_u64(get_field_by_symbol("sfMPTAmount")), 0);
}

#[test]
fn mptoken_authorize_dispatch_deletes_zero_token_after_issuance_destroyed() {
    let holder = sample_account(0xC8);
    let issuer = sample_account(0xC9);
    let mpt_id = share_id_for(issuer, 1);
    let token = mptoken_entry(holder, mpt_id, 0);
    let ledger = empty_ledger(vec![
        account_root(holder, 1, 0),
        owner_dir_root(holder, *token.key()),
        token,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_AUTHORIZE, |object| {
        object.set_account_id(sf("sfAccount"), holder);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(sf("sfFlags"), protocol::tfMPTUnauthorize);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &tx, TxType::MPTOKEN_AUTHORIZE),
        protocol::Ter::TES_SUCCESS
    );
    assert!(
        view.read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(holder)
        ))
        .expect("token read should succeed")
        .is_none()
    );
    let holder_root = view
        .read(account_keylet(raw_account_id(holder)))
        .expect("holder read should succeed")
        .expect("holder should remain");
    assert_eq!(holder_root.get_field_u32(sf("sfOwnerCount")), 0);
}

#[test]
fn mptoken_authorize_dispatch_rejects_locked_amount_without_issuance() {
    let holder = sample_account(0xCA);
    let issuer = sample_account(0xCB);
    let mpt_id = share_id_for(issuer, 1);
    let mut token = mptoken_entry(holder, mpt_id, 0);
    token.set_field_u64(sf("sfLockedAmount"), 1);
    let mut ledger = empty_ledger(vec![account_root(holder, 1, 0), token]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_1_3"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_AUTHORIZE, |object| {
        object.set_account_id(sf("sfAccount"), holder);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(sf("sfFlags"), protocol::tfMPTUnauthorize);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        apply_simulated_transaction(&mut view, &tx).0,
        protocol::Ter::TEF_INTERNAL
    );
    assert!(
        view.read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(holder)
        ))
        .expect("token read should succeed")
        .is_some()
    );
}

#[test]
fn mptoken_authorize_pre_cleanup_313_ignores_locked_amount_on_delete() {
    let holder = sample_account(0xCC);
    let issuer = sample_account(0xCD);
    let mpt_id = share_id_for(issuer, 1);
    let mut token = mptoken_entry(holder, mpt_id, 0);
    token.set_field_u64(sf("sfLockedAmount"), 1);
    let ledger = empty_ledger(vec![
        account_root(holder, 1, 0),
        owner_dir_root(holder, *token.key()),
        token,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_AUTHORIZE, |object| {
        object.set_account_id(sf("sfAccount"), holder);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(sf("sfFlags"), protocol::tfMPTUnauthorize);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &tx, TxType::MPTOKEN_AUTHORIZE),
        protocol::Ter::TES_SUCCESS
    );
    assert!(
        view.read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(holder)
        ))
        .expect("token read")
        .is_none()
    );
}

#[test]
fn mptoken_authorize_dispatch_rejects_self_holder_before_ledger_checks() {
    let account = sample_account(0xCC);
    let issuer = sample_account(0xCD);
    let mpt_id = share_id_for(issuer, 1);
    let mut ledger = empty_ledger(vec![]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV1")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_AUTHORIZE, |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_account_id(sf("sfHolder"), account);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        apply_simulated_transaction(&mut view, &tx).0,
        protocol::Ter::TEM_MALFORMED
    );
}

#[test]
fn mptoken_issuance_create_dispatch_preserves_optional_fields() {
    let issuer = sample_account(0xD1);
    let sequence = 7;
    let mpt_id = share_id_for(issuer, sequence);
    let domain_id = sample_uint256(0xD2);
    let mut ledger = empty_ledger(vec![account_root_with_balance(issuer, 0, 0, 1_000_000_000)]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("PermissionedDomains"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("DynamicMPT"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), issuer);
        object.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        object.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::lsfMPTCanTransfer | protocol::lsfMPTRequireAuth,
        );
        object.set_field_u64(get_field_by_symbol("sfMaximumAmount"), 1_000_000);
        object.set_field_u8(get_field_by_symbol("sfAssetScale"), 6);
        object.set_field_u16(get_field_by_symbol("sfTransferFee"), 250);
        object.set_field_vl(get_field_by_symbol("sfMPTokenMetadata"), b"meta");
        object.set_field_h256(get_field_by_symbol("sfDomainID"), domain_id);
        object.set_field_u32(
            get_field_by_symbol("sfImmutableFlags"),
            protocol::lsifMPTMetadata | protocol::lsifMPTTransferFee,
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });

    let result = dispatch_with_pre_fee_balance(&mut view, &tx, TxType::MPTOKEN_ISSUANCE_CREATE);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read should succeed")
        .expect("issuance should be created");
    assert_eq!(
        issuance.get_account_id(get_field_by_symbol("sfIssuer")),
        issuer
    );
    assert_eq!(
        issuance.get_field_u64(get_field_by_symbol("sfMaximumAmount")),
        1_000_000
    );
    assert_eq!(
        issuance.get_field_u8(get_field_by_symbol("sfAssetScale")),
        6
    );
    assert_eq!(
        issuance.get_field_u16(get_field_by_symbol("sfTransferFee")),
        250
    );
    assert_eq!(
        issuance.get_field_vl(get_field_by_symbol("sfMPTokenMetadata")),
        b"meta".to_vec()
    );
    assert_eq!(
        issuance.get_field_h256(get_field_by_symbol("sfDomainID")),
        domain_id
    );
    assert_eq!(
        issuance.get_field_u32(get_field_by_symbol("sfImmutableFlags")),
        protocol::lsifMPTMetadata | protocol::lsifMPTTransferFee
    );
    assert_eq!(
        issuance.get_field_u32(get_field_by_symbol("sfFlags")),
        protocol::lsfMPTCanTransfer | protocol::lsfMPTRequireAuth
    );
    let issuer_root = view
        .read(account_keylet(raw_account_id(issuer)))
        .expect("issuer read should succeed")
        .expect("issuer should remain");
    assert_eq!(issuer_root.get_field_u32(sf("sfOwnerCount")), 1);
}

#[test]
fn mptoken_issuance_create_dispatch_checks_extra_features_before_apply() {
    let issuer = sample_account(0xD3);
    let domain_id = sample_uint256(0xD4);
    let mut ledger = empty_ledger(vec![account_root_with_balance(issuer, 0, 0, 1_000_000_000)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV1")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let domain_tx = STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_field_u32(sf("sfFlags"), protocol::tfMPTRequireAuth);
        object.set_field_h256(sf("sfDomainID"), domain_id);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });
    assert_eq!(
        apply_simulated_transaction(&mut view, &domain_tx).0,
        protocol::Ter::TEM_DISABLED
    );

    let immutable_tx = STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_u32(sf("sfSequence"), 2);
        object.set_field_u32(sf("sfFlags"), 0);
        object.set_field_u32(sf("sfImmutableFlags"), protocol::lsifMPTMetadata);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });
    assert_eq!(
        apply_simulated_transaction(&mut view, &immutable_tx).0,
        protocol::Ter::TEM_DISABLED
    );
}

#[test]
fn mptoken_issuance_create_dispatch_runs_preflight_before_apply() {
    let issuer = sample_account(0xD4);
    let mut ledger = empty_ledger(vec![account_root_with_balance(issuer, 0, 0, 1_000_000_000)]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("PermissionedDomains"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("DynamicMPT"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    // sfReferenceHolding is not in the canonical MPTokenIssuanceCreate
    // transaction format, so STTx correctly strips it. Exercise the pinned
    // fixCleanup3_2_0 semantic branch at its facts boundary instead of using
    // an impossible serialized transaction fixture.
    assert_eq!(
        run_mp_token_issuance_create_preflight(MPTokenIssuanceCreatePreflightFacts {
            fix_cleanup_3_2_0_enabled: true,
            confidential_transfer_enabled: false,
            reference_holding_present: true,
            immutable_flags: None,
            tx_flags: 0,
            transfer_fee: None,
            domain_id_present: false,
            domain_id_is_zero: false,
            metadata_len: None,
            maximum_amount: None,
        }),
        protocol::Ter::TEM_MALFORMED
    );

    let cases = [
        (
            STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
                object.set_account_id(sf("sfAccount"), issuer);
                object.set_field_u32(sf("sfSequence"), 2);
                object.set_field_u32(sf("sfFlags"), 0);
                object.set_field_u32(sf("sfImmutableFlags"), 0);
                object.set_field_amount(
                    sf("sfFee"),
                    STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
                );
            }),
            protocol::Ter::TEM_INVALID_FLAG,
        ),
        (
            STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
                object.set_account_id(sf("sfAccount"), issuer);
                object.set_field_u32(sf("sfSequence"), 3);
                object.set_field_u32(sf("sfFlags"), 0);
                object.set_field_u16(sf("sfTransferFee"), 1);
                object.set_field_amount(
                    sf("sfFee"),
                    STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
                );
            }),
            protocol::Ter::TEM_MALFORMED,
        ),
        (
            STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
                object.set_account_id(sf("sfAccount"), issuer);
                object.set_field_u32(sf("sfSequence"), 4);
                object.set_field_u32(sf("sfFlags"), protocol::tfMPTRequireAuth);
                object.set_field_h256(sf("sfDomainID"), Uint256::zero());
                object.set_field_amount(
                    sf("sfFee"),
                    STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
                );
            }),
            protocol::Ter::TEM_MALFORMED,
        ),
        (
            STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
                object.set_account_id(sf("sfAccount"), issuer);
                object.set_field_u32(sf("sfSequence"), 5);
                object.set_field_u32(sf("sfFlags"), 0);
                object.set_field_vl(sf("sfMPTokenMetadata"), b"");
                object.set_field_amount(
                    sf("sfFee"),
                    STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
                );
            }),
            protocol::Ter::TEM_MALFORMED,
        ),
        (
            STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
                object.set_account_id(sf("sfAccount"), issuer);
                object.set_field_u32(sf("sfSequence"), 6);
                object.set_field_u32(sf("sfFlags"), 0);
                object.set_field_u64(sf("sfMaximumAmount"), 0);
                object.set_field_amount(
                    sf("sfFee"),
                    STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
                );
            }),
            protocol::Ter::TEM_MALFORMED,
        ),
    ];

    for (case_index, (tx, expected)) in cases.into_iter().enumerate() {
        assert_eq!(
            apply_simulated_transaction(&mut view, &tx).0,
            expected,
            "preflight case {case_index}"
        );
    }
    for sequence in 2..=6 {
        assert!(
            view.read(protocol::mpt_issuance_keylet_from_mptid(share_id_for(
                issuer, sequence
            )))
            .expect("issuance read should succeed")
            .is_none()
        );
    }
}

#[test]
fn mptoken_issuance_create_dispatch_masks_universal_transaction_flags() {
    let issuer = sample_account(0xD5);
    let sequence = 2;
    let mpt_id = share_id_for(issuer, sequence);
    let ledger = empty_ledger(vec![account_root_with_balance(issuer, 0, 0, 1_000_000_000)]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_u32(sf("sfSequence"), sequence);
        object.set_field_u32(
            sf("sfFlags"),
            protocol::tfUniversal | protocol::lsfMPTCanTransfer,
        );
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });

    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &tx, TxType::MPTOKEN_ISSUANCE_CREATE),
        protocol::Ter::TES_SUCCESS
    );
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read should succeed")
        .expect("issuance should be created");
    assert_eq!(
        issuance.get_field_u32(sf("sfFlags")),
        protocol::lsfMPTCanTransfer
    );
}

#[test]
fn mptoken_issuance_create_dispatch_rejects_missing_issuer() {
    let issuer = sample_account(0xD9);
    let ledger = empty_ledger(vec![]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_field_u32(sf("sfFlags"), 0);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::MPTOKEN_ISSUANCE_CREATE, Some(0)),
        protocol::Ter::TEC_INTERNAL
    );
    assert!(
        view.read(protocol::mpt_issuance_keylet_from_mptid(share_id_for(
            issuer, 1
        )))
        .expect("issuance read should succeed")
        .is_none()
    );
}

#[test]
fn mptoken_issuance_create_dispatch_rejects_insufficient_prefee_reserve() {
    let issuer = sample_account(0xDA);
    let mut ledger = empty_ledger(vec![account_root_with_balance(issuer, 0, 0, 1_000_000_000)]);
    ledger.set_fees(ledger::Fees {
        base: 10,
        reserve: 200,
        increment: 50,
    });
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_field_u32(sf("sfFlags"), 0);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::MPTOKEN_ISSUANCE_CREATE, Some(0)),
        protocol::Ter::TEC_INSUFFICIENT_RESERVE
    );
    assert!(
        view.read(protocol::mpt_issuance_keylet_from_mptid(share_id_for(
            issuer, 1
        )))
        .expect("issuance read should succeed")
        .is_none()
    );
    let issuer_root = view
        .read(account_keylet(raw_account_id(issuer)))
        .expect("issuer read should succeed")
        .expect("issuer should remain");
    assert_eq!(issuer_root.get_field_u32(sf("sfOwnerCount")), 0);
}

#[test]
fn mptoken_issuance_set_dispatch_applies_cpp_mutation_order() {
    let issuer = sample_account(0xD3);
    let mpt_id = share_id_for(issuer, 1);
    let mut issuance = mpt_issuance_entry(
        issuer,
        1,
        0,
        protocol::lsfMPTCanLock | protocol::lsfMPTCanTransfer | protocol::lsfMPTRequireAuth,
    );
    issuance.set_field_u32(get_field_by_symbol("sfImmutableFlags"), 0);
    issuance.set_field_u16(get_field_by_symbol("sfTransferFee"), 500);
    issuance.set_field_h256(get_field_by_symbol("sfDomainID"), sample_uint256(0xD4));
    issuance.set_stbase(protocol::STBlob::from_buffer(
        get_field_by_symbol("sfMPTokenMetadata"),
        basics::buffer::Buffer::from(&b"old-meta"[..]),
    ));
    let mut ledger = empty_ledger(vec![account_root(issuer, 1, 0), issuance]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("DynamicMPT"),
        protocol::feature_id("PermissionedDomains"),
        protocol::feature_id("SingleAssetVault"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_SET, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), issuer);
        object.set_field_h192(get_field_by_symbol("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::tfMPTSetCanTransfer,
        );
        object.set_field_u16(get_field_by_symbol("sfTransferFee"), 0);
        object.set_field_vl(get_field_by_symbol("sfMPTokenMetadata"), b"");
        object.set_field_h256(
            get_field_by_symbol("sfDomainID"),
            Uint256::from_array([0; 32]),
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::MPTOKEN_ISSUANCE_SET, None);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read should succeed")
        .expect("issuance should remain");
    let flags = issuance.get_field_u32(get_field_by_symbol("sfFlags"));
    assert_eq!(flags & protocol::lsfMPTLocked, 0);
    assert_ne!(flags & protocol::lsfMPTCanTransfer, 0);
    assert!(!issuance.is_field_present(get_field_by_symbol("sfTransferFee")));
    assert!(!issuance.is_field_present(get_field_by_symbol("sfMPTokenMetadata")));
    assert!(!issuance.is_field_present(get_field_by_symbol("sfDomainID")));
}

#[test]
fn mptoken_issuance_set_dispatch_rejects_dynamic_mutation_without_dynamic_mpt() {
    let issuer = sample_account(0xE6);
    let mpt_id = share_id_for(issuer, 1);
    let mut issuance = mpt_issuance_entry(issuer, 1, 0, protocol::lsfMPTCanTransfer);
    issuance.set_field_u32(sf("sfImmutableFlags"), protocol::lsifMPTMetadata);
    let ledger = empty_ledger(vec![account_root(issuer, 1, 0), issuance]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_SET, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_vl(sf("sfMPTokenMetadata"), b"new-meta");
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        apply_simulated_transaction(&mut view, &tx).0,
        protocol::Ter::TEM_DISABLED
    );
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read should succeed")
        .expect("issuance should remain");
    assert!(!issuance.is_field_present(sf("sfMPTokenMetadata")));
}

#[test]
fn mptoken_issuance_set_enables_capability_and_adds_immutable_bits() {
    let issuer = sample_account(0xA7);
    let mpt_id = share_id_for(issuer, 1);
    let mut issuance = mpt_issuance_entry(issuer, 1, 0, 0);
    issuance.set_field_u32(sf("sfImmutableFlags"), protocol::lsifMPTMetadata);
    let mut ledger = empty_ledger(vec![account_root(issuer, 1, 0), issuance]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("DynamicMPT"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_SET, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(sf("sfFlags"), protocol::tfMPTSetCanTransfer);
        object.set_field_u32(
            sf("sfImmutableFlags"),
            protocol::lsifMPTCanTransfer | protocol::lsifMPTTransferFee,
        );
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::MPTOKEN_ISSUANCE_SET, None),
        protocol::Ter::TES_SUCCESS
    );
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read")
        .expect("issuance exists");
    assert!(issuance.is_flag(protocol::lsfMPTCanTransfer));
    assert_eq!(
        issuance.get_field_u32(sf("sfImmutableFlags")),
        protocol::lsifMPTMetadata | protocol::lsifMPTCanTransfer | protocol::lsifMPTTransferFee
    );
}

#[test]
fn mptoken_issuance_set_immutable_policy_is_enforced_by_production_preclaim() {
    let issuer = sample_account(0xA6);
    let mpt_id = share_id_for(issuer, 1);
    let mut issuance = mpt_issuance_entry(issuer, 1, 0, 0);
    issuance.set_field_u32(sf("sfImmutableFlags"), protocol::tifMPTCanTransfer);
    let mut ledger = empty_ledger(vec![account_root(issuer, 1, 0), issuance]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("DynamicMPT"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_SET, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(sf("sfFlags"), protocol::tfMPTSetCanTransfer);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        apply_simulated_transaction(&mut view, &tx).0,
        Ter::TEC_NO_PERMISSION
    );
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read")
        .expect("issuance remains");
    assert!(!issuance.is_flag(protocol::lsfMPTCanTransfer));
}

#[test]
fn mpt_issuance_create_and_destroy_preserve_reserve_sponsor_accounting() {
    let issuer = sample_account(0xA8);
    let sponsor = sample_account(0xA9);
    let mpt_id = share_id_for(issuer, 1);
    let ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 0, 0, 1_000_000_000),
        account_root_with_balance(sponsor, 0, 0, 1_000_000_000),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let create = STTx::new(TxType::MPTOKEN_ISSUANCE_CREATE, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_account_id(sf("sfSponsor"), sponsor);
        object.set_field_u32(sf("sfSponsorFlags"), ledger::SPF_SPONSOR_RESERVE);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &create,
            TxType::MPTOKEN_ISSUANCE_CREATE,
            Some(1_000_000_000),
        ),
        Ter::TES_SUCCESS
    );
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read")
        .expect("issuance created");
    assert_eq!(issuance.get_account_id(sf("sfSponsor")), sponsor);
    let issuer_root = view
        .read(account_keylet(raw_account_id(issuer)))
        .expect("issuer read")
        .expect("issuer exists");
    let sponsor_root = view
        .read(account_keylet(raw_account_id(sponsor)))
        .expect("sponsor read")
        .expect("sponsor exists");
    assert_eq!(issuer_root.get_field_u32(sf("sfOwnerCount")), 1);
    assert_eq!(issuer_root.get_field_u32(sf("sfSponsoredOwnerCount")), 1);
    assert_eq!(sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")), 1);

    let destroy = STTx::new(TxType::MPTOKEN_ISSUANCE_DESTROY, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 2);
    });
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &destroy, TxType::MPTOKEN_ISSUANCE_DESTROY),
        Ter::TES_SUCCESS
    );
    let issuer_root = view
        .read(account_keylet(raw_account_id(issuer)))
        .expect("issuer read")
        .expect("issuer exists");
    let sponsor_root = view
        .read(account_keylet(raw_account_id(sponsor)))
        .expect("sponsor read")
        .expect("sponsor exists");
    assert_eq!(issuer_root.get_field_u32(sf("sfOwnerCount")), 0);
    assert_eq!(issuer_root.get_field_u32(sf("sfSponsoredOwnerCount")), 0);
    assert_eq!(sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")), 0);
}

#[test]
fn mptoken_authorize_create_and_delete_preserve_reserve_sponsor_accounting() {
    let issuer = sample_account(0xAA);
    let holder = sample_account(0xAB);
    let sponsor = sample_account(0xAC);
    let mpt_id = share_id_for(issuer, 1);
    let ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        account_root_with_balance(holder, 0, 0, 1_000_000_000),
        account_root_with_balance(sponsor, 0, 0, 1_000_000_000),
        mpt_issuance_entry(issuer, 1, 0, 0),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let create = STTx::new(TxType::MPTOKEN_AUTHORIZE, |object| {
        object.set_account_id(sf("sfAccount"), holder);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_account_id(sf("sfSponsor"), sponsor);
        object.set_field_u32(sf("sfSponsorFlags"), ledger::SPF_SPONSOR_RESERVE);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &create,
            TxType::MPTOKEN_AUTHORIZE,
            Some(1_000_000_000),
        ),
        Ter::TES_SUCCESS
    );
    let token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(holder),
        ))
        .expect("token read")
        .expect("token created");
    assert_eq!(token.get_account_id(sf("sfSponsor")), sponsor);
    let holder_root = view
        .read(account_keylet(raw_account_id(holder)))
        .expect("holder read")
        .expect("holder exists");
    let sponsor_root = view
        .read(account_keylet(raw_account_id(sponsor)))
        .expect("sponsor read")
        .expect("sponsor exists");
    assert_eq!(holder_root.get_field_u32(sf("sfSponsoredOwnerCount")), 1);
    assert_eq!(sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")), 1);

    let remove = STTx::new(TxType::MPTOKEN_AUTHORIZE, |object| {
        object.set_account_id(sf("sfAccount"), holder);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(sf("sfFlags"), protocol::tfMPTUnauthorize);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 2);
    });
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &remove, TxType::MPTOKEN_AUTHORIZE),
        Ter::TES_SUCCESS
    );
    let holder_root = view
        .read(account_keylet(raw_account_id(holder)))
        .expect("holder read")
        .expect("holder exists");
    let sponsor_root = view
        .read(account_keylet(raw_account_id(sponsor)))
        .expect("sponsor read")
        .expect("sponsor exists");
    assert_eq!(holder_root.get_field_u32(sf("sfOwnerCount")), 0);
    assert_eq!(holder_root.get_field_u32(sf("sfSponsoredOwnerCount")), 0);
    assert_eq!(sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")), 0);
}

#[test]
fn mptoken_issuance_set_dispatch_rejects_domain_without_required_features() {
    let issuer = sample_account(0xE7);
    let mpt_id = share_id_for(issuer, 1);
    let ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        mpt_issuance_entry(
            issuer,
            1,
            0,
            protocol::lsfMPTCanLock | protocol::lsfMPTRequireAuth,
        ),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_SET, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_h256(sf("sfDomainID"), sample_uint256(0xE8));
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        apply_simulated_transaction(&mut view, &tx).0,
        protocol::Ter::TEM_DISABLED
    );
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read should succeed")
        .expect("issuance should remain");
    assert!(!issuance.is_field_present(sf("sfDomainID")));
}

#[test]
fn mptoken_issuance_set_dispatch_rejects_wrong_issuer() {
    let issuer = sample_account(0xE0);
    let other = sample_account(0xE1);
    let mpt_id = share_id_for(issuer, 1);
    let mut ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        account_root(other, 1, 0),
        mpt_issuance_entry(issuer, 1, 0, protocol::lsfMPTCanLock),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV1")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_SET, |object| {
        object.set_account_id(sf("sfAccount"), other);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(sf("sfFlags"), protocol::tfMPTLock);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        apply_simulated_transaction(&mut view, &tx).0,
        protocol::Ter::TEC_NO_PERMISSION
    );
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read should succeed")
        .expect("issuance should remain");
    assert_eq!(
        issuance.get_field_u32(sf("sfFlags")) & protocol::lsfMPTLocked,
        0
    );
}

#[test]
fn mptoken_issuance_set_do_apply_maps_preclaim_proven_target_disappearance_to_internal() {
    let issuer = sample_account(0xE8);
    let holder = sample_account(0xE9);
    let mpt_id = share_id_for(issuer, 1);
    let ledger = empty_ledger(vec![account_root(issuer, 0, 0)]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_SET, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(sf("sfFlags"), protocol::tfMPTLock);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    // This is deliberately a doApply-only harness: immutable preclaim would
    // reject the missing issuance with tecOBJECT_NOT_FOUND.  Once preclaim has
    // succeeded, pinned doApply classifies disappearance of either the
    // issuance or holder-token target as tecINTERNAL.
    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::MPTOKEN_ISSUANCE_SET, None),
        Ter::TEC_INTERNAL
    );

    let ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        account_root(holder, 0, 0),
        mpt_issuance_entry(issuer, 1, 0, protocol::lsfMPTCanLock),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let holder_tx = STTx::new(TxType::MPTOKEN_ISSUANCE_SET, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_account_id(sf("sfHolder"), holder);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(sf("sfFlags"), protocol::tfMPTLock);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });
    assert_eq!(
        handle_real_dispatch(&mut view, &holder_tx, TxType::MPTOKEN_ISSUANCE_SET, None,),
        Ter::TEC_INTERNAL
    );
}

#[test]
fn mptoken_issuance_set_dispatch_rejects_missing_domain() {
    let issuer = sample_account(0xE2);
    let mpt_id = share_id_for(issuer, 1);
    let mut ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        mpt_issuance_entry(
            issuer,
            1,
            0,
            protocol::lsfMPTCanLock | protocol::lsfMPTRequireAuth,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("PermissionedDomains"),
        protocol::feature_id("SingleAssetVault"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_SET, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_h256(sf("sfDomainID"), sample_uint256(0xE3));
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        apply_simulated_transaction(&mut view, &tx).0,
        protocol::Ter::TEC_OBJECT_NOT_FOUND
    );
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read should succeed")
        .expect("issuance should remain");
    assert!(!issuance.is_field_present(sf("sfDomainID")));
}

#[test]
fn mptoken_issuance_set_dispatch_locks_holder_token_not_issuance() {
    let issuer = sample_account(0xE4);
    let holder = sample_account(0xE5);
    let mpt_id = share_id_for(issuer, 1);
    let ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        account_root(holder, 1, 0),
        mpt_issuance_entry(issuer, 1, 0, protocol::lsfMPTCanLock),
        mptoken_entry(holder, mpt_id, 0),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_SET, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_account_id(sf("sfHolder"), holder);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(sf("sfFlags"), protocol::tfMPTLock);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::MPTOKEN_ISSUANCE_SET, None),
        protocol::Ter::TES_SUCCESS
    );
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read should succeed")
        .expect("issuance should remain");
    let token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(holder),
        ))
        .expect("holder token read should succeed")
        .expect("holder token should remain");
    assert_eq!(
        issuance.get_field_u32(sf("sfFlags")) & protocol::lsfMPTLocked,
        0
    );
    assert_ne!(
        token.get_field_u32(sf("sfFlags")) & protocol::lsfMPTLocked,
        0
    );
}

#[test]
fn mptoken_authorize_dispatch_rejects_issuer_unauthorize_of_amm_pseudo_holder() {
    let issuer = sample_account(0xC3);
    let amm_holder = sample_account(0xC4);
    let mpt_id = share_id_for(issuer, 1);
    let mut amm_root = account_root(amm_holder, 1, 0);
    amm_root.set_field_h256(get_field_by_symbol("sfAMMID"), sample_uint256(0xC5));
    let mut token = mptoken_entry(amm_holder, mpt_id, 0);
    token.set_field_u32(get_field_by_symbol("sfFlags"), protocol::lsfMPTAuthorized);
    let mut ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        amm_root,
        mpt_issuance_entry(
            issuer,
            1,
            0,
            protocol::lsfMPTRequireAuth | protocol::lsfMPTCanTransfer,
        ),
        token,
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV1")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_AUTHORIZE, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), issuer);
        object.set_account_id(get_field_by_symbol("sfHolder"), amm_holder);
        object.set_field_h192(get_field_by_symbol("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(get_field_by_symbol("sfFlags"), protocol::tfMPTUnauthorize);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = apply_simulated_transaction(&mut view, &tx).0;

    assert_eq!(result, protocol::Ter::TEC_NO_PERMISSION);
}

#[test]
fn mptoken_authorize_issuer_branch_checks_holder_before_issuance() {
    let issuer = sample_account(0xCF);
    let holder = sample_account(0xD0);
    let mpt_id = share_id_for(issuer, 1);
    let mut ledger = empty_ledger(vec![account_root(issuer, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV1")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_AUTHORIZE, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_account_id(sf("sfHolder"), holder);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        apply_simulated_transaction(&mut view, &tx).0,
        protocol::Ter::TEC_NO_DST
    );
}

#[test]
fn mptoken_authorize_issuer_branch_checks_holder_token_before_pseudo() {
    let issuer = sample_account(0xD1);
    let holder = sample_account(0xD2);
    let mpt_id = share_id_for(issuer, 1);
    let mut holder_root = account_root(holder, 0, 0);
    holder_root.set_field_h256(sf("sfVaultID"), sample_uint256(0xD3));
    let mut ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        holder_root,
        mpt_issuance_entry(
            issuer,
            1,
            0,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTRequireAuth,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV1")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_AUTHORIZE, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_account_id(sf("sfHolder"), holder);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        apply_simulated_transaction(&mut view, &tx).0,
        protocol::Ter::TEC_OBJECT_NOT_FOUND
    );
}

#[test]
fn mptoken_authorize_do_apply_maps_preclaim_proven_targets_to_internal() {
    let issuer = sample_account(0xDA);
    let holder = sample_account(0xDB);
    let mpt_id = share_id_for(issuer, 1);
    let tx = STTx::new(TxType::MPTOKEN_AUTHORIZE, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_account_id(sf("sfHolder"), holder);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    let ledger = empty_ledger(vec![account_root(issuer, 0, 0)]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &tx, TxType::MPTOKEN_AUTHORIZE),
        Ter::TEC_INTERNAL
    );

    let ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        mpt_issuance_entry(
            issuer,
            1,
            0,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTRequireAuth,
        ),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &tx, TxType::MPTOKEN_AUTHORIZE),
        Ter::TEC_INTERNAL
    );
}

#[test]
fn mptoken_issuance_destroy_rejects_active_escrow_locked_amount() {
    let issuer = sample_account(0xC6);
    let mpt_id = share_id_for(issuer, 1);
    let mut issuance = mpt_issuance_entry(issuer, 1, 0, protocol::lsfMPTCanTransfer);
    issuance.set_field_u64(get_field_by_symbol("sfLockedAmount"), 10);
    let mut ledger = empty_ledger(vec![account_root(issuer, 1, 0), issuance]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV1")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_DESTROY, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), issuer);
        object.set_field_h192(get_field_by_symbol("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = apply_simulated_transaction(&mut view, &tx).0;

    assert_eq!(result, protocol::Ter::TEC_HAS_OBLIGATIONS);
    assert!(
        view.read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
            .expect("issuance read should succeed")
            .is_some()
    );
}

#[test]
fn mptoken_issuance_destroy_rejects_missing_owner_dir_before_erase() {
    let issuer = sample_account(0xD4);
    let mpt_id = share_id_for(issuer, 1);
    let ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        mpt_issuance_entry(issuer, 1, 0, protocol::lsfMPTCanTransfer),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_DESTROY, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &tx, TxType::MPTOKEN_ISSUANCE_DESTROY),
        protocol::Ter::TEF_BAD_LEDGER
    );
    assert!(
        view.read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
            .expect("issuance read should succeed")
            .is_some()
    );
}

#[test]
fn mptoken_issuance_destroy_rejects_missing_issuance() {
    let issuer = sample_account(0xCC);
    let mpt_id = share_id_for(issuer, 1);
    let mut ledger = empty_ledger(vec![account_root(issuer, 1, 0)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV1")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_DESTROY, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_h192(sf("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        apply_simulated_transaction(&mut view, &tx).0,
        protocol::Ter::TEC_OBJECT_NOT_FOUND
    );
}

#[test]
fn mptoken_issuance_destroy_rejects_non_issuer() {
    let issuer = sample_account(0xC7);
    let other = sample_account(0xC8);
    let mpt_id = share_id_for(issuer, 1);
    let mut ledger = empty_ledger(vec![
        account_root(issuer, 1, 0),
        account_root(other, 0, 0),
        mpt_issuance_entry(issuer, 1, 0, protocol::lsfMPTCanTransfer),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV1")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_DESTROY, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), other);
        object.set_field_h192(get_field_by_symbol("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = apply_simulated_transaction(&mut view, &tx).0;

    assert_eq!(result, protocol::Ter::TEC_NO_PERMISSION);
}

#[test]
fn offer_create_places_funded_mpt_offer_without_iou_issue_panic() {
    let owner = sample_account(0xCA);
    let issuer = sample_account(0xCB);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let taker_pays = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let taker_gets = STAmount::from_mpt_amount(
        get_field_by_symbol("sfTakerGets"),
        protocol::MPTAmount::from_value(10),
        mpt_issue,
    );
    let ledger = empty_ledger(vec![
        account_root_with_balance(owner, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
        ),
        mptoken_entry(owner, mpt_id, 50),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = offer_create_tx(owner, 2, taker_pays, taker_gets, 0, None);

    // MPT authorization/freeze/trade checks are immutable OfferCreate
    // preclaim work in rippled. Exercise the production shell so the test
    // cannot accidentally skip that phase by calling the doApply dispatcher.
    let result = apply_submit_transactor_shell(&mut view, &tx, TxType::OFFER_CREATE);

    assert_eq!(result, Ter::TES_SUCCESS);
    let offer = view
        .read(protocol::offer_keylet(raw_account_id(owner), 2))
        .expect("offer read should succeed")
        .expect("offer should be placed");
    assert_eq!(
        offer
            .get_field_amount(get_field_by_symbol("sfTakerGets"))
            .asset(),
        Asset::MPTIssue(mpt_issue)
    );
}

#[test]
fn offer_create_rejects_locked_mpt_asset_before_placing_offer() {
    let owner = sample_account(0xC1);
    let issuer = sample_account(0xC2);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let taker_pays = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let taker_gets = STAmount::from_mpt_amount(
        get_field_by_symbol("sfTakerGets"),
        protocol::MPTAmount::from_value(10),
        mpt_issue,
    );
    let ledger = empty_ledger(vec![
        account_root_with_balance(owner, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade | protocol::lsfMPTLocked,
        ),
        mptoken_entry(owner, mpt_id, 50),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = offer_create_tx(owner, 2, taker_pays, taker_gets, 0, None);

    // checkAcceptAsset(TakerPays) precedes canTrade in pinned OfferCreate.
    // The full shell is required to preserve that preclaim ordering.
    let result = apply_submit_transactor_shell(&mut view, &tx, TxType::OFFER_CREATE);

    assert_eq!(result, Ter::TEC_LOCKED);
    assert!(
        view.read(protocol::offer_keylet(raw_account_id(owner), 2))
            .expect("offer read should succeed")
            .is_none()
    );
}

#[test]
fn offer_create_requires_authorization_for_mpt_accept_asset() {
    let owner = sample_account(0xC3);
    let issuer = sample_account(0xC4);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let taker_pays = STAmount::from_mpt_amount(
        get_field_by_symbol("sfTakerPays"),
        protocol::MPTAmount::from_value(10),
        mpt_issue,
    );
    let taker_gets = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let ledger = empty_ledger(vec![
        account_root_with_balance(owner, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade | protocol::lsfMPTRequireAuth,
        ),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = offer_create_tx(owner, 2, taker_pays, taker_gets, 0, None);

    // Pinned OfferCreate checks acceptance of TakerPays before canTrade.
    // Exercise that immutable preclaim through the production shell.
    let result = apply_submit_transactor_shell(&mut view, &tx, TxType::OFFER_CREATE);

    assert_eq!(result, Ter::TEC_NO_AUTH);
    assert!(
        view.read(protocol::offer_keylet(raw_account_id(owner), 2))
            .expect("offer read should succeed")
            .is_none()
    );
}

#[test]
fn offer_create_allows_tradable_nontransferable_mpt_sell_offer() {
    let owner = sample_account(0xC5);
    let issuer = sample_account(0xC6);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let taker_pays = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let taker_gets = STAmount::from_mpt_amount(
        get_field_by_symbol("sfTakerGets"),
        protocol::MPTAmount::from_value(10),
        mpt_issue,
    );
    let ledger = empty_ledger(vec![
        account_root_with_balance(owner, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        mpt_issuance_entry(issuer, 1, 100, protocol::lsfMPTCanTrade),
        mptoken_entry(owner, mpt_id, 50),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = offer_create_tx(owner, 2, taker_pays, taker_gets, 0, None);

    let result = dispatch_with_pre_fee_balance(&mut view, &tx, TxType::OFFER_CREATE);

    assert_eq!(result, Ter::TES_SUCCESS);
    assert!(
        view.read(protocol::offer_keylet(raw_account_id(owner), 2))
            .expect("offer read should succeed")
            .is_some()
    );
}

#[test]
fn offer_create_tick_rounding_preserves_mpt_side_in_both_orientations() {
    let iou_issuer = sample_account(0xC7);
    let holder = sample_account(0xC8);
    let mpt_issuer = sample_account(0xC9);
    let mpt_id = share_id_for(mpt_issuer, 1);
    let mpt_issue = MPTIssue::new(mpt_id);
    let usd = Issue::new(currency_from_string("USD"), iou_issuer);
    let mut iou_issuer_root = account_root_with_balance(iou_issuer, 1, 0, 1_000_000_000);
    iou_issuer_root.set_field_u8(sf("sfTickSize"), 3);
    let ledger = empty_ledger(vec![
        iou_issuer_root,
        account_root_with_balance(holder, 1, 0, 1_000_000_000),
        account_root(mpt_issuer, 1, 0),
        mpt_issuance_entry(
            mpt_issuer,
            1,
            2_000_000,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
        ),
        mptoken_entry(holder, mpt_id, 1_000_000),
        mptoken_entry(iou_issuer, mpt_id, 0),
        trust_line_entry(holder, iou_issuer, usd.currency, 0),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    // Non-sell rounds TakerGets in rippled, except when that side is MPT.
    let non_sell_mpt =
        STAmount::from_mpt_amount(sf("sfTakerGets"), MPTAmount::from_value(123_457), mpt_issue);
    let tx = offer_create_tx(
        holder,
        2,
        STAmount::from_iou_amount(
            sf("sfTakerPays"),
            IOUAmount::from_parts(765_439, 0).expect("IOU amount"),
            usd,
        ),
        non_sell_mpt.clone(),
        0,
        None,
    );
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &tx, TxType::OFFER_CREATE),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        view.read(protocol::offer_keylet(raw_account_id(holder), 2))
            .expect("offer read")
            .expect("offer exists")
            .get_field_amount(sf("sfTakerGets")),
        non_sell_mpt
    );

    // tfSell rounds TakerPays, except when that side is MPT.
    let sell_mpt =
        STAmount::from_mpt_amount(sf("sfTakerPays"), MPTAmount::from_value(234_569), mpt_issue);
    let tx = offer_create_tx(
        iou_issuer,
        2,
        sell_mpt.clone(),
        STAmount::from_iou_amount(
            sf("sfTakerGets"),
            IOUAmount::from_parts(876_541, 0).expect("IOU amount"),
            usd,
        ),
        0x0008_0000,
        None,
    );
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &tx, TxType::OFFER_CREATE),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        view.read(protocol::offer_keylet(raw_account_id(iou_issuer), 2))
            .expect("offer read")
            .expect("offer exists")
            .get_field_amount(sf("sfTakerPays")),
        sell_mpt
    );
}

#[test]
fn check_create_rejects_mpt_when_transfer_is_disabled() {
    let source = sample_account(0xD1);
    let destination = sample_account(0xD2);
    let issuer = sample_account(0xD3);
    let mpt_id = share_id_for(issuer, 1);
    let send_max = STAmount::from_mpt_amount(
        get_field_by_symbol("sfSendMax"),
        protocol::MPTAmount::from_value(10),
        protocol::MPTIssue::new(mpt_id),
    );
    let ledger = empty_ledger(vec![
        account_root_with_balance(source, 0, 0, 1_000_000_000),
        account_root_with_balance(destination, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        mpt_issuance_entry(issuer, 1, 100, protocol::lsfMPTCanTrade),
        mptoken_entry(source, mpt_id, 50),
        mptoken_entry(destination, mpt_id, 0),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::CHECK_CREATE, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), source);
        object.set_account_id(get_field_by_symbol("sfDestination"), destination);
        object.set_field_amount(get_field_by_symbol("sfSendMax"), send_max);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 2);
    });

    let result = dispatch_with_pre_fee_balance(&mut view, &tx, TxType::CHECK_CREATE);

    assert_eq!(result, Ter::TEC_NO_AUTH);
    assert!(
        view.read(protocol::check_keylet(raw_account_id(source), 2))
            .expect("check read should succeed")
            .is_none()
    );
}

#[test]
fn check_create_uses_prefunded_reserve_sponsor_once() {
    let source = sample_account(0xD7);
    let destination = sample_account(0xD8);
    let sponsor = sample_account(0xD9);
    let sponsorship_key =
        protocol::sponsorship_keylet(raw_account_id(sponsor), raw_account_id(source));
    let sponsorship =
        protocol::SponsorshipBuilder::new(sponsor, source, 0, 0, Uint256::default(), 0)
            .set_remaining_owner_count(2)
            .build(sponsorship_key.key)
            .get_sle()
            .as_ref()
            .clone();
    let mut ledger = empty_ledger(vec![
        // The source cannot carry an owner reserve by itself.
        account_root_with_balance(source, 0, 0, 200),
        account_root_with_balance(destination, 0, 0, 1_000),
        account_root_with_balance(sponsor, 0, 0, 1_000),
        sponsorship,
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("Sponsor")]));
    ledger.set_fees(Fees {
        base: 10,
        reserve: 200,
        increment: 50,
    });
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::CHECK_CREATE, |object| {
        object.set_account_id(sf("sfAccount"), source);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_amount(sf("sfSendMax"), test_xrp(100));
        object.set_account_id(sf("sfSponsor"), sponsor);
        object.set_field_u32(sf("sfSponsorFlags"), ledger::SPF_SPONSOR_RESERVE);
        object.set_field_u32(sf("sfSequence"), 2);
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::CHECK_CREATE, Some(200)),
        Ter::TES_SUCCESS
    );
    let check = view
        .read(protocol::check_keylet(raw_account_id(source), 2))
        .expect("check read")
        .expect("check created");
    assert_eq!(check.get_account_id(sf("sfSponsor")), sponsor);
    assert!(check.is_field_present(sf("sfOwnerNode")));
    assert!(check.is_field_present(sf("sfDestinationNode")));
    let source_root = view
        .read(account_keylet(raw_account_id(source)))
        .expect("source read")
        .expect("source root");
    let sponsor_root = view
        .read(account_keylet(raw_account_id(sponsor)))
        .expect("sponsor read")
        .expect("sponsor root");
    let sponsorship = view
        .read(sponsorship_key)
        .expect("sponsorship read")
        .expect("sponsorship remains");
    assert_eq!(source_root.get_field_u32(sf("sfOwnerCount")), 1);
    assert_eq!(source_root.get_field_u32(sf("sfSponsoredOwnerCount")), 1);
    assert_eq!(sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")), 1);
    assert_eq!(sponsorship.get_field_u32(sf("sfRemainingOwnerCount")), 1);
}

#[test]
fn check_cash_transfers_mpt_without_requiring_dex_trading() {
    let source = sample_account(0xD4);
    let destination = sample_account(0xD5);
    let issuer = sample_account(0xD6);
    let mpt_id = share_id_for(issuer, 1);
    let send_max = STAmount::from_mpt_amount(
        get_field_by_symbol("sfSendMax"),
        protocol::MPTAmount::from_value(11),
        protocol::MPTIssue::new(mpt_id),
    );
    let mut issuance = mpt_issuance_entry(issuer, 1, 100, protocol::lsfMPTCanTransfer);
    issuance.set_field_u16(get_field_by_symbol("sfTransferFee"), 10_000);
    let check_keylet = protocol::check_keylet(raw_account_id(source), 3);
    let ledger = empty_ledger(vec![
        account_root_with_balance(source, 1, 0, 1_000_000_000),
        account_root_with_balance(destination, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        issuance,
        mptoken_entry(source, mpt_id, 50),
        owner_dir_root(source, check_keylet.key),
        owner_dir_root(destination, check_keylet.key),
        check_entry(source, destination, 3, send_max.clone()),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let check_id = protocol::check_keylet(raw_account_id(source), 3).key;
    let tx = STTx::new(TxType::CHECK_CASH, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), destination);
        object.set_field_h256(get_field_by_symbol("sfCheckID"), check_id);
        object.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_mpt_amount(
                get_field_by_symbol("sfAmount"),
                protocol::MPTAmount::from_value(10),
                protocol::MPTIssue::new(mpt_id),
            ),
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let expected_delivered = tx.get_field_amount(sf("sfAmount"));
    let (result, delivered_amount) =
        apply_submit_transactor_shell_with_delivered_amount(&mut view, &tx, TxType::CHECK_CASH);

    assert_eq!(result, Ter::TES_SUCCESS);
    assert_eq!(delivered_amount, Some(expected_delivered));
    let source_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(source),
        ))
        .expect("source token read should succeed")
        .expect("source token should exist");
    let destination_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(destination),
        ))
        .expect("destination token read should succeed")
        .expect("destination token should be created");
    assert_eq!(
        source_token.get_field_u64(get_field_by_symbol("sfMPTAmount")),
        39
    );
    assert_eq!(
        destination_token.get_field_u64(get_field_by_symbol("sfMPTAmount")),
        10
    );
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read should succeed")
        .expect("issuance should exist");
    assert_eq!(
        issuance.get_field_u64(get_field_by_symbol("sfOutstandingAmount")),
        99
    );
}

#[test]
fn check_cash_enforces_new_holding_reserve_and_accepts_reserve_sponsor() {
    let fees = Fees {
        base: 10,
        reserve: 200,
        increment: 50,
    };

    // Missing IOU trust lines use tecNO_LINE_INSUF_RESERVE.
    let issuer = sample_account(0xE1);
    let destination = sample_account(0xE2);
    let usd = Issue::new(currency_from_string("USD"), issuer);
    let iou_send_max = STAmount::from_iou_amount(
        sf("sfSendMax"),
        IOUAmount::from_parts(10, 0).expect("IOU amount"),
        usd,
    );
    let iou_check = protocol::check_keylet(raw_account_id(issuer), 3);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 1, 0, 1_000_000_000),
        account_root_with_balance(destination, 0, 0, 200),
        owner_dir_root(issuer, iou_check.key),
        owner_dir_root(destination, iou_check.key),
        check_entry(issuer, destination, 3, iou_send_max.clone()),
    ]);
    ledger.set_fees(fees);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::CHECK_CASH, |object| {
        object.set_account_id(sf("sfAccount"), destination);
        object.set_field_h256(sf("sfCheckID"), iou_check.key);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_iou_amount(
                sf("sfAmount"),
                IOUAmount::from_parts(10, 0).expect("IOU amount"),
                usd,
            ),
        );
        object.set_field_amount(sf("sfFee"), test_xrp(10));
        object.set_field_u32(sf("sfSequence"), 1);
    });
    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::CHECK_CASH, Some(200)),
        Ter::TEC_NO_LINE_INSUF_RESERVE
    );
    assert!(
        view.read(line(destination, issuer, usd.currency))
            .expect("line read")
            .is_none()
    );

    let iou_sponsor = sample_account(0xEF);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 1, 0, 1_000_000_000),
        account_root_with_balance(destination, 0, 0, 200),
        account_root_with_balance(iou_sponsor, 0, 0, 1_000),
        owner_dir_root(issuer, iou_check.key),
        owner_dir_root(destination, iou_check.key),
        check_entry(issuer, destination, 3, iou_send_max),
    ]);
    ledger.set_fees(fees);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let mut sponsored_iou_tx = tx.clone();
    sponsored_iou_tx.set_account_id(sf("sfSponsor"), iou_sponsor);
    sponsored_iou_tx.set_field_u32(sf("sfSponsorFlags"), ledger::SPF_SPONSOR_RESERVE);
    assert_eq!(
        handle_real_dispatch(&mut view, &sponsored_iou_tx, TxType::CHECK_CASH, Some(200)),
        Ter::TES_SUCCESS
    );
    let line = view
        .read(line(destination, issuer, usd.currency))
        .expect("line read")
        .expect("sponsored line");
    assert_eq!(line.get_account_id(sf("sfHighSponsor")), iou_sponsor);
    assert_eq!(
        view.read(account_keylet(raw_account_id(destination)))
            .expect("destination read")
            .expect("destination")
            .get_field_u32(sf("sfSponsoredOwnerCount")),
        1
    );
    assert_eq!(
        view.read(account_keylet(raw_account_id(iou_sponsor)))
            .expect("sponsor read")
            .expect("sponsor")
            .get_field_u32(sf("sfSponsoringOwnerCount")),
        1
    );

    // Missing MPT holdings use tecINSUFFICIENT_RESERVE.
    let source = sample_account(0xE3);
    let destination = sample_account(0xE4);
    let mpt_issuer = sample_account(0xE5);
    let mpt_id = share_id_for(mpt_issuer, 1);
    let mpt_issue = MPTIssue::new(mpt_id);
    let mpt_send_max =
        STAmount::from_mpt_amount(sf("sfSendMax"), MPTAmount::from_value(10), mpt_issue);
    let mpt_check = protocol::check_keylet(raw_account_id(source), 3);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(source, 1, 0, 1_000_000_000),
        account_root_with_balance(destination, 0, 0, 200),
        account_root(mpt_issuer, 1, 0),
        mpt_issuance_entry(mpt_issuer, 1, 100, protocol::lsfMPTCanTransfer),
        mptoken_entry(source, mpt_id, 50),
        owner_dir_root(source, mpt_check.key),
        owner_dir_root(destination, mpt_check.key),
        check_entry(source, destination, 3, mpt_send_max.clone()),
    ]);
    ledger.set_fees(fees);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let make_mpt_cash = |sponsor: Option<AccountID>| {
        STTx::new(TxType::CHECK_CASH, |object| {
            object.set_account_id(sf("sfAccount"), destination);
            object.set_field_h256(sf("sfCheckID"), mpt_check.key);
            object.set_field_amount(
                sf("sfAmount"),
                STAmount::from_mpt_amount(sf("sfAmount"), MPTAmount::from_value(10), mpt_issue),
            );
            object.set_field_amount(sf("sfFee"), test_xrp(10));
            object.set_field_u32(sf("sfSequence"), 1);
            if let Some(sponsor) = sponsor {
                object.set_account_id(sf("sfSponsor"), sponsor);
                object.set_field_u32(sf("sfSponsorFlags"), ledger::SPF_SPONSOR_RESERVE);
            }
        })
    };
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &make_mpt_cash(None),
            TxType::CHECK_CASH,
            Some(200)
        ),
        Ter::TEC_INSUFFICIENT_RESERVE
    );
    assert!(
        view.read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(destination)
        ))
        .expect("token read")
        .is_none()
    );

    // Sponsor base-account reserves are part of the reserve calculation.
    // This sponsor carries one additional account: 400 drops would satisfy
    // the legacy owner-only formula (250) but not rippled's two-base formula
    // (450).
    let sponsor = sample_account(0xE6);
    let mut sponsor_with_account = account_root_with_balance(sponsor, 0, 0, 400);
    sponsor_with_account.set_field_u32(sf("sfSponsoringAccountCount"), 1);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(source, 1, 0, 1_000_000_000),
        account_root_with_balance(destination, 0, 0, 200),
        sponsor_with_account,
        account_root(mpt_issuer, 1, 0),
        mpt_issuance_entry(mpt_issuer, 1, 100, protocol::lsfMPTCanTransfer),
        mptoken_entry(source, mpt_id, 50),
        owner_dir_root(source, mpt_check.key),
        owner_dir_root(destination, mpt_check.key),
        check_entry(source, destination, 3, mpt_send_max.clone()),
    ]);
    ledger.set_fees(fees);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &make_mpt_cash(Some(sponsor)),
            TxType::CHECK_CASH,
            Some(200),
        ),
        Ter::TEC_INSUFFICIENT_RESERVE
    );

    // A prefunded Sponsorship with no remaining object assignments cannot be
    // consumed even when the sponsor otherwise has enough XRP.
    let sponsorship_key =
        protocol::sponsorship_keylet(raw_account_id(sponsor), raw_account_id(destination));
    let empty_sponsorship =
        protocol::SponsorshipBuilder::new(sponsor, destination, 0, 0, Uint256::default(), 0)
            .set_remaining_owner_count(0)
            .build(sponsorship_key.key)
            .get_sle()
            .as_ref()
            .clone();
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(source, 1, 0, 1_000_000_000),
        account_root_with_balance(destination, 0, 0, 200),
        account_root_with_balance(sponsor, 0, 0, 1_000),
        account_root(mpt_issuer, 1, 0),
        mpt_issuance_entry(mpt_issuer, 1, 100, protocol::lsfMPTCanTransfer),
        mptoken_entry(source, mpt_id, 50),
        owner_dir_root(source, mpt_check.key),
        owner_dir_root(destination, mpt_check.key),
        check_entry(source, destination, 3, mpt_send_max.clone()),
        empty_sponsorship,
    ]);
    ledger.set_fees(fees);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &make_mpt_cash(Some(sponsor)),
            TxType::CHECK_CASH,
            Some(200),
        ),
        Ter::TEC_INSUFFICIENT_RESERVE
    );

    // The same low-reserve destination succeeds when a reserve sponsor can
    // carry the extra owner reserve, and all sponsorship metadata is updated.
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(source, 1, 0, 1_000_000_000),
        account_root_with_balance(destination, 0, 0, 200),
        account_root_with_balance(sponsor, 0, 0, 1_000),
        account_root(mpt_issuer, 1, 0),
        mpt_issuance_entry(mpt_issuer, 1, 100, protocol::lsfMPTCanTransfer),
        mptoken_entry(source, mpt_id, 50),
        owner_dir_root(source, mpt_check.key),
        owner_dir_root(destination, mpt_check.key),
        check_entry(source, destination, 3, mpt_send_max),
    ]);
    ledger.set_fees(fees);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let result = handle_real_dispatch(
        &mut view,
        &make_mpt_cash(Some(sponsor)),
        TxType::CHECK_CASH,
        Some(200),
    );
    assert_eq!(
        result,
        Ter::TES_SUCCESS,
        "{}",
        protocol::trans_token(result)
    );
    let destination_root = view
        .read(account_keylet(raw_account_id(destination)))
        .expect("destination read")
        .expect("destination root");
    let sponsor_root = view
        .read(account_keylet(raw_account_id(sponsor)))
        .expect("sponsor read")
        .expect("sponsor root");
    let token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(destination),
        ))
        .expect("token read")
        .expect("token exists");
    assert_eq!(token.get_account_id(sf("sfSponsor")), sponsor);
    assert_eq!(
        (
            destination_root.get_field_u32(sf("sfOwnerCount")),
            destination_root.get_field_u32(sf("sfSponsoredOwnerCount")),
            sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")),
        ),
        (1, 1, 1)
    );
}

#[test]
fn check_cash_delivered_amount_matches_xrp_amount_and_deliver_min_rules() {
    let source = sample_account(0xD7);
    let destination = sample_account(0xD8);
    let check_keylet = protocol::check_keylet(raw_account_id(source), 3);
    let send_max = test_xrp(500);

    for deliver_min in [false, true] {
        let ledger = empty_ledger(vec![
            account_root_with_balance(source, 1, 0, 1_000),
            account_root_with_balance(destination, 0, 0, 1_000),
            owner_dir_root(source, check_keylet.key),
            owner_dir_root(destination, check_keylet.key),
            check_entry(source, destination, 3, send_max.clone()),
        ]);
        let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
        let tx = STTx::new(TxType::CHECK_CASH, |object| {
            object.set_account_id(sf("sfAccount"), destination);
            object.set_field_h256(sf("sfCheckID"), check_keylet.key);
            object.set_field_amount(
                if deliver_min {
                    sf("sfDeliverMin")
                } else {
                    sf("sfAmount")
                },
                test_xrp(200),
            );
            object.set_field_amount(sf("sfFee"), test_xrp(10));
            object.set_field_u32(sf("sfSequence"), 1);
        });

        let (result, delivered_amount) =
            apply_submit_transactor_shell_with_delivered_amount(&mut view, &tx, TxType::CHECK_CASH);

        assert_eq!(result, Ter::TES_SUCCESS);
        assert_eq!(
            delivered_amount,
            deliver_min.then(|| test_xrp(500)),
            "XRP Amount has no delivered metadata; XRP DeliverMin records the actual maximum"
        );
    }
}

#[test]
fn sponsored_xrp_check_does_not_release_source_owner_reserve() {
    let source = sample_account(0xC7);
    let destination = sample_account(0xC8);
    let sponsor = sample_account(0xC9);
    let check_keylet = protocol::check_keylet(raw_account_id(source), 3);
    let cash = STTx::new(TxType::CHECK_CASH, |object| {
        object.set_account_id(sf("sfAccount"), destination);
        object.set_field_h256(sf("sfCheckID"), check_keylet.key);
        object.set_field_amount(sf("sfAmount"), test_xrp(50));
    });

    let make_view = |sponsored: bool| {
        let mut check = check_entry(source, destination, 3, test_xrp(50));
        if sponsored {
            check.set_account_id(sf("sfSponsor"), sponsor);
        }
        let mut ledger = empty_ledger(vec![
            // With reserve=200 and increment=50, this account can cash 50
            // only if deleting the Check releases its own owner increment.
            account_root_with_balance(source, 1, 0, 250),
            account_root_with_balance(destination, 0, 0, 1_000),
            owner_dir_root(source, check_keylet.key),
            owner_dir_root(destination, check_keylet.key),
            check,
        ]);
        ledger.set_fees(Fees {
            base: 10,
            reserve: 200,
            increment: 50,
        });
        ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE)
    };

    let mut unsponsored = make_view(false);
    assert_eq!(
        handle_real_dispatch(&mut unsponsored, &cash, TxType::CHECK_CASH, None),
        Ter::TES_SUCCESS
    );

    let mut sponsored = make_view(true);
    assert_eq!(
        handle_real_dispatch(&mut sponsored, &cash, TxType::CHECK_CASH, None),
        Ter::TEC_UNFUNDED_PAYMENT
    );
}

#[test]
fn check_cancel_releases_reserve_sponsor_counts() {
    let source = sample_account(0xCA);
    let destination = sample_account(0xCB);
    let sponsor = sample_account(0xCC);
    let check_keylet = protocol::check_keylet(raw_account_id(source), 3);
    let mut source_root = account_root_with_balance(source, 1, 0, 1_000);
    source_root.set_field_u32(sf("sfSponsoredOwnerCount"), 1);
    let mut sponsor_root = account_root_with_balance(sponsor, 0, 0, 1_000);
    sponsor_root.set_field_u32(sf("sfSponsoringOwnerCount"), 1);
    let mut check = check_entry(source, destination, 3, test_xrp(100));
    check.set_account_id(sf("sfSponsor"), sponsor);
    let ledger = empty_ledger(vec![
        source_root,
        account_root_with_balance(destination, 0, 0, 1_000),
        sponsor_root,
        owner_dir_root(source, check_keylet.key),
        owner_dir_root(destination, check_keylet.key),
        check,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let cancel = STTx::new(TxType::CHECK_CANCEL, |object| {
        object.set_account_id(sf("sfAccount"), source);
        object.set_field_h256(sf("sfCheckID"), check_keylet.key);
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &cancel, TxType::CHECK_CANCEL, None),
        Ter::TES_SUCCESS
    );
    assert!(view.read(check_keylet).expect("check read").is_none());
    let source_root = view
        .read(account_keylet(raw_account_id(source)))
        .expect("source read")
        .expect("source root");
    let sponsor_root = view
        .read(account_keylet(raw_account_id(sponsor)))
        .expect("sponsor read")
        .expect("sponsor root");
    assert_eq!(source_root.get_field_u32(sf("sfOwnerCount")), 0);
    assert_eq!(source_root.get_field_u32(sf("sfSponsoredOwnerCount")), 0);
    assert_eq!(sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")), 0);
}

#[test]
fn check_cash_releases_reserve_sponsor_counts() {
    let source = sample_account(0xCD);
    let destination = sample_account(0xCE);
    let sponsor = sample_account(0xCF);
    let check_keylet = protocol::check_keylet(raw_account_id(source), 3);
    let mut source_root = account_root_with_balance(source, 1, 0, 1_000);
    source_root.set_field_u32(sf("sfSponsoredOwnerCount"), 1);
    let mut sponsor_root = account_root_with_balance(sponsor, 0, 0, 1_000);
    sponsor_root.set_field_u32(sf("sfSponsoringOwnerCount"), 1);
    let mut check = check_entry(source, destination, 3, test_xrp(100));
    check.set_account_id(sf("sfSponsor"), sponsor);
    let ledger = empty_ledger(vec![
        source_root,
        account_root_with_balance(destination, 0, 0, 1_000),
        sponsor_root,
        owner_dir_root(source, check_keylet.key),
        owner_dir_root(destination, check_keylet.key),
        check,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let cash = STTx::new(TxType::CHECK_CASH, |object| {
        object.set_account_id(sf("sfAccount"), destination);
        object.set_field_h256(sf("sfCheckID"), check_keylet.key);
        object.set_field_amount(sf("sfAmount"), test_xrp(50));
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &cash, TxType::CHECK_CASH, None),
        Ter::TES_SUCCESS
    );
    let source_root = view
        .read(account_keylet(raw_account_id(source)))
        .expect("source read")
        .expect("source root");
    let sponsor_root = view
        .read(account_keylet(raw_account_id(sponsor)))
        .expect("sponsor read")
        .expect("sponsor root");
    assert_eq!(source_root.get_field_u32(sf("sfOwnerCount")), 0);
    assert_eq!(source_root.get_field_u32(sf("sfSponsoredOwnerCount")), 0);
    assert_eq!(sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")), 0);
}

#[test]
fn account_delete_records_remaining_balance_as_delivered_amount() {
    let source = sample_account(0xD9);
    let destination = sample_account(0xDA);
    let ledger = ledger_with_header(
        LedgerHeader {
            seq: 300,
            ..LedgerHeader::default()
        },
        vec![
            account_root_with_balance(source, 0, 0, 1_000),
            account_root_with_balance(destination, 0, 0, 2_000),
        ],
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::ACCOUNT_DELETE, |object| {
        object.set_account_id(sf("sfAccount"), source);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_amount(sf("sfFee"), test_xrp(10));
        object.set_field_u32(sf("sfSequence"), 1);
    });

    let (result, delivered_amount) =
        apply_submit_transactor_shell_with_delivered_amount(&mut view, &tx, TxType::ACCOUNT_DELETE);

    assert_eq!(result, Ter::TES_SUCCESS);
    assert_eq!(delivered_amount, Some(test_xrp(990)));
}

#[test]
fn account_delete_releases_sponsored_deposit_preauth_reserve() {
    let source = sample_account(0xDB);
    let destination = sample_account(0xDC);
    let authorized = sample_account(0xDD);
    let sponsor = destination;
    let preauth_keylet =
        protocol::deposit_preauth_keylet(raw_account_id(source), raw_account_id(authorized));
    let mut source_root = account_root_with_balance(source, 1, 0, 1_000);
    source_root.set_field_u32(sf("sfSponsoredOwnerCount"), 1);
    let mut destination_root = account_root_with_balance(destination, 0, 0, 2_000);
    destination_root.set_field_u32(sf("sfSponsoringOwnerCount"), 1);
    let mut preauth = STLedgerEntry::new(preauth_keylet);
    preauth.set_account_id(sf("sfAccount"), source);
    preauth.set_account_id(sf("sfAuthorize"), authorized);
    preauth.set_account_id(sf("sfSponsor"), sponsor);
    preauth.set_field_u64(sf("sfOwnerNode"), 0);
    let ledger = ledger_with_header(
        LedgerHeader {
            seq: 300,
            ..LedgerHeader::default()
        },
        vec![
            source_root,
            destination_root,
            account_root_with_balance(authorized, 0, 0, 2_000),
            owner_dir_root(source, preauth_keylet.key),
            preauth,
        ],
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::ACCOUNT_DELETE, |object| {
        object.set_account_id(sf("sfAccount"), source);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_amount(sf("sfFee"), test_xrp(10));
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::ACCOUNT_DELETE, None),
        Ter::TES_SUCCESS
    );
    assert!(
        view.read(account_keylet(raw_account_id(source)))
            .expect("source read")
            .is_none()
    );
    assert!(view.read(preauth_keylet).expect("preauth read").is_none());
    assert_eq!(
        view.read(account_keylet(raw_account_id(sponsor)))
            .expect("sponsor read")
            .expect("sponsor exists")
            .get_field_u32(sf("sfSponsoringOwnerCount")),
        0
    );
}

#[test]
fn fix_mpt_delivered_amount_records_actual_partial_mpt_delivery_only_when_enabled() {
    let source = sample_account(0xDA);
    let destination = sample_account(0xDB);
    let issuer = sample_account(0xDC);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = MPTIssue::new(mpt_id);
    let requested_amount =
        STAmount::from_mpt_amount(sf("sfAmount"), MPTAmount::from_value(1_000), mpt_issue);
    let expected_delivery =
        STAmount::from_mpt_amount(sf("sfAmount"), MPTAmount::from_value(800), mpt_issue);

    let expected_with_send_max =
        STAmount::from_mpt_amount(sf("sfAmount"), MPTAmount::from_value(960), mpt_issue);
    let partial_payment_cases = [
        (None, expected_delivery),
        (
            Some(STAmount::from_mpt_amount(
                sf("sfSendMax"),
                MPTAmount::from_value(1_200),
                mpt_issue,
            )),
            expected_with_send_max,
        ),
    ];

    for (send_max, expected_delivery) in partial_payment_cases {
        for amendment_enabled in [false, true] {
            let mut issuance = mpt_issuance_entry_with_transfer_fee(
                issuer,
                1,
                10_000,
                protocol::lsfMPTCanTransfer,
                25_000,
            );
            issuance.set_field_u64(sf("sfOutstandingAmount"), 10_000);
            let mut ledger = empty_ledger(vec![
                account_root_with_balance(source, 1, 0, 1_000_000_000),
                account_root_with_balance(destination, 0, 0, 1_000_000_000),
                account_root(issuer, 1, 0),
                issuance,
                mptoken_entry(source, mpt_id, 10_000),
            ]);
            if amendment_enabled {
                ledger.set_rules(protocol::Rules::new([protocol::fix_mpt_delivered_amount()]));
            }
            let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
            let tx = STTx::new(TxType::PAYMENT, |object| {
                object.set_account_id(sf("sfAccount"), source);
                object.set_account_id(sf("sfDestination"), destination);
                object.set_field_amount(sf("sfAmount"), requested_amount.clone());
                if let Some(send_max) = send_max.clone() {
                    object.set_field_amount(sf("sfSendMax"), send_max);
                }
                object.set_field_u32(sf("sfFlags"), 0x0002_0000); // tfPartialPayment
                object.set_field_amount(
                    sf("sfFee"),
                    STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
                );
                object.set_field_u32(sf("sfSequence"), 1);
            });

            let (result, delivered_amount) = apply_submit_transactor_shell_with_delivered_amount(
                &mut view,
                &tx,
                TxType::PAYMENT,
            );
            assert_eq!(result, Ter::TES_SUCCESS);
            assert_eq!(
                delivered_amount,
                amendment_enabled.then_some(expected_delivery.clone()),
                "fixMPTDeliveredAmount must record the net MPT delivery only when enabled"
            );

            let mut meta = TxMeta::new(tx.get_transaction_id(), 1);
            meta.set_delivered_amount(delivered_amount);
            let mut serializer = Serializer::default();
            meta.add_raw(&mut serializer, result, 0);
            let reparsed = TxMeta::from_raw(tx.get_transaction_id(), 1, serializer.data());
            assert_eq!(
                reparsed.get_delivered_amount(),
                amendment_enabled.then_some(&expected_delivery),
                "sfDeliveredAmount presence must follow the amendment gate"
            );
        }
    }
}

#[test]
fn amendment_pseudo_transaction_serializes_and_replays_each_public_testnet_target() {
    let amendments = [
        protocol::feature_id("fixCleanup3_1_3"),
        protocol::feature_id("fixIncludeKeyletFields"),
        protocol::feature_id("fixTokenEscrowV1"),
        protocol::feature_id("fixPriceOracleOrder"),
        protocol::feature_id("fixMPTDeliveredAmount"),
        protocol::feature_id("fixAMMClawbackRounding"),
    ];
    let config = LedgerConfig::new(
        Fees {
            base: 10,
            reserve: 20,
            increment: 30,
        },
        FeatureSet::new([]),
    );

    for target in amendments {
        let mut view = ApplyViewImpl::new(Arc::new(empty_ledger(Vec::new())), ApplyFlags::NONE);
        let pseudo_transaction = STTx::new(TxType::AMENDMENT, |tx| {
            tx.set_field_h256(sf("sfAmendment"), target);
            tx.set_field_u32(sf("sfFlags"), 0);
        });
        assert_eq!(
            handle_real_dispatch(&mut view, &pseudo_transaction, TxType::AMENDMENT, None),
            Ter::TES_SUCCESS
        );

        let serialized_amendments = view
            .read(protocol::amendments_keylet())
            .expect("Amendments SLE read should succeed")
            .expect("Amendment pseudo-transaction should create the Amendments SLE")
            .get_serializer()
            .data()
            .to_vec();

        for replay_seq in [2, 3] {
            let mut tree = MutableTree::new(1);
            tree.add_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(protocol::amendments_key(), serialized_amendments.clone()),
            )
            .expect("serialized Amendments SLE should insert");
            let mut replay = Ledger::from_maps(
                LedgerHeader {
                    seq: replay_seq,
                    ..LedgerHeader::default()
                },
                SyncTree::from_root_with_type(
                    tree.root(),
                    SHAMapType::State,
                    false,
                    replay_seq,
                    SyncState::Immutable,
                ),
                SyncTree::new_with_type(SHAMapType::Transaction, false, replay_seq),
            );
            assert!(
                replay
                    .setup_from_state_map_with_config(&config)
                    .expect("fresh ledger should decode pseudo-transaction bytes")
            );
            assert_eq!(
                replay.get_enabled_amendments(),
                std::collections::BTreeSet::from([target])
            );
            assert!(replay.rules().enabled(&target));
            for other in amendments {
                if other != target {
                    assert!(!replay.rules().enabled(&other));
                }
            }
        }
    }
}

#[test]
fn fee_pseudo_transaction_creates_typed_fee_settings_entry_and_persists() {
    // Match Change::applyFee's missing-object path. The state batch must receive
    // a standalone FeeSettings SLE, including sfLedgerEntryType, rather than an
    // untyped generic object.
    let mut ledger = empty_ledger(Vec::new());
    let mut view = Sandbox::new(Arc::new(ledger.clone()), ApplyFlags::NONE);
    let pseudo_transaction = STTx::new(TxType::FEE, |tx| {
        tx.set_field_u64(sf("sfBaseFee"), 10);
        tx.set_field_u32(sf("sfReferenceFeeUnits"), 10);
        tx.set_field_u32(sf("sfReserveBase"), 20);
        tx.set_field_u32(sf("sfReserveIncrement"), 30);
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &pseudo_transaction, TxType::FEE, None),
        Ter::TES_SUCCESS
    );
    let fee_settings = view
        .read(protocol::fee_settings_keylet())
        .expect("FeeSettings SLE read should succeed")
        .expect("Fee pseudo-transaction should create the FeeSettings SLE");
    assert_eq!(fee_settings.get_type(), LedgerEntryType::FeeSettings);

    view.apply(&mut ledger)
        .expect("typed FeeSettings payload should survive state-batch decoding");
    assert_eq!(
        ledger
            .read(protocol::fee_settings_keylet())
            .expect("persisted FeeSettings SLE read should succeed")
            .expect("persisted FeeSettings SLE should exist")
            .get_type(),
        LedgerEntryType::FeeSettings
    );
}

#[test]
fn fee_pseudo_transaction_xrp_fees_replaces_legacy_fields_and_persists() {
    // `Change::applyFee` uses the ledger amendment state, rather than the
    // incoming field shape, and removes all legacy fee fields in XRPFees mode.
    let keylet = protocol::fee_settings_keylet();
    let mut legacy_fee_settings = STLedgerEntry::new(keylet);
    legacy_fee_settings.set_field_u64(sf("sfBaseFee"), 10);
    legacy_fee_settings.set_field_u32(sf("sfReferenceFeeUnits"), 10);
    legacy_fee_settings.set_field_u32(sf("sfReserveBase"), 20);
    legacy_fee_settings.set_field_u32(sf("sfReserveIncrement"), 30);

    let mut ledger = empty_ledger(vec![legacy_fee_settings]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_xrp_fees()]));
    let mut view = Sandbox::new(Arc::new(ledger.clone()), ApplyFlags::NONE);
    let pseudo_transaction = STTx::new(TxType::FEE, |tx| {
        tx.set_field_amount(sf("sfBaseFeeDrops"), test_xrp(12));
        tx.set_field_amount(sf("sfReserveBaseDrops"), test_xrp(22));
        tx.set_field_amount(sf("sfReserveIncrementDrops"), test_xrp(32));
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &pseudo_transaction, TxType::FEE, None),
        Ter::TES_SUCCESS
    );
    let fee_settings = view
        .read(keylet)
        .expect("FeeSettings SLE read should succeed")
        .expect("FeeSettings SLE should remain present");
    assert_eq!(fee_settings.get_type(), LedgerEntryType::FeeSettings);
    assert_eq!(
        fee_settings.get_field_amount(sf("sfBaseFeeDrops")),
        test_xrp(12)
    );
    assert_eq!(
        fee_settings.get_field_amount(sf("sfReserveBaseDrops")),
        test_xrp(22)
    );
    assert_eq!(
        fee_settings.get_field_amount(sf("sfReserveIncrementDrops")),
        test_xrp(32)
    );
    for legacy_field in [
        sf("sfBaseFee"),
        sf("sfReferenceFeeUnits"),
        sf("sfReserveBase"),
        sf("sfReserveIncrement"),
    ] {
        assert!(
            !fee_settings.is_field_present(legacy_field),
            "XRPFees FeeSettings must not retain {}",
            legacy_field.name()
        );
    }

    view.apply(&mut ledger)
        .expect("XRPFees FeeSettings payload should survive state-batch decoding");
    let persisted = ledger
        .read(keylet)
        .expect("persisted FeeSettings SLE read should succeed")
        .expect("persisted FeeSettings SLE should exist");
    assert_eq!(persisted.get_type(), LedgerEntryType::FeeSettings);
    assert_eq!(
        persisted.get_field_amount(sf("sfBaseFeeDrops")),
        test_xrp(12)
    );
    assert!(!persisted.is_field_present(sf("sfBaseFee")));
}

#[test]
fn conditional_escrow_create_persists_condition_and_finish_requires_matching_fulfillment() {
    let owner = sample_account(0xE1);
    let destination = sample_account(0xE2);
    let amount = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let condition = [
        0xA0, 0x25, 0x80, 0x20, 0x2C, 0xF2, 0x4D, 0xBA, 0x5F, 0xB0, 0xA3, 0x0E, 0x26, 0xE8, 0x3B,
        0x2A, 0xC5, 0xB9, 0xE2, 0x9E, 0x1B, 0x16, 0x1E, 0x5C, 0x1F, 0xA7, 0x42, 0x5E, 0x73, 0x04,
        0x33, 0x62, 0x93, 0x8B, 0x98, 0x24, 0x81, 0x01, 0x05,
    ];
    let fulfillment = [0xA0, 0x07, 0x80, 0x05, b'h', b'e', b'l', b'l', b'o'];

    let mut create_view = ApplyViewImpl::new(
        Arc::new(empty_ledger(vec![
            account_root_with_balance(owner, 0, 0, 1_000_000),
            account_root_with_balance(destination, 0, 0, 1_000_000),
        ])),
        ApplyFlags::NONE,
    );
    let create = STTx::new(TxType::ESCROW_CREATE, |tx| {
        tx.set_account_id(sf("sfAccount"), owner);
        tx.set_account_id(sf("sfDestination"), destination);
        tx.set_field_amount(sf("sfAmount"), amount.clone());
        tx.set_field_u32(sf("sfFinishAfter"), 1);
        tx.set_field_vl(sf("sfCondition"), &condition);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });
    assert_eq!(
        handle_real_dispatch(&mut create_view, &create, TxType::ESCROW_CREATE, None),
        Ter::TES_SUCCESS
    );
    let created = create_view
        .read(protocol::escrow_keylet(raw_account_id(owner), 1))
        .expect("created escrow read")
        .expect("conditional escrow should exist");
    assert_eq!(created.get_field_vl(sf("sfCondition")), condition);

    let escrow_keylet = protocol::escrow_keylet(raw_account_id(owner), 1);
    let mut escrow = STLedgerEntry::from_type_and_key(LedgerEntryType::Escrow, escrow_keylet.key);
    escrow.set_account_id(sf("sfAccount"), owner);
    escrow.set_account_id(sf("sfDestination"), destination);
    escrow.set_field_amount(sf("sfAmount"), amount);
    escrow.set_field_u32(sf("sfFinishAfter"), 1);
    escrow.set_field_vl(sf("sfCondition"), &condition);
    escrow.set_field_u64(sf("sfOwnerNode"), 0);
    let finish_ledger = ledger_with_header(
        LedgerHeader {
            seq: 2,
            parent_close_time: 2,
            ..LedgerHeader::default()
        },
        vec![
            account_root_with_balance(owner, 1, 0, 1_000_000),
            account_root_with_balance(destination, 0, 0, 1_000_000),
            owner_dir_root(owner, escrow_keylet.key),
            escrow,
        ],
    );
    let finish_tx = |condition: Option<&[u8]>, fulfillment: Option<&[u8]>| {
        STTx::new(TxType::ESCROW_FINISH, |tx| {
            tx.set_account_id(sf("sfAccount"), destination);
            tx.set_account_id(sf("sfOwner"), owner);
            tx.set_field_u32(sf("sfOfferSequence"), 1);
            if let Some(condition) = condition {
                tx.set_field_vl(sf("sfCondition"), condition);
            }
            if let Some(fulfillment) = fulfillment {
                tx.set_field_vl(sf("sfFulfillment"), fulfillment);
            }
            tx.set_field_amount(
                sf("sfFee"),
                STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
            );
            tx.set_field_u32(sf("sfSequence"), 1);
        })
    };

    let mut missing_fulfillment =
        ApplyViewImpl::new(Arc::new(finish_ledger.clone()), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut missing_fulfillment,
            &finish_tx(None, None),
            TxType::ESCROW_FINISH,
            Some(1_000_000),
        ),
        Ter::TEC_CRYPTOCONDITION_ERROR
    );
    assert!(
        missing_fulfillment
            .read(escrow_keylet)
            .expect("escrow read after failed finish")
            .is_some()
    );

    let mut malformed = ApplyViewImpl::new(Arc::new(finish_ledger.clone()), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut malformed,
            &finish_tx(Some(&condition), None),
            TxType::ESCROW_FINISH,
            Some(1_000_000),
        ),
        Ter::TEM_MALFORMED
    );

    let mut successful = ApplyViewImpl::new(Arc::new(finish_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut successful,
            &finish_tx(Some(&condition), Some(&fulfillment)),
            TxType::ESCROW_FINISH,
            Some(1_000_000),
        ),
        Ter::TES_SUCCESS
    );
    assert!(
        successful
            .read(escrow_keylet)
            .expect("escrow read after successful finish")
            .is_none()
    );
    assert_eq!(
        successful
            .read(account_keylet(raw_account_id(destination)))
            .expect("destination account read")
            .expect("destination account")
            .get_field_amount(sf("sfBalance"))
            .xrp()
            .drops(),
        1_000_100
    );
}

#[test]
fn escrow_create_mpt_obeys_token_and_mpt_feature_gates_then_locks_balance() {
    let owner = sample_account(0xE3);
    let destination = sample_account(0xE4);
    let issuer = sample_account(0xE5);
    let issuance_id = share_id_for(issuer, 1);
    let amount = STAmount::from_mpt_amount(
        sf("sfAmount"),
        MPTAmount::from_value(100),
        MPTIssue::new(issuance_id),
    );
    let create = STTx::new(TxType::ESCROW_CREATE, |tx| {
        tx.set_account_id(sf("sfAccount"), owner);
        tx.set_account_id(sf("sfDestination"), destination);
        tx.set_field_amount(sf("sfAmount"), amount.clone());
        tx.set_field_u32(sf("sfFinishAfter"), 1);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });
    let base_ledger = || {
        empty_ledger(vec![
            account_root_with_balance(owner, 0, 0, 1_000_000),
            account_root_with_balance(destination, 0, 0, 1_000_000),
            account_root_with_balance(issuer, 0, 0, 1_000_000),
            mpt_issuance_entry(
                issuer,
                1,
                10_000,
                MPT_CAN_ESCROW_FLAG | MPT_CAN_TRANSFER_FLAG,
            ),
            mptoken_entry(owner, issuance_id, 1_000),
        ])
    };

    for (features, expected) in [
        (Vec::new(), Ter::TEM_BAD_AMOUNT),
        (vec![protocol::feature_token_escrow()], Ter::TEM_DISABLED),
    ] {
        let mut ledger = base_ledger();
        ledger.set_rules(protocol::Rules::new(features));
        let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
        assert_eq!(
            handle_real_dispatch(&mut view, &create, TxType::ESCROW_CREATE, None),
            expected
        );
    }

    let mut ledger = base_ledger();
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_token_escrow(),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut view, &create, TxType::ESCROW_CREATE, None),
        Ter::TES_SUCCESS
    );
    let source_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            issuance_id,
            raw_account_id(owner),
        ))
        .expect("source token read")
        .expect("source token");
    assert_eq!(source_token.get_field_u64(sf("sfMPTAmount")), 900);
    assert_eq!(source_token.get_field_u64(sf("sfLockedAmount")), 100);
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(issuance_id))
        .expect("issuance read")
        .expect("issuance");
    assert_eq!(issuance.get_field_u64(sf("sfLockedAmount")), 100);
    assert!(
        view.read(protocol::escrow_keylet(raw_account_id(owner), 1))
            .expect("escrow read")
            .is_some()
    );
}

#[test]
fn mpt_escrow_create_then_finish_tracks_gross_lock_across_fix_token_escrow_v1() {
    let owner = sample_account(0xE6);
    let destination = sample_account(0xE7);
    let issuer = sample_account(0xE8);
    let issuance_id = share_id_for(issuer, 1);
    let amount = STAmount::from_mpt_amount(
        sf("sfAmount"),
        MPTAmount::from_value(125),
        MPTIssue::new(issuance_id),
    );

    for amendment_enabled in [false, true] {
        let mut ledger = empty_ledger(vec![
            account_root_with_balance(owner, 0, 0, 1_000_000),
            account_root_with_balance(destination, 0, 0, 1_000_000),
            account_root_with_balance(issuer, 0, 0, 1_000_000),
            mpt_issuance_entry_with_transfer_fee(
                issuer,
                1,
                1_000,
                MPT_CAN_ESCROW_FLAG | MPT_CAN_TRANSFER_FLAG,
                25_000,
            ),
            mptoken_entry(owner, issuance_id, 1_000),
            mptoken_entry(destination, issuance_id, 0),
        ]);
        let mut features = vec![
            protocol::feature_token_escrow(),
            protocol::feature_id("MPTokensV1"),
        ];
        if amendment_enabled {
            features.push(protocol::feature_id("fixTokenEscrowV1"));
        }
        ledger.set_rules(protocol::Rules::new(features));

        let create = STTx::new(TxType::ESCROW_CREATE, |tx| {
            tx.set_account_id(sf("sfAccount"), owner);
            tx.set_account_id(sf("sfDestination"), destination);
            tx.set_field_amount(sf("sfAmount"), amount.clone());
            tx.set_field_u32(sf("sfFinishAfter"), 1);
            tx.set_field_amount(sf("sfFee"), test_xrp(10));
            tx.set_field_u32(sf("sfSequence"), 1);
        });
        let mut create_view = Sandbox::new(Arc::new(ledger.clone()), ApplyFlags::NONE);
        assert_eq!(
            handle_real_dispatch(&mut create_view, &create, TxType::ESCROW_CREATE, None),
            Ter::TES_SUCCESS,
            "MPT escrow creation must succeed with amendment enabled={amendment_enabled}"
        );
        create_view
            .apply(&mut ledger)
            .expect("MPT escrow creation should apply");

        let source_after_create = ledger
            .read(protocol::mptoken_keylet_from_mptid(
                issuance_id,
                raw_account_id(owner),
            ))
            .expect("source holding read after create")
            .expect("source holding after create");
        let issuance_after_create = ledger
            .read(protocol::mpt_issuance_keylet_from_mptid(issuance_id))
            .expect("issuance read after create")
            .expect("issuance after create");
        assert_eq!(source_after_create.get_field_u64(sf("sfMPTAmount")), 875);
        assert_eq!(source_after_create.get_field_u64(sf("sfLockedAmount")), 125);
        assert_eq!(
            issuance_after_create.get_field_u64(sf("sfLockedAmount")),
            125
        );
        assert_eq!(owner_count(&ledger, owner), 1);
        assert!(
            ledger
                .read(owner_dir_keylet(raw_account_id(owner)))
                .expect("owner directory after create")
                .is_some()
        );
        assert!(
            ledger
                .read(owner_dir_keylet(raw_account_id(destination)))
                .expect("destination directory after create")
                .is_some()
        );

        let mut header = ledger.header();
        header.parent_close_time = 2;
        ledger.set_ledger_info(header);
        let finish = STTx::new(TxType::ESCROW_FINISH, |tx| {
            tx.set_account_id(sf("sfAccount"), destination);
            tx.set_account_id(sf("sfOwner"), owner);
            tx.set_field_u32(sf("sfOfferSequence"), 1);
            tx.set_field_amount(sf("sfFee"), test_xrp(10));
            tx.set_field_u32(sf("sfSequence"), 1);
        });
        let mut finish_view = Sandbox::new(Arc::new(ledger.clone()), ApplyFlags::NONE);
        assert_eq!(
            dispatch_with_pre_fee_balance(&mut finish_view, &finish, TxType::ESCROW_FINISH),
            Ter::TES_SUCCESS,
            "MPT escrow finish must succeed with amendment enabled={amendment_enabled}"
        );
        finish_view
            .apply(&mut ledger)
            .expect("MPT escrow finish should apply");

        let source_after_finish = ledger
            .read(protocol::mptoken_keylet_from_mptid(
                issuance_id,
                raw_account_id(owner),
            ))
            .expect("source holding read after finish")
            .expect("source holding after finish");
        let destination_after_finish = ledger
            .read(protocol::mptoken_keylet_from_mptid(
                issuance_id,
                raw_account_id(destination),
            ))
            .expect("destination holding read after finish")
            .expect("destination holding after finish");
        let issuance_after_finish = ledger
            .read(protocol::mpt_issuance_keylet_from_mptid(issuance_id))
            .expect("issuance read after finish")
            .expect("issuance after finish");
        assert_eq!(source_after_finish.get_field_u64(sf("sfMPTAmount")), 875);
        assert_eq!(
            destination_after_finish.get_field_u64(sf("sfMPTAmount")),
            100
        );
        assert_eq!(
            source_after_finish.is_field_present(sf("sfLockedAmount")),
            !amendment_enabled,
            "legacy finish leaves the fee remainder locked; fixTokenEscrowV1 unlocks gross"
        );
        assert_eq!(
            issuance_after_finish.is_field_present(sf("sfLockedAmount")),
            !amendment_enabled,
            "issuance lock must follow the same gross/net behavior"
        );
        if amendment_enabled {
            assert_eq!(
                issuance_after_finish.get_field_u64(sf("sfOutstandingAmount")),
                975
            );
        } else {
            assert_eq!(source_after_finish.get_field_u64(sf("sfLockedAmount")), 25);
            assert_eq!(
                issuance_after_finish.get_field_u64(sf("sfLockedAmount")),
                25
            );
            assert_eq!(
                issuance_after_finish.get_field_u64(sf("sfOutstandingAmount")),
                1_000
            );
        }
        assert_eq!(owner_count(&ledger, owner), 0);
        assert!(
            ledger
                .read(protocol::escrow_keylet(raw_account_id(owner), 1))
                .expect("escrow read after finish")
                .is_none()
        );
        for account in [owner, destination] {
            let directory = ledger
                .read(owner_dir_keylet(raw_account_id(account)))
                .expect("directory after finish")
                .expect("rippled preserves the empty owner-directory root");
            assert!(directory.get_field_v256(sf("sfIndexes")).value().is_empty());
        }
    }
}

#[test]
fn mpt_escrow_create_then_cancel_enforces_boundary_and_releases_full_lock() {
    let owner = sample_account(0xE9);
    let destination = sample_account(0xEA);
    let issuer = sample_account(0xEB);
    let issuance_id = share_id_for(issuer, 1);
    let amount = STAmount::from_mpt_amount(
        sf("sfAmount"),
        MPTAmount::from_value(125),
        MPTIssue::new(issuance_id),
    );

    for amendment_enabled in [false, true] {
        let mut ledger = empty_ledger(vec![
            account_root_with_balance(owner, 0, 0, 1_000_000),
            account_root_with_balance(destination, 0, 0, 1_000_000),
            account_root_with_balance(issuer, 0, 0, 1_000_000),
            mpt_issuance_entry(
                issuer,
                1,
                1_000,
                MPT_CAN_ESCROW_FLAG | MPT_CAN_TRANSFER_FLAG,
            ),
            mptoken_entry(owner, issuance_id, 1_000),
            mptoken_entry(destination, issuance_id, 0),
        ]);
        let mut features = vec![
            protocol::feature_token_escrow(),
            protocol::feature_id("MPTokensV1"),
        ];
        if amendment_enabled {
            features.push(protocol::feature_id("fixTokenEscrowV1"));
        }
        ledger.set_rules(protocol::Rules::new(features));

        let create = STTx::new(TxType::ESCROW_CREATE, |tx| {
            tx.set_account_id(sf("sfAccount"), owner);
            tx.set_account_id(sf("sfDestination"), destination);
            tx.set_field_amount(sf("sfAmount"), amount.clone());
            tx.set_field_u32(sf("sfFinishAfter"), 0);
            tx.set_field_u32(sf("sfCancelAfter"), 1);
            tx.set_field_amount(sf("sfFee"), test_xrp(10));
            tx.set_field_u32(sf("sfSequence"), 1);
        });
        let mut create_view = Sandbox::new(Arc::new(ledger.clone()), ApplyFlags::NONE);
        assert_eq!(
            handle_real_dispatch(&mut create_view, &create, TxType::ESCROW_CREATE, None),
            Ter::TES_SUCCESS
        );
        create_view
            .apply(&mut ledger)
            .expect("MPT cancel escrow creation should apply");

        let mut header = ledger.header();
        header.parent_close_time = 1;
        ledger.set_ledger_info(header);
        let cancel = STTx::new(TxType::ESCROW_CANCEL, |tx| {
            tx.set_account_id(sf("sfAccount"), owner);
            tx.set_account_id(sf("sfOwner"), owner);
            tx.set_field_u32(sf("sfOfferSequence"), 1);
            tx.set_field_amount(sf("sfFee"), test_xrp(10));
            tx.set_field_u32(sf("sfSequence"), 2);
        });
        let mut boundary_view = Sandbox::new(Arc::new(ledger.clone()), ApplyFlags::NONE);
        assert_eq!(
            dispatch_with_pre_fee_balance(&mut boundary_view, &cancel, TxType::ESCROW_CANCEL),
            Ter::TEC_NO_PERMISSION,
            "CancelAfter is not cancellable at its exact boundary"
        );

        let mut header = ledger.header();
        header.parent_close_time = 2;
        ledger.set_ledger_info(header);
        let mut cancel_view = Sandbox::new(Arc::new(ledger.clone()), ApplyFlags::NONE);
        assert_eq!(
            dispatch_with_pre_fee_balance(&mut cancel_view, &cancel, TxType::ESCROW_CANCEL),
            Ter::TES_SUCCESS,
            "MPT escrow cancel must succeed after CancelAfter with amendment enabled={amendment_enabled}"
        );
        cancel_view
            .apply(&mut ledger)
            .expect("MPT escrow cancel should apply");

        let source_after_cancel = ledger
            .read(protocol::mptoken_keylet_from_mptid(
                issuance_id,
                raw_account_id(owner),
            ))
            .expect("source holding read after cancel")
            .expect("source holding after cancel");
        let destination_after_cancel = ledger
            .read(protocol::mptoken_keylet_from_mptid(
                issuance_id,
                raw_account_id(destination),
            ))
            .expect("destination holding read after cancel")
            .expect("destination holding after cancel");
        let issuance_after_cancel = ledger
            .read(protocol::mpt_issuance_keylet_from_mptid(issuance_id))
            .expect("issuance read after cancel")
            .expect("issuance after cancel");
        assert_eq!(source_after_cancel.get_field_u64(sf("sfMPTAmount")), 1_000);
        assert_eq!(destination_after_cancel.get_field_u64(sf("sfMPTAmount")), 0);
        assert!(!source_after_cancel.is_field_present(sf("sfLockedAmount")));
        assert!(!issuance_after_cancel.is_field_present(sf("sfLockedAmount")));
        assert_eq!(
            issuance_after_cancel.get_field_u64(sf("sfOutstandingAmount")),
            1_000
        );
        assert_eq!(owner_count(&ledger, owner), 0);
        assert!(
            ledger
                .read(protocol::escrow_keylet(raw_account_id(owner), 1))
                .expect("escrow read after cancel")
                .is_none()
        );
        for account in [owner, destination] {
            let directory = ledger
                .read(owner_dir_keylet(raw_account_id(account)))
                .expect("directory after cancel")
                .expect("rippled preserves the empty owner-directory root");
            assert!(directory.get_field_v256(sf("sfIndexes")).value().is_empty());
        }
    }
}

#[test]
fn mpt_escrow_cancel_missing_owner_holding_matches_cleanup_3_2_0_boundary() {
    let owner = sample_account(0xB1);
    let destination = sample_account(0xB2);
    let issuer = sample_account(0xB3);
    let issuance_id = share_id_for(issuer, 1);
    let escrow_key = protocol::escrow_keylet(raw_account_id(owner), 1);
    let amount = STAmount::from_mpt_amount(
        sf("sfAmount"),
        MPTAmount::from_value(125),
        MPTIssue::new(issuance_id),
    );
    let mut escrow = STLedgerEntry::from_type_and_key(LedgerEntryType::Escrow, escrow_key.key);
    escrow.set_account_id(sf("sfAccount"), owner);
    escrow.set_account_id(sf("sfDestination"), destination);
    escrow.set_field_amount(sf("sfAmount"), amount);
    escrow.set_field_u32(sf("sfCancelAfter"), 1);
    escrow.set_field_u64(sf("sfOwnerNode"), 0);
    let cancel = STTx::new(TxType::ESCROW_CANCEL, |tx| {
        tx.set_account_id(sf("sfAccount"), owner);
        tx.set_account_id(sf("sfOwner"), owner);
        tx.set_field_u32(sf("sfOfferSequence"), 1);
        tx.set_field_amount(sf("sfFee"), test_xrp(10));
        tx.set_field_u32(sf("sfSequence"), 2);
    });

    for (cleanup_enabled, expected) in [
        (false, Ter::TEF_INTERNAL),
        (true, Ter::TEC_INSUFFICIENT_RESERVE),
    ] {
        let mut issuance = mpt_issuance_entry(
            issuer,
            1,
            1_000,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRANSFER_FLAG,
        );
        issuance.set_field_u64(sf("sfLockedAmount"), 125);
        let mut ledger = ledger_with_header(
            LedgerHeader {
                seq: 2,
                parent_close_time: 2,
                ..LedgerHeader::default()
            },
            vec![
                account_root_with_balance(owner, 1, 0, 0),
                account_root_with_balance(destination, 0, 0, 1_000_000),
                account_root_with_balance(issuer, 0, 0, 1_000_000),
                issuance,
                owner_dir_root(owner, escrow_key.key),
                escrow.clone(),
            ],
        );
        let mut features = vec![
            protocol::feature_token_escrow(),
            protocol::feature_id("MPTokensV1"),
        ];
        if cleanup_enabled {
            features.push(protocol::feature_id("fixCleanup3_2_0"));
        }
        ledger.set_fees(Fees {
            base: 10,
            reserve: 200,
            increment: 50,
        });
        ledger.set_rules(protocol::Rules::new(features));
        let mut view = Sandbox::new(Arc::new(ledger), ApplyFlags::NONE);
        assert_eq!(
            dispatch_with_pre_fee_balance(&mut view, &cancel, TxType::ESCROW_CANCEL),
            expected,
            "fixCleanup3_2_0 enabled={cleanup_enabled}"
        );
    }
}

#[test]
fn payment_transfers_mpt_without_rewriting_issue() {
    let source = sample_account(0xD7);
    let destination = sample_account(0xD8);
    let issuer = sample_account(0xD9);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let amount = STAmount::from_mpt_amount(
        get_field_by_symbol("sfAmount"),
        protocol::MPTAmount::from_value(10),
        mpt_issue,
    );
    let ledger = empty_ledger(vec![
        account_root_with_balance(source, 1, 0, 1_000_000_000),
        account_root_with_balance(destination, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        mpt_issuance_entry(issuer, 1, 100, protocol::lsfMPTCanTransfer),
        mptoken_entry(source, mpt_id, 50),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::PAYMENT, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), source);
        object.set_account_id(get_field_by_symbol("sfDestination"), destination);
        object.set_field_amount(get_field_by_symbol("sfAmount"), amount);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = dispatch_with_pre_fee_balance(&mut view, &tx, TxType::PAYMENT);

    assert_eq!(result, Ter::TES_SUCCESS);
    let source_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(source),
        ))
        .expect("source token read should succeed")
        .expect("source token should exist");
    let destination_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(destination),
        ))
        .expect("destination token read should succeed")
        .expect("destination token should be created");
    assert_eq!(
        source_token.get_field_u64(get_field_by_symbol("sfMPTAmount")),
        40
    );
    assert_eq!(
        destination_token.get_field_u64(get_field_by_symbol("sfMPTAmount")),
        10
    );
}

#[test]
fn direct_xrp_payment_preserves_fee_when_fee_exceeds_source_reserve() {
    let source = sample_account(0xA1);
    let destination = sample_account(0xA2);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(source, 0, 0, 599),
        account_root_with_balance(destination, 0, 0, 0),
    ]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 200,
        increment: 50,
    });
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = direct_xrp_payment_tx(source, destination, 100, 500);

    // 599 covers amount + reserve, but not amount + max(reserve, Fee).
    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::PAYMENT, Some(599)),
        Ter::TEC_UNFUNDED_PAYMENT
    );
}

#[test]
fn payment_sponsor_created_account_tracks_base_reserve_sponsorship() {
    let source = sample_account(0xB1);
    let destination = sample_account(0xB2);
    let mut ledger = empty_ledger(vec![account_root_with_balance(source, 0, 0, 1_000)]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 200,
        increment: 50,
    });
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("Sponsor")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::PAYMENT, |object| {
        object.set_account_id(sf("sfAccount"), source);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_amount(sf("sfAmount"), test_xrp(1));
        object.set_field_u32(sf("sfFlags"), protocol::tfSponsorCreatedAccount);
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::PAYMENT, Some(1_000)),
        Ter::TES_SUCCESS
    );
    let destination_root = view
        .read(account_keylet(raw_account_id(destination)))
        .expect("destination read")
        .expect("sponsored destination");
    assert_eq!(destination_root.get_account_id(sf("sfSponsor")), source);
    assert_eq!(
        destination_root.get_field_amount(sf("sfBalance")),
        test_xrp(1)
    );
    let source_root = view
        .read(account_keylet(raw_account_id(source)))
        .expect("source read")
        .expect("sponsor source");
    assert_eq!(source_root.get_field_u32(sf("sfSponsoringAccountCount")), 1);
    assert_eq!(source_root.get_field_amount(sf("sfBalance")), test_xrp(999));
}

#[test]
fn direct_xrp_payment_reserve_only_sponsor_does_not_override_initiator_fee_payer() {
    let source = sample_account(0xB1);
    let destination = sample_account(0xB2);
    let delegate = sample_account(0xB3);
    let sponsor = sample_account(0xB4);

    let make_ledger = || {
        let mut ledger = empty_ledger(vec![
            account_root_with_balance(source, 0, 0, 599),
            account_root_with_balance(destination, 0, 0, 0),
            account_root_with_balance(delegate, 0, 0, 1_000),
            account_root_with_balance(sponsor, 0, 0, 1_000),
        ]);
        ledger.set_fees(Fees {
            base: 10,
            reserve: 200,
            increment: 50,
        });
        ledger
    };

    let mut account_paid = direct_xrp_payment_tx(source, destination, 100, 500);
    account_paid.set_account_id(sf("sfSponsor"), sponsor);
    account_paid.set_field_u32(sf("sfSponsorFlags"), 2);
    let mut account_view = ApplyViewImpl::new(Arc::new(make_ledger()), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut account_view, &account_paid, TxType::PAYMENT, Some(599),),
        Ter::TEC_UNFUNDED_PAYMENT,
        "reserve-only sponsor leaves sfAccount responsible for the fee"
    );

    let mut delegate_paid = account_paid.clone();
    delegate_paid.set_account_id(sf("sfDelegate"), delegate);
    let mut delegate_view = ApplyViewImpl::new(Arc::new(make_ledger()), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut delegate_view,
            &delegate_paid,
            TxType::PAYMENT,
            Some(599),
        ),
        Ter::TES_SUCCESS,
        "reserve-only sponsor leaves sfDelegate responsible for the fee"
    );
}

#[test]
fn direct_xrp_payment_rejects_every_registered_pseudo_account_kind() {
    let source = sample_account(0xA3);
    for (index, discriminator) in ["sfAMMID", "sfVaultID", "sfLoanBrokerID"]
        .into_iter()
        .enumerate()
    {
        let destination = sample_account(0xA4 + index as u8);
        let mut pseudo = account_root_with_balance(destination, 0, 0, 0);
        pseudo.set_field_h256(sf(discriminator), sample_uint256(0xB0 + index as u8));
        let mut ledger = empty_ledger(vec![account_root_with_balance(source, 0, 0, 1_000), pseudo]);
        ledger.set_fees(Fees {
            base: 10,
            reserve: 200,
            increment: 50,
        });
        let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
        let tx = direct_xrp_payment_tx(source, destination, 1, 10);

        assert_eq!(
            handle_real_dispatch(&mut view, &tx, TxType::PAYMENT, Some(1_000)),
            Ter::TEC_NO_PERMISSION,
            "{discriminator} must identify a pseudo-account"
        );
    }
}

#[test]
fn delegated_single_sign_reaches_apply_after_shared_preclaim_authorization() {
    let source = sample_account(0xA8);
    let destination = sample_account(0xA9);
    let delegate = sample_account(0xAA);
    let ledger = empty_ledger(vec![
        account_root_with_balance(source, 0, 0, 1_000_000),
        account_root_with_balance(destination, 0, 0, 0),
        account_root_with_balance(delegate, 0, 0, 1_000_000),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let mut tx = direct_xrp_payment_tx(source, destination, 100, 10);
    tx.set_account_id(sf("sfDelegate"), delegate);
    tx.set_field_vl(sf("sfSigningPubKey"), &[0xED; 33]);

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::PAYMENT, Some(1_000_000)),
        Ter::TES_SUCCESS
    );
}

#[test]
fn delegated_multisign_reaches_apply_after_shared_preclaim_authorization() {
    let source = sample_account(0xAB);
    let destination = sample_account(0xAC);
    let delegate = sample_account(0xAD);
    let signer = sample_account(0xAE);
    let ledger = empty_ledger(vec![
        account_root_with_balance(source, 0, 0, 1_000_000),
        account_root_with_balance(destination, 0, 0, 0),
        account_root_with_balance(delegate, 0, 0, 1_000_000),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let mut tx = direct_xrp_payment_tx(source, destination, 100, 10);
    tx.set_account_id(sf("sfDelegate"), delegate);
    tx.set_field_vl(sf("sfSigningPubKey"), &[]);
    let mut signers = STArray::new(sf("sfSigners"));
    let mut signer_object = STObject::make_inner_object(sf("sfSigner"));
    signer_object.set_account_id(sf("sfAccount"), signer);
    signer_object.set_field_vl(sf("sfSigningPubKey"), &[0xED; 33]);
    signer_object.set_field_vl(sf("sfTxnSignature"), &[0x30, 0x00]);
    signers.push_back(signer_object);
    tx.set_field_array(sf("sfSigners"), signers);

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::PAYMENT, Some(1_000_000)),
        Ter::TES_SUCCESS
    );
}

#[test]
fn payment_recycles_max_issued_mpt_between_holders() {
    let source = sample_account(0xDA);
    let destination = sample_account(0xDB);
    let issuer = sample_account(0xDC);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = MPTIssue::new(mpt_id);
    let mut issuance = mpt_issuance_entry(issuer, 1, 100, protocol::lsfMPTCanTransfer);
    issuance.set_field_u64(sf("sfMaximumAmount"), 100);
    let ledger = empty_ledger(vec![
        account_root_with_balance(source, 1, 0, 1_000_000_000),
        account_root_with_balance(destination, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        issuance,
        mptoken_entry(source, mpt_id, 50),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::PAYMENT, |object| {
        object.set_account_id(sf("sfAccount"), source);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_mpt_amount(sf("sfAmount"), MPTAmount::from_value(10), mpt_issue),
        );
        object.set_field_amount(sf("sfFee"), test_xrp(10));
        object.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &tx, TxType::PAYMENT),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        view.read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(source)
        ))
        .expect("source read")
        .expect("source token")
        .get_field_u64(sf("sfMPTAmount")),
        40
    );
    assert_eq!(
        view.read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(destination)
        ))
        .expect("destination read")
        .expect("destination token")
        .get_field_u64(sf("sfMPTAmount")),
        10
    );
    assert_eq!(
        view.read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
            .expect("issuance read")
            .expect("issuance")
            .get_field_u64(sf("sfOutstandingAmount")),
        100
    );
}

fn vault_create_tx(account: AccountID, asset: Asset, sequence: u32) -> STTx {
    vault_create_tx_with_scale(account, asset, sequence, None)
}

fn vault_create_tx_with_scale(
    account: AccountID,
    asset: Asset,
    sequence: u32,
    scale: Option<u8>,
) -> STTx {
    STTx::new(TxType::VAULT_CREATE, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_issue(
            get_field_by_symbol("sfAsset"),
            STIssue::new_with_asset(get_field_by_symbol("sfAsset"), asset),
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        if let Some(scale) = scale {
            object.set_field_u8(get_field_by_symbol("sfScale"), scale);
        }
    })
}

fn vault_create_issue_tx(account: AccountID, asset: Asset, sequence: u32) -> STTx {
    STTx::new(TxType::VAULT_CREATE, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_issue(
            get_field_by_symbol("sfAsset"),
            STIssue::new_with_asset(get_field_by_symbol("sfAsset"), asset),
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
    })
}

fn vault_set_tx(account: AccountID, vault_id: Uint256, assets_maximum_drops: i64) -> STTx {
    STTx::new(TxType::VAULT_SET, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_amount(
            get_field_by_symbol("sfAssetsMaximum"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(assets_maximum_drops)),
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn vault_set_domain_tx(account: AccountID, vault_id: Uint256, domain_id: Uint256) -> STTx {
    STTx::new(TxType::VAULT_SET, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_h256(get_field_by_symbol("sfDomainID"), domain_id);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn vault_delete_tx(account: AccountID, vault_id: Uint256) -> STTx {
    STTx::new(TxType::VAULT_DELETE, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn vault_deposit_tx(account: AccountID, vault_id: Uint256, amount_drops: i64) -> STTx {
    STTx::new(TxType::VAULT_DEPOSIT, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(amount_drops)),
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn vault_withdraw_share_tx(
    account: AccountID,
    vault_id: Uint256,
    share_id: Uint192,
    amount: i64,
) -> STTx {
    STTx::new(TxType::VAULT_WITHDRAW, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_mpt_amount(
                get_field_by_symbol("sfAmount"),
                protocol::MPTAmount::from_value(amount),
                protocol::MPTIssue::new(share_id),
            ),
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn vault_withdraw_asset_tx(account: AccountID, vault_id: Uint256, amount_drops: i64) -> STTx {
    STTx::new(TxType::VAULT_WITHDRAW, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(amount_drops)),
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn vault_clawback_share_tx(
    account: AccountID,
    holder: AccountID,
    vault_id: Uint256,
    share_id: Uint192,
) -> STTx {
    STTx::new(TxType::VAULT_CLAWBACK, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_account_id(get_field_by_symbol("sfHolder"), holder);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_mpt_amount(
                get_field_by_symbol("sfAmount"),
                protocol::MPTAmount::new(),
                protocol::MPTIssue::new(share_id),
            ),
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn vault_clawback_asset_tx(
    account: AccountID,
    holder: AccountID,
    vault_id: Uint256,
    amount_drops: i64,
) -> STTx {
    STTx::new(TxType::VAULT_CLAWBACK, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_account_id(get_field_by_symbol("sfHolder"), holder);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(amount_drops)),
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn loan_broker_set_tx(account: AccountID, vault_id: Uint256, sequence: u32) -> STTx {
    STTx::new(TxType::LOAN_BROKER_SET, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn loan_broker_set_update_tx(
    account: AccountID,
    vault_id: Uint256,
    broker_id: Uint256,
    debt_maximum: Option<STNumber>,
    data: Option<&'static [u8]>,
) -> STTx {
    STTx::new(TxType::LOAN_BROKER_SET, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_h256(get_field_by_symbol("sfLoanBrokerID"), broker_id);
        if let Some(debt_maximum) = debt_maximum.clone() {
            object.set_field_number(get_field_by_symbol("sfDebtMaximum"), debt_maximum);
        }
        if let Some(data) = data {
            object.set_field_vl(get_field_by_symbol("sfData"), data);
        }
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    })
}

fn loan_broker_delete_tx(account: AccountID, broker_id: Uint256) -> STTx {
    STTx::new(TxType::LOAN_BROKER_DELETE, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfLoanBrokerID"), broker_id);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn loan_broker_cover_deposit_tx(account: AccountID, broker_id: Uint256, amount: STAmount) -> STTx {
    STTx::new(TxType::LOAN_BROKER_COVER_DEPOSIT, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfLoanBrokerID"), broker_id);
        object.set_field_amount(get_field_by_symbol("sfAmount"), amount.clone());
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    })
}

fn loan_broker_cover_withdraw_tx(account: AccountID, broker_id: Uint256, amount: STAmount) -> STTx {
    STTx::new(TxType::LOAN_BROKER_COVER_WITHDRAW, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfLoanBrokerID"), broker_id);
        object.set_field_amount(get_field_by_symbol("sfAmount"), amount.clone());
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    })
}

fn loan_broker_cover_withdraw_to_tx(
    account: AccountID,
    destination: AccountID,
    broker_id: Uint256,
    amount: STAmount,
) -> STTx {
    STTx::new(TxType::LOAN_BROKER_COVER_WITHDRAW, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_account_id(get_field_by_symbol("sfDestination"), destination);
        object.set_field_h256(get_field_by_symbol("sfLoanBrokerID"), broker_id);
        object.set_field_amount(get_field_by_symbol("sfAmount"), amount.clone());
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    })
}

fn loan_broker_cover_clawback_tx(account: AccountID, broker_id: Uint256, amount: STAmount) -> STTx {
    STTx::new(TxType::LOAN_BROKER_COVER_CLAWBACK, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfLoanBrokerID"), broker_id);
        object.set_field_amount(get_field_by_symbol("sfAmount"), amount.clone());
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    })
}

fn loan_broker_cover_clawback_without_id_tx(account: AccountID, amount: STAmount) -> STTx {
    STTx::new(TxType::LOAN_BROKER_COVER_CLAWBACK, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_amount(get_field_by_symbol("sfAmount"), amount.clone());
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    })
}

fn loan_broker_cover_clawback_empty_tx(account: AccountID) -> STTx {
    STTx::new(TxType::LOAN_BROKER_COVER_CLAWBACK, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    })
}

fn loan_broker_set_update_with_management_fee_tx(
    account: AccountID,
    vault_id: Uint256,
    broker_id: Uint256,
    management_fee_rate: u16,
) -> STTx {
    STTx::new(TxType::LOAN_BROKER_SET, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_h256(get_field_by_symbol("sfLoanBrokerID"), broker_id);
        object.set_field_u16(
            get_field_by_symbol("sfManagementFeeRate"),
            management_fee_rate,
        );
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    })
}

fn loan_delete_tx(account: AccountID, loan_id: Uint256) -> STTx {
    STTx::new(TxType::LOAN_DELETE, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn loan_manage_tx(account: AccountID, loan_id: Uint256, flags: u32) -> STTx {
    STTx::new(TxType::LOAN_MANAGE, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        object.set_field_u32(get_field_by_symbol("sfFlags"), flags);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    })
}

fn lending_enabled_empty_view() -> ApplyViewImpl<Ledger> {
    let mut ledger = empty_ledger(vec![]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE)
}

#[test]
fn loan_delete_dispatch_rejects_zero_loan_id_before_lookup() {
    let account = sample_account(0xAA);
    let mut view = lending_enabled_empty_view();

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_delete_tx(account, Uint256::from_array([0; 32])),
            TxType::LOAN_DELETE,
            None,
        ),
        protocol::Ter::TEM_INVALID
    );
}

#[test]
fn loan_manage_dispatch_runs_preflight_before_lookup() {
    let account = sample_account(0xAB);
    let mut zero_view = lending_enabled_empty_view();
    assert_eq!(
        handle_real_dispatch(
            &mut zero_view,
            &loan_manage_tx(account, Uint256::from_array([0; 32]), 0),
            TxType::LOAN_MANAGE,
            None,
        ),
        protocol::Ter::TEM_INVALID
    );

    let mut flags_view = lending_enabled_empty_view();
    assert_eq!(
        handle_real_dispatch(
            &mut flags_view,
            &loan_manage_tx(
                account,
                sample_uint256(0xAC),
                protocol::tfLoanDefault | protocol::tfLoanImpair,
            ),
            TxType::LOAN_MANAGE,
            None,
        ),
        protocol::Ter::TEM_INVALID_FLAG
    );
}

#[test]
fn loan_pay_dispatch_runs_preflight_before_lookup() {
    let account = sample_account(0xAD);
    let mut zero_id_view = lending_enabled_empty_view();
    let zero_id_tx = STTx::new(TxType::LOAN_PAY, |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_field_h256(sf("sfLoanID"), Uint256::from_array([0; 32]));
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(1)),
        );
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });
    assert_eq!(
        handle_real_dispatch(&mut zero_id_view, &zero_id_tx, TxType::LOAN_PAY, None),
        protocol::Ter::TEM_INVALID
    );

    let mut bad_amount_view = lending_enabled_empty_view();
    let bad_amount_tx = STTx::new(TxType::LOAN_PAY, |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_field_h256(sf("sfLoanID"), sample_uint256(0xAE));
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(0)),
        );
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });
    assert_eq!(
        handle_real_dispatch(&mut bad_amount_view, &bad_amount_tx, TxType::LOAN_PAY, None,),
        protocol::Ter::TEM_BAD_AMOUNT
    );

    let mut flags_view = lending_enabled_empty_view();
    let flags_tx = STTx::new(TxType::LOAN_PAY, |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_field_h256(sf("sfLoanID"), sample_uint256(0xAF));
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(1)),
        );
        object.set_field_u32(
            sf("sfFlags"),
            protocol::LOAN_LATE_PAYMENT_FLAG | protocol::LOAN_FULL_PAYMENT_FLAG,
        );
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(sf("sfSequence"), 1);
    });
    assert_eq!(
        handle_real_dispatch(&mut flags_view, &flags_tx, TxType::LOAN_PAY, None),
        protocol::Ter::TEM_INVALID_FLAG
    );
}

fn loan_set_tx(
    account: AccountID,
    broker_id: Uint256,
    principal_requested_drops: i64,
    sequence: u32,
) -> STTx {
    STTx::new(TxType::LOAN_SET, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfLoanBrokerID"), broker_id);
        object.set_field_number(
            get_field_by_symbol("sfPrincipalRequested"),
            STNumber::from(RuntimeNumber::from_i64(principal_requested_drops)),
        );
        object.set_field_u32(get_field_by_symbol("sfPaymentInterval"), 60);
        object.set_field_u32(get_field_by_symbol("sfPaymentTotal"), 1);
        object.set_field_u32(get_field_by_symbol("sfInterestRate"), 0);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
    })
}

fn loan_set_tx_with_origination_fee(
    account: AccountID,
    broker_id: Uint256,
    principal_requested_drops: i64,
    origination_fee_drops: i64,
    sequence: u32,
) -> STTx {
    STTx::new(TxType::LOAN_SET, move |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), account);
        object.set_field_h256(get_field_by_symbol("sfLoanBrokerID"), broker_id);
        object.set_field_number(
            get_field_by_symbol("sfPrincipalRequested"),
            STNumber::from(RuntimeNumber::from_i64(principal_requested_drops)),
        );
        object.set_field_number(
            get_field_by_symbol("sfLoanOriginationFee"),
            STNumber::from(RuntimeNumber::from_i64(origination_fee_drops)),
        );
        object.set_field_u32(get_field_by_symbol("sfPaymentInterval"), 60);
        object.set_field_u32(get_field_by_symbol("sfPaymentTotal"), 1);
        object.set_field_u32(get_field_by_symbol("sfInterestRate"), 0);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
    })
}

fn loan_entry(
    loan_id: Uint256,
    borrower: AccountID,
    broker_id: Uint256,
    broker_node: u64,
    owner_node: u64,
) -> STLedgerEntry {
    let mut entry = STLedgerEntry::from_type_and_key(
        LedgerEntryType::Loan,
        protocol::loan_keylet_from_key(loan_id).key,
    );
    entry.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), sample_uint256(0xC1));
    entry.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 1);
    entry.set_field_u64(get_field_by_symbol("sfLoanBrokerNode"), broker_node);
    entry.set_field_u64(get_field_by_symbol("sfOwnerNode"), owner_node);
    entry.set_field_h256(get_field_by_symbol("sfLoanBrokerID"), broker_id);
    entry.set_field_u32(get_field_by_symbol("sfLoanSequence"), 1);
    entry.set_account_id(get_field_by_symbol("sfBorrower"), borrower);
    entry.set_field_u32(get_field_by_symbol("sfPaymentRemaining"), 0);
    entry
}

fn loan_broker_entry(
    broker_id: Uint256,
    owner: AccountID,
    pseudo: AccountID,
    vault_id: Uint256,
    asset: Asset,
    debt_total: i64,
    cover_available: i64,
    cover_rate_minimum: u32,
    cover_rate_liquidation: u32,
) -> STLedgerEntry {
    let mut entry = STLedgerEntry::from_type_and_key(
        LedgerEntryType::LoanBroker,
        protocol::loan_broker_keylet_from_key(broker_id).key,
    );
    entry.set_field_h256(get_field_by_symbol("sfPreviousTxnID"), sample_uint256(0xD1));
    entry.set_field_u32(get_field_by_symbol("sfPreviousTxnLgrSeq"), 1);
    entry.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
    entry.set_account_id(get_field_by_symbol("sfOwner"), owner);
    entry.set_account_id(get_field_by_symbol("sfAccount"), pseudo);
    entry.set_field_u32(get_field_by_symbol("sfLoanSequence"), 1);
    entry.set_field_u32(get_field_by_symbol("sfOwnerCount"), 0);
    entry.set_field_u64(get_field_by_symbol("sfOwnerNode"), 0);
    entry.set_field_u64(get_field_by_symbol("sfVaultNode"), 0);
    entry.set_field_number(
        get_field_by_symbol("sfDebtTotal"),
        asset_number(asset, debt_total),
    );
    entry.set_field_number(
        get_field_by_symbol("sfCoverAvailable"),
        asset_number(asset, cover_available),
    );
    entry.set_field_u32(
        get_field_by_symbol("sfCoverRateMinimum"),
        cover_rate_minimum,
    );
    entry.set_field_u32(
        get_field_by_symbol("sfCoverRateLiquidation"),
        cover_rate_liquidation,
    );
    entry
}

fn managed_vault_entry(
    owner: AccountID,
    pseudo: AccountID,
    seq: u32,
    asset: Asset,
    assets_total: i64,
    assets_available: i64,
    loss_unrealized: i64,
) -> STLedgerEntry {
    let mut entry = vault_entry(owner, pseudo, seq, asset);
    entry.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, assets_total),
    );
    entry.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, assets_available),
    );
    entry.set_field_number(
        get_field_by_symbol("sfLossUnrealized"),
        asset_number(asset, loss_unrealized),
    );
    entry
}

fn managed_loan_entry(
    loan_id: Uint256,
    borrower: AccountID,
    broker_id: Uint256,
    total_value_outstanding: i64,
    principal_outstanding: i64,
    management_fee_outstanding: i64,
    payment_remaining: u32,
    next_payment_due_date: u32,
) -> STLedgerEntry {
    let asset = Asset::Issue(xrp_issue());
    let mut entry = loan_entry(loan_id, borrower, broker_id, 0, 0);
    entry.set_field_i32(get_field_by_symbol("sfLoanScale"), 0);
    entry.set_field_number(
        get_field_by_symbol("sfTotalValueOutstanding"),
        asset_number(asset, total_value_outstanding),
    );
    entry.set_field_number(
        get_field_by_symbol("sfPrincipalOutstanding"),
        asset_number(asset, principal_outstanding),
    );
    entry.set_field_number(
        get_field_by_symbol("sfManagementFeeOutstanding"),
        asset_number(asset, management_fee_outstanding),
    );
    entry.set_field_u32(get_field_by_symbol("sfPaymentRemaining"), payment_remaining);
    entry.set_field_u32(
        get_field_by_symbol("sfNextPaymentDueDate"),
        next_payment_due_date,
    );
    entry.set_field_u32(get_field_by_symbol("sfPreviousPaymentDueDate"), 120);
    entry.set_field_u32(get_field_by_symbol("sfStartDate"), 100);
    entry.set_field_u32(get_field_by_symbol("sfPaymentInterval"), 30);
    entry.set_field_u32(get_field_by_symbol("sfGracePeriod"), 0);
    entry.set_field_number(
        get_field_by_symbol("sfPeriodicPayment"),
        asset_number(asset, 0),
    );
    entry
}

#[test]
fn signer_list_set_owner_tracks_fix_include_keylet_fields() {
    let account = sample_account(0x12);
    let signer = sample_account(0x13);
    let tx = signer_list_set_tx(account, 1, &[(signer, 1)]);

    let legacy_ledger = empty_ledger(vec![account_root(account, 0, 0)]);
    let mut legacy_view = ApplyViewImpl::new(Arc::new(legacy_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut legacy_view, &tx, TxType::SIGNER_LIST_SET, None),
        Ter::TES_SUCCESS
    );
    let legacy = legacy_view
        .read(signers_keylet(raw_account_id(account)))
        .expect("legacy signer list read")
        .expect("legacy signer list exists");
    assert!(!legacy.is_field_present(sf("sfOwner")));

    let mut amended_ledger = empty_ledger(vec![account_root(account, 0, 0)]);
    amended_ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "fixIncludeKeyletFields",
    )]));
    let mut amended_view = ApplyViewImpl::new(Arc::new(amended_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut amended_view, &tx, TxType::SIGNER_LIST_SET, None),
        Ter::TES_SUCCESS
    );
    let amended = amended_view
        .read(signers_keylet(raw_account_id(account)))
        .expect("amended signer list read")
        .expect("amended signer list exists");
    assert_eq!(amended.get_account_id(sf("sfOwner")), account);
}

#[test]
fn escrow_create_sequence_tracks_fix_include_keylet_fields() {
    let account = sample_account(0x14);
    let destination = sample_account(0x15);
    let sequence = 9;
    let tx = escrow_create_tx(account, destination, sequence);
    let keylet = protocol::escrow_keylet(raw_account_id(account), sequence);

    let legacy_ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        account_root(destination, 0, 0),
    ]);
    let mut legacy_view = ApplyViewImpl::new(Arc::new(legacy_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut legacy_view, &tx, TxType::ESCROW_CREATE, None),
        Ter::TES_SUCCESS
    );
    assert!(
        !legacy_view
            .read(keylet.clone())
            .expect("legacy escrow read")
            .expect("legacy escrow exists")
            .is_field_present(sf("sfSequence"))
    );

    let mut amended_ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        account_root(destination, 0, 0),
    ]);
    amended_ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "fixIncludeKeyletFields",
    )]));
    let mut amended_view = ApplyViewImpl::new(Arc::new(amended_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut amended_view, &tx, TxType::ESCROW_CREATE, None),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        amended_view
            .read(keylet)
            .expect("amended escrow read")
            .expect("amended escrow exists")
            .get_field_u32(sf("sfSequence")),
        sequence
    );

    let ticket_sequence = 11;
    let ticketed_tx = STTx::new(TxType::ESCROW_CREATE, |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(1_000)),
        );
        object.set_field_u32(sf("sfSequence"), 0);
        object.set_field_u32(sf("sfTicketSequence"), ticket_sequence);
        object.set_field_u32(sf("sfFinishAfter"), 1001);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });
    let ticket_keylet = protocol::escrow_keylet(raw_account_id(account), ticket_sequence);
    let mut ticket_ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        account_root(destination, 0, 0),
    ]);
    ticket_ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "fixIncludeKeyletFields",
    )]));
    let mut ticket_view = ApplyViewImpl::new(Arc::new(ticket_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut ticket_view, &ticketed_tx, TxType::ESCROW_CREATE, None,),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        ticket_view
            .read(ticket_keylet)
            .expect("ticketed escrow read")
            .expect("ticketed escrow exists")
            .get_field_u32(sf("sfSequence")),
        ticket_sequence,
        "ticketed EscrowCreate must store the ticket value, never Sequence = 0"
    );
}

#[test]
fn sponsored_rules_escrow_create_checks_post_fee_source_balance() {
    let account = sample_account(0x18);
    let destination = sample_account(0x19);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 250),
        account_root(destination, 0, 0),
    ]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 100,
        increment: 50,
    });
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("Sponsor")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::ESCROW_CREATE, |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_amount(sf("sfAmount"), test_xrp(100));
        object.set_field_u32(sf("sfFinishAfter"), 1001);
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_field_amount(sf("sfFee"), test_xrp(10));
    });

    assert_eq!(
        apply_submit_transactor_shell(&mut view, &tx, TxType::ESCROW_CREATE),
        Ter::TEC_UNFUNDED
    );
    assert!(
        view.read(protocol::escrow_keylet(raw_account_id(account), 1))
            .expect("escrow read")
            .is_none()
    );
}

#[test]
fn paychan_create_sequence_uses_ticket_value_only_with_fix_include_keylet_fields() {
    let account = sample_account(0x16);
    let destination = sample_account(0x17);
    let ticket_sequence = 11;
    let tx = paychan_create_ticket_tx(account, destination, ticket_sequence);
    let keylet = protocol::pay_channel_keylet(
        raw_account_id(account),
        raw_account_id(destination),
        ticket_sequence,
    );

    let legacy_ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        account_root(destination, 0, 0),
    ]);
    let mut legacy_view = ApplyViewImpl::new(Arc::new(legacy_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut legacy_view, &tx, TxType::PAYCHAN_CREATE, None),
        Ter::TES_SUCCESS
    );
    assert!(
        !legacy_view
            .read(keylet.clone())
            .expect("legacy pay channel read")
            .expect("legacy pay channel exists")
            .is_field_present(sf("sfSequence"))
    );

    let mut amended_ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        account_root(destination, 0, 0),
    ]);
    amended_ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "fixIncludeKeyletFields",
    )]));
    let mut amended_view = ApplyViewImpl::new(Arc::new(amended_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut amended_view, &tx, TxType::PAYCHAN_CREATE, None),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        amended_view
            .read(keylet)
            .expect("amended pay channel read")
            .expect("amended pay channel exists")
            .get_field_u32(sf("sfSequence")),
        ticket_sequence
    );
}

#[test]
fn escrow_create_uses_strict_parent_close_time_expiration() {
    let account = sample_account(0x16);
    let destination = sample_account(0x17);
    let tx = escrow_create_tx(account, destination, 9);

    for (parent_close_time, expected) in [(1001, Ter::TES_SUCCESS), (1002, Ter::TEC_NO_PERMISSION)]
    {
        let ledger = ledger_with_header(
            LedgerHeader {
                parent_close_time,
                ..LedgerHeader::default()
            },
            vec![account_root(account, 0, 0), account_root(destination, 0, 0)],
        );
        let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
        assert_eq!(
            handle_real_dispatch(&mut view, &tx, TxType::ESCROW_CREATE, None),
            expected
        );
    }
}

#[test]
fn paychan_create_sequence_uses_normal_sequence_only_with_fix_include_keylet_fields() {
    let account = sample_account(0x1A);
    let destination = sample_account(0x1B);
    let sequence = 9;
    let tx = STTx::new(TxType::PAYCHAN_CREATE, |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(1_000)),
        );
        object.set_field_u32(sf("sfSettleDelay"), 60);
        object.set_field_vl(sf("sfPublicKey"), &[4; 33]);
        object.set_field_u32(sf("sfSequence"), sequence);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });
    let keylet = protocol::pay_channel_keylet(
        raw_account_id(account),
        raw_account_id(destination),
        sequence,
    );

    for amendment_enabled in [false, true] {
        let mut ledger = empty_ledger(vec![
            account_root(account, 0, 0),
            account_root(destination, 0, 0),
        ]);
        if amendment_enabled {
            ledger.set_rules(protocol::Rules::new([protocol::feature_id(
                "fixIncludeKeyletFields",
            )]));
        }
        let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
        assert_eq!(
            handle_real_dispatch(&mut view, &tx, TxType::PAYCHAN_CREATE, None),
            Ter::TES_SUCCESS
        );
        let channel = view
            .read(keylet.clone())
            .expect("pay channel read")
            .expect("pay channel exists");
        assert_eq!(
            channel.is_field_present(sf("sfSequence")),
            amendment_enabled,
            "PayChan sfSequence must be feature-gated for ordinary Sequence transactions"
        );
        if amendment_enabled {
            assert_eq!(channel.get_field_u32(sf("sfSequence")), sequence);
        }
    }
}

#[test]
fn oracle_set_keylet_fields_and_creation_order_track_amendments() {
    let account = sample_account(0x18);
    let document_id = 7;
    let high_currency = Currency::from_array([0xFF; 20]);
    let high_currency_text = protocol::currency_to_string(high_currency);
    let input_series = [
        oracle_price_data_with_currencies(currency_from_string("XRP"), high_currency, 742, 2),
        oracle_price_data("XRP", "USD", 711, 2),
    ];
    let mut create = oracle_set_tx(account, document_id, 1_000, &input_series, true);
    let raw_uri = [0xFF, 0x00, b'o', b'r', b'a', b'c', b'l', b'e'];
    create.set_field_vl(sf("sfURI"), &raw_uri);
    let update = oracle_set_tx(account, document_id, 1_001, &input_series, false);
    let keylet = protocol::oracle_keylet(raw_account_id(account), document_id);

    let legacy_ledger = empty_ledger(vec![account_root(account, 0, 0)]);
    let mut legacy_view = ApplyViewImpl::new(Arc::new(legacy_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut legacy_view, &create, TxType::ORACLE_SET, None),
        Ter::TES_SUCCESS
    );
    let legacy_created = legacy_view
        .read(keylet.clone())
        .expect("legacy oracle read")
        .expect("legacy oracle exists");
    assert!(!legacy_created.is_field_present(sf("sfOracleDocumentID")));
    assert_eq!(legacy_created.get_field_vl(sf("sfURI")), raw_uri);
    let legacy_created_series = legacy_created.get_field_array(sf("sfPriceDataSeries"));
    assert_eq!(
        oracle_pair(legacy_created_series.get(0).expect("first legacy pair")),
        ("XRP".to_owned(), high_currency_text.clone())
    );
    assert_eq!(
        oracle_pair(legacy_created_series.get(1).expect("second legacy pair")),
        ("XRP".to_owned(), "USD".to_owned())
    );

    assert_eq!(
        handle_real_dispatch(&mut legacy_view, &update, TxType::ORACLE_SET, None),
        Ter::TES_SUCCESS
    );
    let legacy_updated = legacy_view
        .read(keylet.clone())
        .expect("updated legacy oracle read")
        .expect("updated legacy oracle exists");
    assert!(!legacy_updated.is_field_present(sf("sfOracleDocumentID")));
    assert_eq!(legacy_updated.get_field_vl(sf("sfURI")), raw_uri);
    let legacy_updated_series = legacy_updated.get_field_array(sf("sfPriceDataSeries"));
    assert_eq!(
        oracle_pair(
            legacy_updated_series
                .get(0)
                .expect("first updated legacy pair")
        ),
        ("XRP".to_owned(), "USD".to_owned())
    );
    assert_eq!(
        oracle_pair(
            legacy_updated_series
                .get(1)
                .expect("second updated legacy pair")
        ),
        ("XRP".to_owned(), high_currency_text.clone())
    );

    let legacy_for_backfill =
        STLedgerEntry::from_stobject(legacy_updated.clone_as_object(), *legacy_updated.key());
    let mut backfill_ledger = empty_ledger(vec![account_root(account, 1, 0), legacy_for_backfill]);
    backfill_ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "fixIncludeKeyletFields",
    )]));
    let mut backfill_view = ApplyViewImpl::new(Arc::new(backfill_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut backfill_view, &update, TxType::ORACLE_SET, None),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        backfill_view
            .read(keylet.clone())
            .expect("backfilled oracle read")
            .expect("backfilled oracle exists")
            .get_field_u32(sf("sfOracleDocumentID")),
        document_id
    );

    let mut amended_ledger = empty_ledger(vec![account_root(account, 0, 0)]);
    amended_ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("fixIncludeKeyletFields"),
        protocol::feature_id("fixPriceOracleOrder"),
    ]));
    let mut amended_view = ApplyViewImpl::new(Arc::new(amended_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut amended_view, &create, TxType::ORACLE_SET, None),
        Ter::TES_SUCCESS
    );
    let amended_created = amended_view
        .read(keylet.clone())
        .expect("amended oracle read")
        .expect("amended oracle exists");
    assert_eq!(
        amended_created.get_field_u32(sf("sfOracleDocumentID")),
        document_id
    );
    let amended_created_series = amended_created.get_field_array(sf("sfPriceDataSeries"));
    assert_eq!(
        oracle_pair(amended_created_series.get(0).expect("first amended pair")),
        ("XRP".to_owned(), "USD".to_owned())
    );
    assert_eq!(
        oracle_pair(amended_created_series.get(1).expect("second amended pair")),
        ("XRP".to_owned(), high_currency_text.clone())
    );

    assert_eq!(
        handle_real_dispatch(&mut amended_view, &update, TxType::ORACLE_SET, None),
        Ter::TES_SUCCESS
    );
    let amended_updated = amended_view
        .read(keylet)
        .expect("updated amended oracle read")
        .expect("updated amended oracle exists");
    assert_eq!(
        amended_updated.get_field_u32(sf("sfOracleDocumentID")),
        document_id
    );
    let amended_updated_series = amended_updated.get_field_array(sf("sfPriceDataSeries"));
    assert_eq!(
        oracle_pair(
            amended_updated_series
                .get(0)
                .expect("first updated amended pair")
        ),
        ("XRP".to_owned(), "USD".to_owned())
    );
    assert_eq!(
        oracle_pair(
            amended_updated_series
                .get(1)
                .expect("second updated amended pair")
        ),
        ("XRP".to_owned(), high_currency_text)
    );
}

#[test]
fn oracle_price_series_reserve_tracks_five_to_six_and_delete() {
    let account = sample_account(0x1C);
    let document_id = 19;
    let oracle_keylet = protocol::oracle_keylet(raw_account_id(account), document_id);
    let owner_keylet = owner_dir_keylet(raw_account_id(account));
    let five_pairs = [
        oracle_price_data("XRP", "USD", 1, 0),
        oracle_price_data("EUR", "USD", 2, 0),
        oracle_price_data("GBP", "USD", 3, 0),
        oracle_price_data("JPY", "USD", 4, 0),
        oracle_price_data("AUD", "USD", 5, 0),
    ];
    let sixth_pair = oracle_price_data("CAD", "USD", 6, 0);
    let mut remove_sixth_pair = sixth_pair.clone();
    remove_sixth_pair.make_field_absent(sf("sfAssetPrice"));

    let mut view = ApplyViewImpl::new(
        Arc::new(empty_ledger(vec![account_root(account, 0, 0)])),
        ApplyFlags::NONE,
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &oracle_set_tx(account, document_id, 1, &five_pairs, true),
            TxType::ORACLE_SET,
            None,
        ),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        view.read(protocol::account_keylet(raw_account_id(account)))
            .expect("owner account read")
            .expect("owner account exists")
            .get_field_u32(sf("sfOwnerCount")),
        1
    );

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &oracle_set_tx(account, document_id, 2, &[sixth_pair.clone()], false),
            TxType::ORACLE_SET,
            None,
        ),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        view.read(oracle_keylet.clone())
            .expect("oracle read")
            .expect("oracle exists")
            .get_field_array(sf("sfPriceDataSeries"))
            .len(),
        6
    );
    assert_eq!(
        view.read(protocol::account_keylet(raw_account_id(account)))
            .expect("owner account read")
            .expect("owner account exists")
            .get_field_u32(sf("sfOwnerCount")),
        2
    );

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &oracle_set_tx(account, document_id, 3, &[remove_sixth_pair], false),
            TxType::ORACLE_SET,
            None,
        ),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        view.read(oracle_keylet.clone())
            .expect("oracle read")
            .expect("oracle exists")
            .get_field_array(sf("sfPriceDataSeries"))
            .len(),
        5
    );
    assert_eq!(
        view.read(protocol::account_keylet(raw_account_id(account)))
            .expect("owner account read")
            .expect("owner account exists")
            .get_field_u32(sf("sfOwnerCount")),
        1
    );

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &oracle_set_tx(account, document_id, 4, &[sixth_pair], false),
            TxType::ORACLE_SET,
            None,
        ),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        view.read(protocol::account_keylet(raw_account_id(account)))
            .expect("owner account read")
            .expect("owner account exists")
            .get_field_u32(sf("sfOwnerCount")),
        2
    );

    let delete = STTx::new(TxType::ORACLE_DELETE, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_u32(sf("sfOracleDocumentID"), document_id);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 5);
    });
    assert_eq!(
        handle_real_dispatch(&mut view, &delete, TxType::ORACLE_DELETE, None),
        Ter::TES_SUCCESS
    );
    assert!(
        view.read(oracle_keylet.clone())
            .expect("deleted oracle read")
            .is_none()
    );
    assert_eq!(
        view.read(protocol::account_keylet(raw_account_id(account)))
            .expect("owner account read")
            .expect("owner account exists")
            .get_field_u32(sf("sfOwnerCount")),
        0
    );
    if let Some(owner_dir) = view.read(owner_keylet).expect("owner directory read") {
        assert!(
            !owner_dir
                .get_field_v256(sf("sfIndexes"))
                .value()
                .contains(&oracle_keylet.key),
            "OracleDelete must remove the six-pair oracle from its owner directory"
        );
    }
}

#[test]
fn oracle_set_shell_enforces_reserve_and_accepts_immutable_field_omission() {
    let account = sample_account(0x1D);
    let document_id = 20;
    let close_time = 1_000;
    let last_update_time = 946_684_800 + close_time;
    let five_pairs = [
        oracle_price_data("XRP", "USD", 1, 0),
        oracle_price_data("EUR", "USD", 2, 0),
        oracle_price_data("GBP", "USD", 3, 0),
        oracle_price_data("JPY", "USD", 4, 0),
        oracle_price_data("AUD", "USD", 5, 0),
    ];
    let sixth_pair = oracle_price_data("CAD", "USD", 6, 0);
    let shell_tx = |sequence, timestamp, entries: &[STObject], create| {
        let mut tx = oracle_set_tx(account, document_id, timestamp, entries, create);
        tx.set_field_u32(sf("sfSequence"), sequence);
        tx
    };
    let header = LedgerHeader {
        seq: 1,
        close_time,
        parent_close_time: close_time - 1,
        ..LedgerHeader::default()
    };
    let reserve_fees = ledger::Fees {
        base: 10,
        reserve: 200,
        increment: 50,
    };

    // The first owner count increment is affordable, but the sixth pair's
    // second reserve increment is not. A tec result remains claimed.
    let low_balance = reserve_fees.account_reserve(1) as i64;
    let mut low_ledger = ledger_with_header(
        header.clone(),
        vec![account_root_with_balance(account, 0, 0, low_balance)],
    );
    low_ledger.set_fees(reserve_fees);
    let mut low_view = ApplyViewImpl::new(Arc::new(low_ledger), ApplyFlags::NONE);
    assert_eq!(
        apply_submit_transactor_shell(
            &mut low_view,
            &shell_tx(1, last_update_time, &five_pairs, true),
            TxType::ORACLE_SET,
        ),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        apply_submit_transactor_shell(
            &mut low_view,
            &shell_tx(2, last_update_time + 1, &[sixth_pair.clone()], false),
            TxType::ORACLE_SET,
        ),
        Ter::TEC_INSUFFICIENT_RESERVE
    );
    assert_eq!(
        low_view
            .read(protocol::oracle_keylet(
                raw_account_id(account),
                document_id
            ))
            .expect("oracle read")
            .expect("oracle remains")
            .get_field_array(sf("sfPriceDataSeries"))
            .len(),
        5,
        "a rejected sixth pair must not mutate the Oracle"
    );
    assert_eq!(
        low_view
            .read(account_keylet(raw_account_id(account)))
            .expect("account read")
            .expect("account remains")
            .get_field_u32(sf("sfSequence")),
        3,
        "tecINSUFFICIENT_RESERVE must consume the transaction sequence"
    );

    let high_balance = reserve_fees.account_reserve(2) as i64 + 100;
    let mut high_ledger = ledger_with_header(
        header,
        vec![account_root_with_balance(account, 0, 0, high_balance)],
    );
    high_ledger.set_fees(reserve_fees);
    let mut high_view = ApplyViewImpl::new(Arc::new(high_ledger), ApplyFlags::NONE);
    assert_eq!(
        apply_submit_transactor_shell(
            &mut high_view,
            &shell_tx(1, last_update_time, &five_pairs, true),
            TxType::ORACLE_SET,
        ),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        apply_submit_transactor_shell(
            &mut high_view,
            &shell_tx(2, last_update_time + 1, &[sixth_pair], false),
            TxType::ORACLE_SET,
        ),
        Ter::TES_SUCCESS,
        "updates may omit immutable Provider and AssetClass"
    );
    let high_account = high_view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read")
        .expect("account remains");
    assert_eq!(high_account.get_field_u32(sf("sfOwnerCount")), 2);
}

#[test]
fn signer_list_set_create_populates_signer_sle_and_owner_dir() {
    let account = sample_account(0x11);
    let signer_a = sample_account(0x44);
    let signer_b = sample_account(0x33);
    let ledger = empty_ledger(vec![account_root(account, 0, 0)]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = signer_list_set_tx(account, 3, &[(signer_a, 1), (signer_b, 2)]);

    let result = handle_real_dispatch(&mut view, &sttx, TxType::SIGNER_LIST_SET, None);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let signer_list = view
        .read(signers_keylet(raw_account_id(account)))
        .expect("signer list read should succeed")
        .expect("signer list should exist");
    assert_eq!(
        signer_list.get_field_u32(get_field_by_symbol("sfSignerQuorum")),
        3
    );
    assert_eq!(
        signer_list.get_field_u32(get_field_by_symbol("sfSignerListID")),
        0
    );
    assert_eq!(
        signer_list.get_field_u32(get_field_by_symbol("sfFlags")),
        LSF_ONE_OWNER_COUNT
    );
    assert_eq!(
        signer_list.get_field_u64(get_field_by_symbol("sfOwnerNode")),
        0
    );

    let signer_entries = signer_list.get_field_array(get_field_by_symbol("sfSignerEntries"));
    assert_eq!(signer_entries.len(), 2);
    assert_eq!(
        signer_entries
            .get(0)
            .expect("first signer")
            .get_account_id(get_field_by_symbol("sfAccount")),
        signer_b
    );
    assert_eq!(
        signer_entries
            .get(1)
            .expect("second signer")
            .get_account_id(get_field_by_symbol("sfAccount")),
        signer_a
    );

    let account_sle = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read should succeed")
        .expect("account should exist");
    assert_eq!(
        account_sle.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        1
    );

    let owner_dir = view
        .read(owner_dir_keylet(raw_account_id(account)))
        .expect("owner dir read should succeed")
        .expect("owner dir should exist");
    assert_eq!(
        owner_dir.get_account_id(get_field_by_symbol("sfOwner")),
        account
    );
    assert_eq!(
        owner_dir
            .get_field_v256(get_field_by_symbol("sfIndexes"))
            .value(),
        &[signer_list.key().to_owned()]
    );
}

#[test]
fn ticket_create_populates_owner_directory_description() {
    let account = sample_account(0x19);
    let mut account_sle = account_root(account, 0, 0);
    account_sle.set_field_u32(sf("sfSequence"), 2);
    let ledger = empty_ledger(vec![account_sle]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = ticket_create_tx(account, 1, 1);

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::TICKET_CREATE, None),
        Ter::TES_SUCCESS
    );

    let ticket = protocol::ticket_keylet(raw_account_id(account), 2);
    let owner_dir = view
        .read(owner_dir_keylet(raw_account_id(account)))
        .expect("owner directory read")
        .expect("owner directory exists");
    assert_eq!(owner_dir.get_account_id(sf("sfOwner")), account);
    assert_eq!(
        owner_dir.get_field_v256(sf("sfIndexes")).value(),
        &[ticket.key]
    );
    assert_eq!(
        view.read(ticket)
            .expect("ticket read")
            .expect("ticket exists")
            .get_field_u64(sf("sfOwnerNode")),
        0
    );
}

#[test]
fn ticket_create_returns_tec_dir_full_at_legacy_page_limit() {
    let account = sample_account(0x1A);
    let owner_dir_keylet = owner_dir_keylet(raw_account_id(account));
    let last_page = protocol::DIR_NODE_MAX_PAGES - 1;
    let full_indexes = (0..protocol::DIR_NODE_MAX_ENTRIES)
        .map(|index| sample_uint256(index as u8 + 1))
        .collect::<Vec<_>>();

    let mut root = STLedgerEntry::new(owner_dir_keylet);
    root.set_account_id(sf("sfOwner"), account);
    root.set_field_h256(sf("sfRootIndex"), owner_dir_keylet.key);
    root.set_field_v256(
        sf("sfIndexes"),
        protocol::STVector256::from_values(sf("sfIndexes"), full_indexes.clone()),
    );
    root.set_field_u64(sf("sfIndexPrevious"), last_page);
    root.set_field_u64(sf("sfIndexNext"), last_page);

    let mut tail = STLedgerEntry::new(protocol::page_keylet(owner_dir_keylet, last_page));
    tail.set_account_id(sf("sfOwner"), account);
    tail.set_field_h256(sf("sfRootIndex"), owner_dir_keylet.key);
    tail.set_field_v256(
        sf("sfIndexes"),
        protocol::STVector256::from_values(sf("sfIndexes"), full_indexes),
    );

    let mut account_sle = account_root(account, 0, 0);
    account_sle.set_field_u32(sf("sfSequence"), 2);
    let ledger = empty_ledger(vec![account_sle, root, tail]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = ticket_create_tx(account, 1, 1);

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::TICKET_CREATE, None),
        Ter::TEC_DIR_FULL
    );
}

#[test]
fn ticketed_ticket_create_starts_at_post_preamble_account_sequence() {
    let account = sample_account(0x1B);
    let consumed_sequence = 5;
    let first_created_sequence = 10;
    let consumed_keylet = protocol::ticket_keylet(raw_account_id(account), consumed_sequence);
    let mut account_sle = account_root(account, 1, 0);
    account_sle.set_field_u32(sf("sfSequence"), first_created_sequence);
    account_sle.set_field_u32(sf("sfTicketCount"), 1);
    let mut consumed = STLedgerEntry::new(consumed_keylet);
    consumed.set_account_id(sf("sfAccount"), account);
    consumed.set_field_u32(sf("sfTicketSequence"), consumed_sequence);
    consumed.set_field_u64(sf("sfOwnerNode"), 0);
    let ledger = empty_ledger(vec![
        account_sle,
        owner_dir_root(account, consumed_keylet.key),
        consumed,
    ]);
    let mut view = Sandbox::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::TICKET_CREATE, |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_field_u32(sf("sfSequence"), 0);
        object.set_field_u32(sf("sfTicketSequence"), consumed_sequence);
        object.set_field_u32(sf("sfTicketCount"), 1);
        object.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });

    assert_eq!(
        apply_submit_transactor_shell(&mut view, &tx, TxType::TICKET_CREATE),
        Ter::TES_SUCCESS
    );
    assert!(
        view.read(consumed_keylet)
            .expect("consumed ticket read")
            .is_none()
    );
    assert!(
        view.read(protocol::ticket_keylet(
            raw_account_id(account),
            first_created_sequence,
        ))
        .expect("created ticket read")
        .is_some()
    );
    let account_after = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read")
        .expect("account exists");
    assert_eq!(
        account_after.get_field_u32(sf("sfSequence")),
        first_created_sequence + 1
    );
}

#[test]
fn signer_list_set_destroy_removes_existing_signer_list() {
    let account = sample_account(0x21);
    let signer_list = signer_list_entry(account, 0, LSF_ONE_OWNER_COUNT);
    let ledger = empty_ledger(vec![
        account_root(account, 1, 0),
        owner_dir_root(account, signer_list.key().to_owned()),
        signer_list,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = signer_list_set_tx(account, 0, &[]);

    let result = handle_real_dispatch(&mut view, &sttx, TxType::SIGNER_LIST_SET, None);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    assert!(
        view.read(signers_keylet(raw_account_id(account)))
            .expect("signer list read should succeed")
            .is_none()
    );
    let account_sle = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read should succeed")
        .expect("account should exist");
    assert_eq!(
        account_sle.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        0
    );
}

#[test]
fn signer_list_set_destroy_modern_list_removes_one_owner_count() {
    // Testnet ledger 20,121,340, transaction A1C0DBCB... destroyed a
    // one-signer list carrying lsfOneOwnerCount.  rippled changes OwnerCount
    // from 2 to 1; applying the legacy `2 + signer_count` cost here forks the
    // account-state root even though the transaction returns tesSUCCESS.
    let account = sample_account(0x22);
    let signer_list = signer_list_entry(account, 0, LSF_ONE_OWNER_COUNT);
    let ledger = empty_ledger(vec![
        account_root(account, 2, 0),
        owner_dir_root(account, signer_list.key().to_owned()),
        signer_list,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = signer_list_set_tx(account, 0, &[]);

    assert_eq!(
        handle_real_dispatch(&mut view, &sttx, TxType::SIGNER_LIST_SET, Some(1_000_000),),
        Ter::TES_SUCCESS
    );
    let account_sle = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read")
        .expect("account remains");
    assert_eq!(account_sle.get_field_u32(sf("sfOwnerCount")), 1);
}

#[test]
fn signer_list_set_destroy_legacy_list_uses_signer_count_cost() {
    let account = sample_account(0x23);
    let signer_list = signer_list_entry(account, 0, 0);
    let ledger = empty_ledger(vec![
        account_root(account, 3, 0),
        owner_dir_root(account, signer_list.key().to_owned()),
        signer_list,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &signer_list_set_tx(account, 0, &[]),
            TxType::SIGNER_LIST_SET,
            Some(1_000_000),
        ),
        Ter::TES_SUCCESS
    );
    let account_sle = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read")
        .expect("account remains");
    assert_eq!(account_sle.get_field_u32(sf("sfOwnerCount")), 0);
}

#[test]
fn signer_list_set_destroy_updates_reserve_sponsor_counts() {
    let account = sample_account(0x24);
    let sponsor = sample_account(0x25);
    let mut signer_list = signer_list_entry(account, 0, LSF_ONE_OWNER_COUNT);
    signer_list.set_account_id(sf("sfSponsor"), sponsor);
    let mut account_sle = account_root(account, 2, 0);
    account_sle.set_field_u32(sf("sfSponsoredOwnerCount"), 1);
    let mut sponsor_sle = account_root(sponsor, 1, 0);
    sponsor_sle.set_field_u32(sf("sfSponsoringOwnerCount"), 1);
    let ledger = empty_ledger(vec![
        account_sle,
        sponsor_sle,
        owner_dir_root(account, signer_list.key().to_owned()),
        signer_list,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &signer_list_set_tx(account, 0, &[]),
            TxType::SIGNER_LIST_SET,
            Some(1_000_000),
        ),
        Ter::TES_SUCCESS
    );
    let account_sle = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read")
        .expect("account remains");
    let sponsor_sle = view
        .read(account_keylet(raw_account_id(sponsor)))
        .expect("sponsor read")
        .expect("sponsor remains");
    assert_eq!(account_sle.get_field_u32(sf("sfOwnerCount")), 1);
    assert_eq!(account_sle.get_field_u32(sf("sfSponsoredOwnerCount")), 0);
    assert_eq!(sponsor_sle.get_field_u32(sf("sfSponsoringOwnerCount")), 0);
}

#[test]
fn signer_list_set_create_assigns_reserve_sponsor() {
    let account = sample_account(0x26);
    let sponsor = sample_account(0x27);
    let signer = sample_account(0x28);
    let ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        account_root(sponsor, 0, 0),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let mut sttx = signer_list_set_tx(account, 1, &[(signer, 1)]);
    sttx.set_account_id(sf("sfSponsor"), sponsor);
    sttx.set_field_u32(sf("sfSponsorFlags"), ledger::SPF_SPONSOR_RESERVE);

    assert_eq!(
        handle_real_dispatch(&mut view, &sttx, TxType::SIGNER_LIST_SET, None),
        Ter::TES_SUCCESS
    );
    let signer_list = view
        .read(signers_keylet(raw_account_id(account)))
        .expect("signer list read")
        .expect("signer list exists");
    let account_sle = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read")
        .expect("account remains");
    let sponsor_sle = view
        .read(account_keylet(raw_account_id(sponsor)))
        .expect("sponsor read")
        .expect("sponsor remains");
    assert_eq!(signer_list.get_account_id(sf("sfSponsor")), sponsor);
    assert_eq!(account_sle.get_field_u32(sf("sfOwnerCount")), 1);
    assert_eq!(account_sle.get_field_u32(sf("sfSponsoredOwnerCount")), 1);
    assert_eq!(sponsor_sle.get_field_u32(sf("sfSponsoringOwnerCount")), 1);
}

#[test]
fn signer_list_set_replace_reassigns_reserve_to_new_sponsor() {
    let account = sample_account(0x29);
    let old_sponsor = sample_account(0x2A);
    let new_sponsor = sample_account(0x2B);
    let signer = sample_account(0x2C);
    let mut old_list = signer_list_entry(account, 0, LSF_ONE_OWNER_COUNT);
    old_list.set_account_id(sf("sfSponsor"), old_sponsor);
    let mut account_sle = account_root(account, 1, 0);
    account_sle.set_field_u32(sf("sfSponsoredOwnerCount"), 1);
    let mut old_sponsor_sle = account_root(old_sponsor, 0, 0);
    old_sponsor_sle.set_field_u32(sf("sfSponsoringOwnerCount"), 1);
    let ledger = empty_ledger(vec![
        account_sle,
        old_sponsor_sle,
        account_root(new_sponsor, 0, 0),
        owner_dir_root(account, old_list.key().to_owned()),
        old_list,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let mut sttx = signer_list_set_tx(account, 1, &[(signer, 1)]);
    sttx.set_account_id(sf("sfSponsor"), new_sponsor);
    sttx.set_field_u32(sf("sfSponsorFlags"), ledger::SPF_SPONSOR_RESERVE);

    assert_eq!(
        handle_real_dispatch(&mut view, &sttx, TxType::SIGNER_LIST_SET, None),
        Ter::TES_SUCCESS
    );
    let signer_list = view
        .read(signers_keylet(raw_account_id(account)))
        .expect("signer list read")
        .expect("replacement exists");
    let old_sponsor_sle = view
        .read(account_keylet(raw_account_id(old_sponsor)))
        .expect("old sponsor read")
        .expect("old sponsor remains");
    let new_sponsor_sle = view
        .read(account_keylet(raw_account_id(new_sponsor)))
        .expect("new sponsor read")
        .expect("new sponsor remains");
    assert_eq!(signer_list.get_account_id(sf("sfSponsor")), new_sponsor);
    assert_eq!(
        old_sponsor_sle.get_field_u32(sf("sfSponsoringOwnerCount")),
        0
    );
    assert_eq!(
        new_sponsor_sle.get_field_u32(sf("sfSponsoringOwnerCount")),
        1
    );
}

#[test]
fn signer_list_set_destroy_requires_alternative_key_when_master_disabled() {
    let account = sample_account(0x31);
    let signer_list = signer_list_entry(account, 0, LSF_ONE_OWNER_COUNT);
    let ledger = empty_ledger(vec![
        account_root(account, 1, lsfDisableMaster),
        owner_dir_root(account, signer_list.key().to_owned()),
        signer_list,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = signer_list_set_tx(account, 0, &[]);

    let result = handle_real_dispatch(&mut view, &sttx, TxType::SIGNER_LIST_SET, None);

    assert_eq!(result, protocol::Ter::TEC_NO_ALTERNATIVE_KEY);
    assert!(
        view.read(signers_keylet(raw_account_id(account)))
            .expect("signer list read should succeed")
            .is_some()
    );
}

#[test]
fn permissioned_domain_set_dispatch_creates_sorted_domain_entry() {
    let account = sample_account(0x41);
    let issuer_a = sample_account(0x10);
    let issuer_b = sample_account(0x20);
    let ledger = empty_ledger(vec![account_root(account, 0, 0)]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = permissioned_domain_set_tx(
        account,
        9,
        None,
        &[
            (issuer_b, b"beta"),
            (issuer_a, b"zeta"),
            (issuer_a, b"alpha"),
        ],
    );

    let result = handle_real_dispatch(&mut view, &sttx, TxType::PERMISSIONED_DOMAIN_SET, None);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let domain = view
        .read(permissioned_domain_keylet(raw_account_id(account), 9))
        .expect("domain read should succeed")
        .expect("domain should exist");
    assert_eq!(
        domain.get_account_id(get_field_by_symbol("sfOwner")),
        account
    );
    assert_eq!(domain.get_field_u32(get_field_by_symbol("sfSequence")), 9);
    assert_eq!(domain.get_field_u64(get_field_by_symbol("sfOwnerNode")), 0);

    let credentials = domain.get_field_array(get_field_by_symbol("sfAcceptedCredentials"));
    assert_eq!(credentials.len(), 3);
    assert_eq!(
        credentials
            .get(0)
            .expect("first credential")
            .get_account_id(get_field_by_symbol("sfIssuer")),
        issuer_a
    );
    assert_eq!(
        credentials
            .get(0)
            .expect("first credential")
            .get_field_vl(get_field_by_symbol("sfCredentialType")),
        b"alpha"
    );
    assert_eq!(
        credentials
            .get(1)
            .expect("second credential")
            .get_account_id(get_field_by_symbol("sfIssuer")),
        issuer_a
    );
    assert_eq!(
        credentials
            .get(1)
            .expect("second credential")
            .get_field_vl(get_field_by_symbol("sfCredentialType")),
        b"zeta"
    );
    assert_eq!(
        credentials
            .get(2)
            .expect("third credential")
            .get_account_id(get_field_by_symbol("sfIssuer")),
        issuer_b
    );

    let owner = view
        .read(account_keylet(raw_account_id(account)))
        .expect("owner read should succeed")
        .expect("owner should exist");
    assert_eq!(owner.get_field_u32(get_field_by_symbol("sfOwnerCount")), 1);

    let owner_dir = view
        .read(owner_dir_keylet(raw_account_id(account)))
        .expect("owner dir read should succeed")
        .expect("owner dir should exist");
    assert_eq!(
        owner_dir
            .get_field_v256(get_field_by_symbol("sfIndexes"))
            .value(),
        &[domain.key().to_owned()]
    );
}

#[test]
fn permissioned_domain_set_reserve_uses_sponsor_adjusted_owner_count() {
    let account = sample_account(0x49);
    let mut account_sle = account_root_with_balance(account, 1, 0, 160);
    account_sle.set_field_u32(sf("sfSponsoredOwnerCount"), 1);
    let mut ledger = empty_ledger(vec![account_sle]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 100,
        increment: 50,
    });
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = permissioned_domain_set_tx(account, 9, None, &[]);

    // Pinned accountReserve computes (OwnerCount + 1 - SponsoredOwnerCount),
    // so this needs 150 drops and succeeds. The obsolete OwnerCount+1 path
    // would incorrectly require 200 drops and reject it.
    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::PERMISSIONED_DOMAIN_SET, None),
        Ter::TES_SUCCESS
    );
    assert!(
        view.read(permissioned_domain_keylet(raw_account_id(account), 9))
            .expect("domain read")
            .is_some()
    );
}

#[test]
fn permissioned_domain_set_dispatch_updates_existing_domain() {
    let account = sample_account(0x51);
    let issuer_a = sample_account(0x12);
    let issuer_b = sample_account(0x34);
    let existing = permissioned_domain_entry(account, 7, 0, &[(issuer_b, b"legacy")]);
    let ledger = empty_ledger(vec![
        account_root(account, 1, 0),
        owner_dir_root(account, existing.key().to_owned()),
        existing.clone(),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = permissioned_domain_set_tx(
        account,
        11,
        Some(existing.key().to_owned()),
        &[(issuer_b, b"beta"), (issuer_a, b"alpha")],
    );

    let result = handle_real_dispatch(&mut view, &sttx, TxType::PERMISSIONED_DOMAIN_SET, None);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let updated = view
        .read(protocol::permissioned_domain_keylet_from_id(
            existing.key().to_owned(),
        ))
        .expect("updated domain read should succeed")
        .expect("updated domain should exist");
    let credentials = updated.get_field_array(get_field_by_symbol("sfAcceptedCredentials"));
    assert_eq!(credentials.len(), 2);
    assert_eq!(
        credentials
            .get(0)
            .expect("first credential")
            .get_account_id(get_field_by_symbol("sfIssuer")),
        issuer_a
    );
    assert_eq!(
        credentials
            .get(0)
            .expect("first credential")
            .get_field_vl(get_field_by_symbol("sfCredentialType")),
        b"alpha"
    );
    assert_eq!(
        credentials
            .get(1)
            .expect("second credential")
            .get_account_id(get_field_by_symbol("sfIssuer")),
        issuer_b
    );

    let owner = view
        .read(account_keylet(raw_account_id(account)))
        .expect("owner read should succeed")
        .expect("owner should exist");
    assert_eq!(owner.get_field_u32(get_field_by_symbol("sfOwnerCount")), 1);
}

#[test]
fn permissioned_domain_delete_dispatch_removes_loaded_domain() {
    let account = sample_account(0x61);
    let domain = permissioned_domain_entry(account, 13, 0, &[(sample_account(0x71), b"alpha")]);
    let ledger = empty_ledger(vec![
        account_root(account, 1, 0),
        owner_dir_root(account, domain.key().to_owned()),
        domain.clone(),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = permissioned_domain_delete_tx(account, domain.key().to_owned());

    let result = handle_real_dispatch(&mut view, &sttx, TxType::PERMISSIONED_DOMAIN_DELETE, None);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    assert!(
        view.read(protocol::permissioned_domain_keylet_from_id(
            domain.key().to_owned()
        ))
        .expect("domain read should succeed")
        .is_none()
    );
    let owner = view
        .read(account_keylet(raw_account_id(account)))
        .expect("owner read should succeed")
        .expect("owner should exist");
    assert_eq!(owner.get_field_u32(get_field_by_symbol("sfOwnerCount")), 0);
    let owner_dir = view
        .read(owner_dir_keylet(raw_account_id(account)))
        .expect("owner dir read should succeed")
        .expect("owner dir should remain");
    assert!(
        owner_dir
            .get_field_v256(get_field_by_symbol("sfIndexes"))
            .value()
            .is_empty()
    );
}

#[test]
fn credential_create_dispatch_uses_issuer_and_subject_nodes() {
    let issuer = sample_account(0x71);
    let subject = sample_account(0x72);
    let credential_type = b"kyc";
    let ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 0, 0, 10_000_000),
        account_root_with_balance(subject, 0, 0, 10_000_000),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = credential_create_tx(issuer, subject, credential_type);

    let result = handle_real_dispatch(
        &mut view,
        &sttx,
        TxType::CREDENTIAL_CREATE,
        Some(10_000_000),
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let credential = view
        .read(credential_keylet(subject, issuer, credential_type))
        .expect("credential read should succeed")
        .expect("credential should exist");
    assert_eq!(
        credential.get_field_u64(get_field_by_symbol("sfIssuerNode")),
        0
    );
    assert_eq!(
        credential.get_field_u64(get_field_by_symbol("sfSubjectNode")),
        0
    );
    assert!(!credential.is_field_present(get_field_by_symbol("sfOwnerNode")));

    let issuer_root = view
        .read(account_keylet(raw_account_id(issuer)))
        .expect("issuer read should succeed")
        .expect("issuer should exist");
    let subject_root = view
        .read(account_keylet(raw_account_id(subject)))
        .expect("subject read should succeed")
        .expect("subject should exist");
    assert_eq!(
        issuer_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        1
    );
    assert_eq!(
        subject_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        0
    );
}

#[test]
fn cleanup_3_3_0_rejects_pseudo_accounts_as_credential_subjects_and_preauth_targets() {
    let issuer = sample_account(0xC1);
    let owner = sample_account(0xC2);
    let pseudo = sample_account(0xC3);
    let mut pseudo_root = account_root_with_balance(pseudo, 0, 0, 10_000_000);
    pseudo_root.set_field_h256(sf("sfAMMID"), sample_uint256(0xC4));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 0, 0, 10_000_000),
        account_root_with_balance(owner, 0, 0, 10_000_000),
        pseudo_root,
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::fix_cleanup_3_3_0()]));

    let mut credential_view = ApplyViewImpl::new(Arc::new(ledger.clone()), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut credential_view,
            &credential_create_tx(issuer, pseudo, b"pseudo"),
            TxType::CREDENTIAL_CREATE,
            Some(10_000_000),
        ),
        Ter::TEC_PSEUDO_ACCOUNT
    );

    let preauth = STTx::new(TxType::DEPOSIT_PREAUTH, |object| {
        object.set_account_id(sf("sfAccount"), owner);
        object.set_account_id(sf("sfAuthorize"), pseudo);
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_field_amount(sf("sfFee"), test_xrp(10));
    });
    let mut preauth_view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut preauth_view,
            &preauth,
            TxType::DEPOSIT_PREAUTH,
            Some(10_000_000),
        ),
        Ter::TEC_PSEUDO_ACCOUNT
    );
}

#[test]
fn trust_set_rejects_new_non_lp_trustline_to_pseudo_account() {
    let account = sample_account(0xD1);
    let vault = sample_account(0xD2);
    let mut vault_root = account_root_with_balance(vault, 0, 0, 10_000_000);
    vault_root.set_field_h256(sf("sfVaultID"), sample_uint256(0xD3));
    let ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 10_000_000),
        vault_root,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::TRUST_SET, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_amount(
            sf("sfLimitAmount"),
            iou_amount(
                sf("sfLimitAmount"),
                Issue::new(currency_from_string("USD"), vault),
                100,
            ),
        );
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::TRUST_SET, Some(10_000_000)),
        Ter::TEC_NO_PERMISSION
    );

    let amm_account = sample_account(0xD4);
    let asset_issuer = sample_account(0xD5);
    let usd = Issue::new(currency_from_string("USD"), asset_issuer);
    let eur = Issue::new(currency_from_string("EUR"), asset_issuer);
    let amm = amm_entry(amm_account, usd, eur, 100, vec![], 0);
    let mut amm_root = account_root_with_balance(amm_account, 0, 0, 10_000_000);
    amm_root.set_field_h256(sf("sfAMMID"), *amm.key());
    let trust_tx = |currency| {
        STTx::new(TxType::TRUST_SET, |tx| {
            tx.set_account_id(sf("sfAccount"), account);
            tx.set_field_amount(
                sf("sfLimitAmount"),
                iou_amount(sf("sfLimitAmount"), Issue::new(currency, amm_account), 100),
            );
        })
    };
    let amm_ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 10_000_000),
        amm_root.clone(),
        amm,
    ]);
    let mut wrong_lp_view = ApplyViewImpl::new(Arc::new(amm_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut wrong_lp_view,
            &trust_tx(currency_from_string("GBP")),
            TxType::TRUST_SET,
            Some(10_000_000),
        ),
        Ter::TEC_NO_PERMISSION
    );

    let empty_amm = amm_entry(amm_account, usd, eur, 0, vec![], 0);
    let empty_amm_ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 10_000_000),
        amm_root,
        empty_amm,
    ]);
    let mut empty_amm_view = ApplyViewImpl::new(Arc::new(empty_amm_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut empty_amm_view,
            &trust_tx(amm_lpt_currency(usd.currency, eur.currency)),
            TxType::TRUST_SET,
            Some(10_000_000),
        ),
        Ter::TEC_AMM_EMPTY
    );
}

#[test]
fn clawback_enforces_rippled_preflight_and_preclaim_decision_families() {
    let issuer = sample_account(0xE1);
    let holder = sample_account(0xE2);
    let other_issuer = sample_account(0xE3);
    let currency = currency_from_string("USD");
    let iou = iou_amount(sf("sfAmount"), Issue::new(currency, holder), 10);
    let iou_tx = |with_holder: bool| {
        STTx::new(TxType::CLAWBACK, |tx| {
            tx.set_account_id(sf("sfAccount"), issuer);
            tx.set_field_amount(sf("sfAmount"), iou.clone());
            if with_holder {
                tx.set_account_id(sf("sfHolder"), holder);
            }
        })
    };

    let mut empty = ApplyViewImpl::new(Arc::new(empty_ledger(Vec::new())), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut empty, &iou_tx(true), TxType::CLAWBACK, None),
        Ter::TEM_MALFORMED
    );

    let mpt_id = share_id_for(other_issuer, 1);
    let mpt_issue = MPTIssue::new(mpt_id);
    let mpt_tx = STTx::new(TxType::CLAWBACK, |tx| {
        tx.set_account_id(sf("sfAccount"), issuer);
        tx.set_account_id(sf("sfHolder"), holder);
        tx.set_field_amount(
            sf("sfAmount"),
            STAmount::from_mpt_amount(sf("sfAmount"), MPTAmount::from_value(10), mpt_issue),
        );
    });
    assert_eq!(
        handle_real_dispatch(&mut empty, &mpt_tx, TxType::CLAWBACK, None),
        Ter::TEM_DISABLED
    );

    let mut no_freeze_issuer = account_root_with_balance(
        issuer,
        0,
        protocol::lsfAllowTrustLineClawback | protocol::lsfNoFreeze,
        10_000_000,
    );
    no_freeze_issuer.set_field_u32(sf("sfSequence"), 1);
    let ledger = empty_ledger(vec![
        no_freeze_issuer,
        account_root_with_balance(holder, 0, 0, 10_000_000),
    ]);
    let mut no_freeze = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut no_freeze, &iou_tx(false), TxType::CLAWBACK, None),
        Ter::TEC_NO_PERMISSION
    );

    let mut pseudo_holder = account_root_with_balance(holder, 0, 0, 10_000_000);
    pseudo_holder.set_field_h256(sf("sfAMMID"), sample_uint256(0xE4));
    let mut pseudo_ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 0, protocol::lsfAllowTrustLineClawback, 10_000_000),
        pseudo_holder.clone(),
    ]);
    pseudo_ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut pseudo_view = ApplyViewImpl::new(Arc::new(pseudo_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut pseudo_view, &iou_tx(false), TxType::CLAWBACK, None),
        Ter::TEC_PSEUDO_ACCOUNT
    );
    let amm_ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 0, protocol::lsfAllowTrustLineClawback, 10_000_000),
        pseudo_holder,
    ]);
    let mut amm_view = ApplyViewImpl::new(Arc::new(amm_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut amm_view, &iou_tx(false), TxType::CLAWBACK, None),
        Ter::TEC_AMM_ACCOUNT
    );

    let direction_ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 0, protocol::lsfAllowTrustLineClawback, 10_000_000),
        account_root_with_balance(holder, 0, 0, 10_000_000),
        trust_line_entry(issuer, holder, currency, 10),
    ]);
    let mut direction_view = ApplyViewImpl::new(Arc::new(direction_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut direction_view, &iou_tx(false), TxType::CLAWBACK, None,),
        Ter::TEC_NO_PERMISSION
    );

    let empty_balance_ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 0, protocol::lsfAllowTrustLineClawback, 10_000_000),
        account_root_with_balance(holder, 0, 0, 10_000_000),
        trust_line_entry(issuer, holder, currency, 0),
    ]);
    let mut empty_balance_view =
        ApplyViewImpl::new(Arc::new(empty_balance_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut empty_balance_view,
            &iou_tx(false),
            TxType::CLAWBACK,
            None,
        ),
        Ter::TEC_INSUFFICIENT_FUNDS
    );

    let mut mpt_ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 0, 0, 10_000_000),
        account_root_with_balance(holder, 0, 0, 10_000_000),
        mpt_issuance_entry(other_issuer, 1, 100, protocol::lsfMPTCanClawback),
        mptoken_entry(holder, mpt_id, 50),
    ]);
    mpt_ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV1")]));
    let mut wrong_issuer = ApplyViewImpl::new(Arc::new(mpt_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(&mut wrong_issuer, &mpt_tx, TxType::CLAWBACK, None),
        Ter::TEC_NO_PERMISSION
    );
}

#[test]
fn credential_accept_dispatch_moves_owner_count_and_sets_accepted_flag() {
    let issuer = sample_account(0x73);
    let subject = sample_account(0x74);
    let credential_type = b"email";
    let credential = credential_entry(subject, issuer, credential_type, 0, Some(0), 0, None);
    let ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 1, 0, 10_000_000),
        account_root_with_balance(subject, 0, 0, 10_000_000),
        owner_dir_root(issuer, credential.key().to_owned()),
        owner_dir_root(subject, credential.key().to_owned()),
        credential,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = credential_accept_tx(subject, issuer, credential_type);

    let result = handle_real_dispatch(
        &mut view,
        &sttx,
        TxType::CREDENTIAL_ACCEPT,
        Some(10_000_000),
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let credential = view
        .read(credential_keylet(subject, issuer, credential_type))
        .expect("credential read should succeed")
        .expect("credential should exist");
    assert!(credential.is_flag(protocol::lsfAccepted));

    let issuer_root = view
        .read(account_keylet(raw_account_id(issuer)))
        .expect("issuer read should succeed")
        .expect("issuer should exist");
    let subject_root = view
        .read(account_keylet(raw_account_id(subject)))
        .expect("subject read should succeed")
        .expect("subject should exist");
    assert_eq!(
        issuer_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        0
    );
    assert_eq!(
        subject_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        1
    );
}

#[test]
fn credential_reserve_sponsor_same_account_counter_stays_balanced_on_accept() {
    let issuer = sample_account(0xA1);
    let subject = sample_account(0xA2);
    let create_sponsor = sample_account(0xA3);
    let accept_sponsor = create_sponsor;
    let credential_type = b"sponsored";
    let ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 0, 0, 10_000_000),
        account_root_with_balance(subject, 0, 0, 10_000_000),
        account_root_with_balance(create_sponsor, 0, 0, 10_000_000),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let mut create = credential_create_tx(issuer, subject, credential_type);
    create.set_account_id(sf("sfSponsor"), create_sponsor);
    create.set_field_u32(sf("sfSponsorFlags"), ledger::SPF_SPONSOR_RESERVE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &create,
            TxType::CREDENTIAL_CREATE,
            Some(10_000_000),
        ),
        Ter::TES_SUCCESS
    );
    let credential_key = credential_keylet(subject, issuer, credential_type);
    assert_eq!(
        view.read(credential_key)
            .expect("credential read")
            .expect("credential exists")
            .get_account_id(sf("sfSponsor")),
        create_sponsor
    );

    let mut accept = credential_accept_tx(subject, issuer, credential_type);
    accept.set_account_id(sf("sfSponsor"), accept_sponsor);
    accept.set_field_u32(sf("sfSponsorFlags"), ledger::SPF_SPONSOR_RESERVE);
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &accept,
            TxType::CREDENTIAL_ACCEPT,
            Some(10_000_000),
        ),
        Ter::TES_SUCCESS
    );

    let credential = view
        .read(credential_key)
        .expect("credential read")
        .expect("credential exists");
    assert!(credential.is_flag(protocol::lsfAccepted));
    assert_eq!(credential.get_account_id(sf("sfSponsor")), accept_sponsor);
    let issuer_root = view
        .read(account_keylet(raw_account_id(issuer)))
        .expect("issuer read")
        .expect("issuer exists");
    let subject_root = view
        .read(account_keylet(raw_account_id(subject)))
        .expect("subject read")
        .expect("subject exists");
    let accept_sponsor_root = view
        .read(account_keylet(raw_account_id(accept_sponsor)))
        .expect("accept sponsor read")
        .expect("accept sponsor exists");
    assert_eq!(issuer_root.get_field_u32(sf("sfSponsoredOwnerCount")), 0);
    assert_eq!(subject_root.get_field_u32(sf("sfSponsoredOwnerCount")), 1);
    assert_eq!(
        accept_sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")),
        1
    );
}

#[test]
fn deposit_preauth_reserve_sponsor_is_assigned_and_released() {
    let owner = sample_account(0xB1);
    let authorized = sample_account(0xB2);
    let sponsor = sample_account(0xB3);
    let ledger = empty_ledger(vec![
        account_root_with_balance(owner, 0, 0, 10_000_000),
        account_root_with_balance(authorized, 0, 0, 10_000_000),
        account_root_with_balance(sponsor, 0, 0, 10_000_000),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let mut authorize = STTx::new(TxType::DEPOSIT_PREAUTH, |object| {
        object.set_account_id(sf("sfAccount"), owner);
        object.set_account_id(sf("sfAuthorize"), authorized);
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_field_amount(sf("sfFee"), test_xrp(10));
    });
    authorize.set_account_id(sf("sfSponsor"), sponsor);
    authorize.set_field_u32(sf("sfSponsorFlags"), ledger::SPF_SPONSOR_RESERVE);
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &authorize,
            TxType::DEPOSIT_PREAUTH,
            Some(10_000_000),
        ),
        Ter::TES_SUCCESS
    );
    let keylet =
        protocol::deposit_preauth_keylet(raw_account_id(owner), raw_account_id(authorized));
    assert_eq!(
        view.read(keylet)
            .expect("preauth read")
            .expect("preauth exists")
            .get_account_id(sf("sfSponsor")),
        sponsor
    );

    let unauthorize = STTx::new(TxType::DEPOSIT_PREAUTH, |object| {
        object.set_account_id(sf("sfAccount"), owner);
        object.set_account_id(sf("sfUnauthorize"), authorized);
        object.set_field_u32(sf("sfSequence"), 2);
        object.set_field_amount(sf("sfFee"), test_xrp(10));
    });
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &unauthorize,
            TxType::DEPOSIT_PREAUTH,
            Some(10_000_000),
        ),
        Ter::TES_SUCCESS
    );
    assert!(view.read(keylet).expect("preauth read").is_none());
    let owner_root = view
        .read(account_keylet(raw_account_id(owner)))
        .expect("owner read")
        .expect("owner exists");
    let sponsor_root = view
        .read(account_keylet(raw_account_id(sponsor)))
        .expect("sponsor read")
        .expect("sponsor exists");
    assert_eq!(owner_root.get_field_u32(sf("sfOwnerCount")), 0);
    assert_eq!(owner_root.get_field_u32(sf("sfSponsoredOwnerCount")), 0);
    assert_eq!(sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")), 0);
}

#[test]
fn payment_deposit_auth_accepts_matching_credential_preauth() {
    let source = sample_account(0xC1);
    let destination = sample_account(0xC2);
    let issuer = sample_account(0xC3);
    let credential_type = b"kyc";
    let credential = credential_entry(
        source,
        issuer,
        credential_type,
        0,
        Some(0),
        protocol::lsfAccepted,
        None,
    );
    let credential_hash = protocol::sha512_half_slices(&[issuer.data(), credential_type]);
    let preauth_keylet = protocol::deposit_preauth_credentials_keylet(
        raw_account_id(destination),
        &[credential_hash],
    );
    let mut authorized_credential = STObject::make_inner_object(sf("sfCredential"));
    authorized_credential.set_account_id(sf("sfIssuer"), issuer);
    authorized_credential.set_field_vl(sf("sfCredentialType"), credential_type);
    let mut authorized_credentials = STArray::new(sf("sfAuthorizeCredentials"));
    authorized_credentials.push_back(authorized_credential);
    let mut preauth = STLedgerEntry::new(preauth_keylet);
    preauth.set_account_id(sf("sfAccount"), destination);
    preauth.set_field_array(sf("sfAuthorizeCredentials"), authorized_credentials);
    preauth.set_field_u64(sf("sfOwnerNode"), 0);
    let ledger = empty_ledger(vec![
        account_root_with_balance(source, 0, 0, 2_000_000_000),
        account_root_with_balance(destination, 1, protocol::lsfDepositAuth, 10_000_000),
        account_root_with_balance(issuer, 0, 0, 10_000_000),
        credential,
        preauth,
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::PAYMENT, |object| {
        object.set_account_id(sf("sfAccount"), source);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_amount(sf("sfAmount"), test_xrp(1_000_000_000));
        object.set_field_v256(
            sf("sfCredentialIDs"),
            protocol::STVector256::from_values(
                sf("sfCredentialIDs"),
                vec![credential_keylet(source, issuer, credential_type).key],
            ),
        );
        object.set_field_u32(sf("sfSequence"), 1);
        object.set_field_amount(sf("sfFee"), test_xrp(10));
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::PAYMENT, Some(2_000_000_000)),
        Ter::TES_SUCCESS
    );
}

#[test]
fn credential_accept_dispatch_deletes_expired_credential_or_propagates_delete_failure() {
    let issuer = sample_account(0x75);
    let subject = sample_account(0x76);
    let credential_type = b"expired";
    let credential = credential_entry(subject, issuer, credential_type, 0, Some(0), 0, Some(10));
    let ledger = ledger_with_header(
        LedgerHeader {
            parent_close_time: 20,
            ..LedgerHeader::default()
        },
        vec![
            account_root_with_balance(issuer, 1, 0, 10_000_000),
            account_root_with_balance(subject, 0, 0, 10_000_000),
            owner_dir_root(issuer, credential.key().to_owned()),
            owner_dir_root(subject, credential.key().to_owned()),
            credential,
        ],
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = credential_accept_tx(subject, issuer, credential_type);

    let result = handle_real_dispatch(
        &mut view,
        &sttx,
        TxType::CREDENTIAL_ACCEPT,
        Some(10_000_000),
    );

    assert_eq!(result, protocol::Ter::TEC_EXPIRED);
    assert!(
        view.read(credential_keylet(subject, issuer, credential_type))
            .expect("credential read should succeed")
            .is_none()
    );

    let bad_credential_type = b"bad-expired";
    let bad_credential = credential_entry(
        subject,
        issuer,
        bad_credential_type,
        99,
        Some(0),
        0,
        Some(10),
    );
    let bad_ledger = ledger_with_header(
        LedgerHeader {
            parent_close_time: 20,
            ..LedgerHeader::default()
        },
        vec![
            account_root_with_balance(issuer, 1, 0, 10_000_000),
            account_root_with_balance(subject, 0, 0, 10_000_000),
            owner_dir_root(subject, bad_credential.key().to_owned()),
            bad_credential,
        ],
    );
    let mut bad_view = ApplyViewImpl::new(Arc::new(bad_ledger), ApplyFlags::NONE);
    let bad_sttx = credential_accept_tx(subject, issuer, bad_credential_type);

    let bad_result = handle_real_dispatch(
        &mut bad_view,
        &bad_sttx,
        TxType::CREDENTIAL_ACCEPT,
        Some(10_000_000),
    );

    assert_eq!(bad_result, protocol::Ter::TEF_BAD_LEDGER);
    assert!(
        bad_view
            .read(credential_keylet(subject, issuer, bad_credential_type))
            .expect("credential read should succeed")
            .is_some()
    );
}

#[test]
fn credential_delete_dispatch_allows_third_party_only_for_expired_credentials() {
    let issuer = sample_account(0x77);
    let subject = sample_account(0x78);
    let actor = sample_account(0x79);
    let credential_type = b"third-party";
    let credential = credential_entry(subject, issuer, credential_type, 0, Some(0), 0, Some(50));
    let ledger = ledger_with_header(
        LedgerHeader {
            parent_close_time: 20,
            ..LedgerHeader::default()
        },
        vec![
            account_root_with_balance(issuer, 1, 0, 10_000_000),
            account_root_with_balance(subject, 0, 0, 10_000_000),
            account_root_with_balance(actor, 0, 0, 10_000_000),
            owner_dir_root(issuer, credential.key().to_owned()),
            owner_dir_root(subject, credential.key().to_owned()),
            credential,
        ],
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = credential_delete_tx(actor, Some(subject), Some(issuer), credential_type);

    let result = handle_real_dispatch(
        &mut view,
        &sttx,
        TxType::CREDENTIAL_DELETE,
        Some(10_000_000),
    );

    assert_eq!(result, protocol::Ter::TEC_NO_PERMISSION);

    let expired_credential =
        credential_entry(subject, issuer, credential_type, 0, Some(0), 0, Some(10));
    let expired_ledger = ledger_with_header(
        LedgerHeader {
            parent_close_time: 20,
            ..LedgerHeader::default()
        },
        vec![
            account_root_with_balance(issuer, 1, 0, 10_000_000),
            account_root_with_balance(subject, 0, 0, 10_000_000),
            account_root_with_balance(actor, 0, 0, 10_000_000),
            owner_dir_root(issuer, expired_credential.key().to_owned()),
            owner_dir_root(subject, expired_credential.key().to_owned()),
            expired_credential,
        ],
    );
    let mut expired_view = ApplyViewImpl::new(Arc::new(expired_ledger), ApplyFlags::NONE);
    let expired_sttx = credential_delete_tx(actor, Some(subject), Some(issuer), credential_type);

    let expired_result = handle_real_dispatch(
        &mut expired_view,
        &expired_sttx,
        TxType::CREDENTIAL_DELETE,
        Some(10_000_000),
    );

    assert_eq!(expired_result, protocol::Ter::TES_SUCCESS);
    assert!(
        expired_view
            .read(credential_keylet(subject, issuer, credential_type))
            .expect("credential read should succeed")
            .is_none()
    );
}

#[test]
fn ledger_state_fix_repairs_broken_nft_page_links_through_dispatch() {
    let owner = sample_account(0x41);
    let bogus = sample_uint256(0x99);
    let base = protocol::nft_page_min_keylet(raw_account_id(owner));
    let first = protocol::nft_page_keylet(base.clone(), sample_uint256(0x11));
    let middle = protocol::nft_page_keylet(base, sample_uint256(0x22));
    let last = protocol::nft_page_max_keylet(raw_account_id(owner));
    let ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        nft_page_entry(first.clone(), sample_uint256(0x51), Some(bogus), None),
        nft_page_entry(middle.clone(), sample_uint256(0x52), Some(bogus), None),
        nft_page_entry(last.clone(), sample_uint256(0x53), Some(bogus), Some(bogus)),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = ledger_state_fix_tx(owner, Some(owner), 1);

    let result = handle_real_dispatch(&mut view, &sttx, TxType::LEDGER_STATE_FIX, None);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let first_page = view
        .read(first)
        .expect("first page read should succeed")
        .expect("first page should exist");
    assert!(!first_page.is_field_present(get_field_by_symbol("sfPreviousPageMin")));
    assert_eq!(
        first_page.get_field_h256(get_field_by_symbol("sfNextPageMin")),
        middle.key
    );

    let middle_page = view
        .read(middle)
        .expect("middle page read should succeed")
        .expect("middle page should exist");
    assert_eq!(
        middle_page.get_field_h256(get_field_by_symbol("sfPreviousPageMin")),
        first.key
    );
    assert_eq!(
        middle_page.get_field_h256(get_field_by_symbol("sfNextPageMin")),
        last.key
    );

    let last_page = view
        .read(last)
        .expect("last page read should succeed")
        .expect("last page should exist");
    assert_eq!(
        last_page.get_field_h256(get_field_by_symbol("sfPreviousPageMin")),
        middle.key
    );
    assert!(!last_page.is_field_present(get_field_by_symbol("sfNextPageMin")));
}

#[test]
fn ledger_state_fix_returns_failed_processing_when_no_repair_is_needed() {
    let owner = sample_account(0x51);
    let page = protocol::nft_page_max_keylet(raw_account_id(owner));
    let ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        nft_page_entry(page.clone(), sample_uint256(0x61), None, None),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = ledger_state_fix_tx(owner, Some(owner), 1);

    let result = handle_real_dispatch(&mut view, &sttx, TxType::LEDGER_STATE_FIX, None);

    assert_eq!(result, protocol::Ter::TEC_FAILED_PROCESSING);
    let repaired_page = view
        .read(page)
        .expect("page read should succeed")
        .expect("page should exist");
    assert!(!repaired_page.is_field_present(get_field_by_symbol("sfPreviousPageMin")));
    assert!(!repaired_page.is_field_present(get_field_by_symbol("sfNextPageMin")));
}

#[test]
fn ledger_state_fix_repairs_book_directory_exchange_rate() {
    let account = sample_account(0x42);
    let mut key_bytes = [0_u8; 32];
    key_bytes[24..].copy_from_slice(&5_u64.to_be_bytes());
    let book_dir = Uint256::from_array(key_bytes);
    let mut ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        book_directory_entry(book_dir, Some(7)),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "fixCleanup3_2_0",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = ledger_state_fix_book_tx(account, book_dir);

    let result = handle_real_dispatch(&mut view, &sttx, TxType::LEDGER_STATE_FIX, None);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let repaired = view
        .read(protocol::Keylet::new(
            LedgerEntryType::DirectoryNode,
            book_dir,
        ))
        .expect("directory read should succeed")
        .expect("directory should exist");
    assert_eq!(
        repaired.get_field_u64(get_field_by_symbol("sfExchangeRate")),
        protocol::quality_from_key(book_dir)
    );
}

#[test]
fn ledger_state_fix_book_exchange_rate_enforces_preclaim_guards() {
    let account = sample_account(0x43);
    let mut key_bytes = [0_u8; 32];
    key_bytes[24..].copy_from_slice(&5_u64.to_be_bytes());
    let book_dir = Uint256::from_array(key_bytes);

    let disabled_ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        book_directory_entry(book_dir, Some(7)),
    ]);
    let mut disabled_view = ApplyViewImpl::new(Arc::new(disabled_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut disabled_view,
            &ledger_state_fix_book_tx(account, book_dir),
            TxType::LEDGER_STATE_FIX,
            None
        ),
        protocol::Ter::TEM_DISABLED
    );

    let mut correct_ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        book_directory_entry(book_dir, Some(protocol::quality_from_key(book_dir))),
    ]);
    correct_ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "fixCleanup3_2_0",
    )]));
    let mut correct_view = ApplyViewImpl::new(Arc::new(correct_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut correct_view,
            &ledger_state_fix_book_tx(account, book_dir),
            TxType::LEDGER_STATE_FIX,
            None
        ),
        protocol::Ter::TEC_NO_PERMISSION
    );

    let mut missing_exchange_ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        book_directory_entry(book_dir, None),
    ]);
    missing_exchange_ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "fixCleanup3_2_0",
    )]));
    let mut missing_exchange_view =
        ApplyViewImpl::new(Arc::new(missing_exchange_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut missing_exchange_view,
            &ledger_state_fix_book_tx(account, book_dir),
            TxType::LEDGER_STATE_FIX,
            None
        ),
        protocol::Ter::TEC_NO_PERMISSION
    );
}

#[test]
fn offer_create_hybrid_domain_offer_places_domain_and_open_books() {
    let account = sample_account(0x55);
    let issuer = sample_account(0x56);
    let domain_id = permissioned_domain_keylet(raw_account_id(account), 7).key;
    let issue = Issue::new(currency_from_string("USD"), issuer);
    let taker_pays = STAmount::from_iou_amount(
        get_field_by_symbol("sfTakerPays"),
        IOUAmount::from_parts(5_000_000, -6).expect("valid iou"),
        issue,
    );
    let taker_gets = STAmount::from_xrp_amount(XRPAmount::from_drops(1_000));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 1, 0, 100_000_000),
        account_root_with_balance(issuer, 0, 0, 100_000_000),
        owner_dir_root(account, domain_id),
        permissioned_domain_entry(account, 7, 0, &[]),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("PermissionedDEX"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = offer_create_tx(
        account,
        1,
        taker_pays,
        taker_gets,
        protocol::tfHybrid,
        Some(domain_id),
    );

    let result = dispatch_with_pre_fee_balance(&mut view, &sttx, TxType::OFFER_CREATE);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let offer_keylet = protocol::offer_keylet(raw_account_id(account), 1);
    let offer = view
        .read(offer_keylet)
        .expect("offer read should succeed")
        .expect("offer should exist");
    assert!(offer.is_flag(protocol::lsfHybrid));
    assert_eq!(
        offer.get_field_h256(get_field_by_symbol("sfDomainID")),
        domain_id
    );
    let owner = view
        .read(account_keylet(raw_account_id(account)))
        .expect("owner read should succeed")
        .expect("owner should exist");
    assert_eq!(owner.get_field_u32(sf("sfOwnerCount")), 2);
    let owner_dir = view
        .read(owner_dir_keylet(raw_account_id(account)))
        .expect("owner directory read should succeed")
        .expect("owner directory should exist");
    let owner_indexes_value = owner_dir.get_field_v256(sf("sfIndexes"));
    let owner_indexes = owner_indexes_value.value();
    assert!(owner_indexes.contains(&domain_id));
    assert!(owner_indexes.contains(&offer_keylet.key));

    let primary_dir_key = offer.get_field_h256(get_field_by_symbol("sfBookDirectory"));
    let primary_dir = view
        .read(protocol::Keylet::new(
            LedgerEntryType::DirectoryNode,
            primary_dir_key,
        ))
        .expect("primary book directory read should succeed")
        .expect("primary book directory should exist");
    assert_eq!(
        primary_dir.get_field_h256(get_field_by_symbol("sfDomainID")),
        domain_id
    );
    assert_eq!(
        primary_dir.get_field_u64(get_field_by_symbol("sfExchangeRate")),
        protocol::quality_from_key(primary_dir_key)
    );
    assert_eq!(
        primary_dir
            .get_field_v256(get_field_by_symbol("sfIndexes"))
            .value(),
        &[offer_keylet.key]
    );

    let additional_books = offer.get_field_array(get_field_by_symbol("sfAdditionalBooks"));
    assert_eq!(additional_books.len(), 1);
    let open_book = additional_books.get(0).expect("open-book reference");
    let open_dir_key = open_book.get_field_h256(get_field_by_symbol("sfBookDirectory"));
    assert_ne!(open_dir_key, primary_dir_key);
    let open_dir = view
        .read(protocol::Keylet::new(
            LedgerEntryType::DirectoryNode,
            open_dir_key,
        ))
        .expect("open book directory read should succeed")
        .expect("open book directory should exist");
    assert!(!open_dir.is_field_present(get_field_by_symbol("sfDomainID")));
    assert_eq!(
        open_dir.get_field_u64(get_field_by_symbol("sfExchangeRate")),
        primary_dir.get_field_u64(get_field_by_symbol("sfExchangeRate"))
    );
    assert_eq!(
        open_dir
            .get_field_v256(get_field_by_symbol("sfIndexes"))
            .value(),
        &[offer_keylet.key]
    );
}

#[test]
fn offer_create_crosses_equal_quality_permissioned_domain_offer() {
    let taker = sample_account(0x51);
    let offer_owner = sample_account(0x52);
    let credential_issuer = sample_account(0x53);
    let credential_type = b"graduate certificate";
    let domain_sequence = 7;
    let domain_id = permissioned_domain_keylet(raw_account_id(taker), domain_sequence).key;
    let usd = currency_from_string("USD");
    let issue = Issue::new(usd, offer_owner);

    let mut ledger = empty_ledger(vec![
        account_root_with_balance(taker, 1, 1, 100_000_000),
        account_root_with_balance(offer_owner, 1, 0, 100_000_000),
        account_root_with_balance(credential_issuer, 1, 0, 100_000_000),
        trust_line_entry(taker, offer_owner, usd, 0),
        permissioned_domain_entry(
            taker,
            domain_sequence,
            0,
            &[(credential_issuer, credential_type)],
        ),
        credential_entry(
            offer_owner,
            credential_issuer,
            credential_type,
            0,
            Some(0),
            protocol::lsfAccepted,
            None,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("Credentials"),
        protocol::feature_id("PermissionedDEX"),
        protocol::feature_id("fixCleanup3_2_0"),
        protocol::fix_cleanup_3_3_0(),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let maker = offer_create_tx(
        offer_owner,
        1,
        STAmount::from_xrp_amount(XRPAmount::from_drops(2_000_000)),
        STAmount::from_iou_amount(
            sf("sfTakerGets"),
            IOUAmount::from_parts(2, 0).expect("two USD"),
            issue,
        ),
        protocol::tfSell,
        Some(domain_id),
    );
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &maker, TxType::OFFER_CREATE),
        Ter::TES_SUCCESS
    );
    assert!(
        view.read(protocol::offer_keylet(raw_account_id(offer_owner), 1))
            .expect("maker offer read")
            .is_some()
    );

    let crossing = offer_create_tx(
        taker,
        1,
        STAmount::from_iou_amount(
            sf("sfTakerPays"),
            IOUAmount::from_parts(2, 0).expect("two USD"),
            issue,
        ),
        STAmount::from_xrp_amount(XRPAmount::from_drops(2_000_000)),
        0,
        Some(domain_id),
    );
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &crossing, TxType::OFFER_CREATE),
        Ter::TES_SUCCESS
    );
    assert!(
        view.read(protocol::offer_keylet(raw_account_id(offer_owner), 1))
            .expect("consumed maker offer read")
            .is_none(),
        "the canonical equal-quality domain offer must be consumed"
    );
    assert!(
        view.read(protocol::offer_keylet(raw_account_id(taker), 1))
            .expect("crossing offer read")
            .is_none(),
        "a fully crossed taker offer must not be placed"
    );
}

#[test]
fn offer_create_cancel_hybrid_offer_removes_domain_and_open_book_entries() {
    let account = sample_account(0x5A);
    let issuer = sample_account(0x5B);
    let domain_id = permissioned_domain_keylet(raw_account_id(account), 7).key;
    let issue = Issue::new(currency_from_string("USD"), issuer);
    let taker_pays = STAmount::from_iou_amount(
        get_field_by_symbol("sfTakerPays"),
        IOUAmount::from_parts(5_000_000, -6).expect("valid iou"),
        issue,
    );
    let taker_gets = STAmount::from_xrp_amount(XRPAmount::from_drops(1_000));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 1, 0, 100_000_000),
        account_root_with_balance(issuer, 0, 0, 100_000_000),
        owner_dir_root(account, domain_id),
        permissioned_domain_entry(account, 7, 0, &[]),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("PermissionedDEX"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let create = offer_create_tx(
        account,
        1,
        taker_pays.clone(),
        taker_gets.clone(),
        protocol::tfHybrid,
        Some(domain_id),
    );
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &create, TxType::OFFER_CREATE),
        protocol::Ter::TES_SUCCESS
    );

    let offer_keylet = protocol::offer_keylet(raw_account_id(account), 1);
    let offer = view
        .read(offer_keylet)
        .expect("offer read should succeed")
        .expect("offer should exist");
    let primary_dir_key = offer.get_field_h256(get_field_by_symbol("sfBookDirectory"));
    let additional_books = offer.get_field_array(get_field_by_symbol("sfAdditionalBooks"));
    let open_book = additional_books.get(0).expect("open-book reference");
    let open_dir_key = open_book.get_field_h256(get_field_by_symbol("sfBookDirectory"));

    let cancel = offer_create_cancel_tx(
        account,
        2,
        1,
        taker_pays,
        taker_gets,
        protocol::tfImmediateOrCancel,
    );
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut view, &cancel, TxType::OFFER_CREATE),
        protocol::Ter::TEC_KILLED
    );

    assert!(
        view.read(offer_keylet)
            .expect("offer read should succeed")
            .is_none()
    );
    assert!(
        view.read(protocol::Keylet::new(
            LedgerEntryType::DirectoryNode,
            primary_dir_key
        ))
        .expect("primary book directory read should succeed")
        .is_none()
    );
    assert!(
        view.read(protocol::Keylet::new(
            LedgerEntryType::DirectoryNode,
            open_dir_key
        ))
        .expect("open book directory read should succeed")
        .is_none()
    );
    assert!(
        view.read(protocol::permissioned_domain_keylet_from_id(domain_id))
            .expect("domain read should succeed")
            .is_some(),
        "OfferSequence cancellation must preserve the preexisting domain"
    );
    let owner = view
        .read(account_keylet(raw_account_id(account)))
        .expect("owner read should succeed")
        .expect("owner should exist");
    assert_eq!(owner.get_field_u32(sf("sfOwnerCount")), 1);
    let owner_dir = view
        .read(owner_dir_keylet(raw_account_id(account)))
        .expect("owner directory read should succeed")
        .expect("owner directory should retain the domain");
    assert_eq!(
        owner_dir.get_field_v256(sf("sfIndexes")).value(),
        &[domain_id],
        "OfferSequence cancellation must remove only the offer owner-directory entry"
    );
}

#[test]
fn offer_create_hybrid_requires_domain_and_permissioned_dex_feature() {
    let account = sample_account(0x58);
    let issuer = sample_account(0x59);
    let issue = Issue::new(currency_from_string("USD"), issuer);
    let taker_pays = STAmount::from_iou_amount(
        get_field_by_symbol("sfTakerPays"),
        IOUAmount::from_parts(5_000_000, -6).expect("valid iou"),
        issue,
    );
    let taker_gets = STAmount::from_xrp_amount(XRPAmount::from_drops(1_000));

    let ledger = empty_ledger(vec![account_root_with_balance(account, 0, 0, 100_000_000)]);
    let mut no_domain_view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let no_domain_tx = offer_create_tx(
        account,
        1,
        taker_pays.clone(),
        taker_gets.clone(),
        protocol::tfHybrid,
        None,
    );
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut no_domain_view, &no_domain_tx, TxType::OFFER_CREATE,),
        protocol::Ter::TEM_INVALID_FLAG
    );

    let disabled_ledger = empty_ledger(vec![account_root_with_balance(account, 0, 0, 100_000_000)]);
    let mut disabled_view = ApplyViewImpl::new(Arc::new(disabled_ledger), ApplyFlags::NONE);
    let disabled_tx = offer_create_tx(
        account,
        1,
        taker_pays,
        taker_gets,
        protocol::tfHybrid,
        Some(sample_uint256(0x5A)),
    );
    assert_eq!(
        dispatch_with_pre_fee_balance(&mut disabled_view, &disabled_tx, TxType::OFFER_CREATE),
        protocol::Ter::TEM_DISABLED
    );
}

#[test]
fn delegate_set_create_inserts_delegate_and_dual_owner_dirs() {
    let account = sample_account(0x31);
    let authorize = sample_account(0x32);
    let mut ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        account_root(authorize, 0, 0),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "PermissionDelegationV1_1",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = delegate_set_tx(account, authorize, &[65_540]);

    let result = handle_real_dispatch(&mut view, &sttx, TxType::DELEGATE_SET, Some(1_000_000));

    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let delegate = view
        .read(protocol::delegate_keylet(
            raw_account_id(account),
            raw_account_id(authorize),
        ))
        .expect("delegate read should succeed")
        .expect("delegate should exist");
    assert_eq!(
        delegate.get_account_id(get_field_by_symbol("sfAccount")),
        account
    );
    assert_eq!(
        delegate.get_account_id(get_field_by_symbol("sfAuthorize")),
        authorize
    );
    let permissions = delegate.get_field_array(get_field_by_symbol("sfPermissions"));
    assert_eq!(permissions.len(), 1);
    assert_eq!(
        permissions
            .get(0)
            .expect("permission entry")
            .get_field_u32(get_field_by_symbol("sfPermissionValue")),
        65_540
    );

    let owner = view
        .read(account_keylet(raw_account_id(account)))
        .expect("owner read should succeed")
        .expect("owner should exist");
    assert_eq!(owner.get_field_u32(get_field_by_symbol("sfOwnerCount")), 1);

    let owner_dir = view
        .read(owner_dir_keylet(raw_account_id(account)))
        .expect("owner dir read should succeed")
        .expect("owner dir should exist");
    let dest_dir = view
        .read(owner_dir_keylet(raw_account_id(authorize)))
        .expect("authorize dir read should succeed")
        .expect("authorize dir should exist");
    assert_eq!(
        owner_dir.get_account_id(get_field_by_symbol("sfOwner")),
        account
    );
    assert_eq!(
        dest_dir.get_account_id(get_field_by_symbol("sfOwner")),
        authorize
    );
    assert_eq!(
        owner_dir
            .get_field_v256(get_field_by_symbol("sfIndexes"))
            .value(),
        &[delegate.key().to_owned()]
    );
    assert_eq!(
        dest_dir
            .get_field_v256(get_field_by_symbol("sfIndexes"))
            .value(),
        &[delegate.key().to_owned()]
    );
}

#[test]
fn delegate_set_reserve_uses_sponsor_adjusted_owner_and_account_counts() {
    let account = sample_account(0x9A);
    let authorize = sample_account(0x9B);
    let mut account_sle = account_root_with_balance(account, 1, 0, 160);
    account_sle.set_field_u32(sf("sfSponsoredOwnerCount"), 1);
    let mut ledger = empty_ledger(vec![account_sle, account_root(authorize, 0, 0)]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 100,
        increment: 50,
    });
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = delegate_set_tx(account, authorize, &[65_540]);

    // Pinned checkReserve charges one effective owner increment after
    // subtracting sponsored objects. That is 150 drops here; the former
    // account_reserve(OwnerCount+1) path incorrectly demanded 200.
    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::DELEGATE_SET, None),
        Ter::TES_SUCCESS
    );
}

#[test]
fn delegate_set_reserve_sponsor_is_persisted_and_counted_on_create_and_delete() {
    let account = sample_account(0x33);
    let authorize = sample_account(0x34);
    let sponsor = sample_account(0x35);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1),
        account_root(authorize, 0, 0),
        account_root_with_balance(sponsor, 0, 0, 100_000_000),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("PermissionDelegationV1_1"),
        protocol::feature_id("Sponsor"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let mut create = delegate_set_tx(account, authorize, &[65_540]);
    create.set_account_id(sf("sfSponsor"), sponsor);
    create.set_field_u32(sf("sfSponsorFlags"), ledger::SPF_SPONSOR_RESERVE);

    assert_eq!(
        handle_real_dispatch(&mut view, &create, TxType::DELEGATE_SET, Some(1)),
        Ter::TES_SUCCESS
    );
    let keylet = protocol::delegate_keylet(raw_account_id(account), raw_account_id(authorize));
    let delegate = view.read(keylet).unwrap().expect("sponsored Delegate");
    assert_eq!(delegate.get_account_id(sf("sfSponsor")), sponsor);
    let owner = view
        .read(account_keylet(raw_account_id(account)))
        .unwrap()
        .unwrap();
    let sponsor_root = view
        .read(account_keylet(raw_account_id(sponsor)))
        .unwrap()
        .unwrap();
    assert_eq!(owner.get_field_u32(sf("sfOwnerCount")), 1);
    assert_eq!(owner.get_field_u32(sf("sfSponsoredOwnerCount")), 1);
    assert_eq!(sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")), 1);

    let delete = delegate_set_tx(account, authorize, &[]);
    assert_eq!(
        handle_real_dispatch(&mut view, &delete, TxType::DELEGATE_SET, Some(1)),
        Ter::TES_SUCCESS
    );
    assert!(view.read(keylet).unwrap().is_none());
    let owner = view
        .read(account_keylet(raw_account_id(account)))
        .unwrap()
        .unwrap();
    let sponsor_root = view
        .read(account_keylet(raw_account_id(sponsor)))
        .unwrap()
        .unwrap();
    assert_eq!(owner.get_field_u32(sf("sfOwnerCount")), 0);
    assert_eq!(owner.get_field_u32(sf("sfSponsoredOwnerCount")), 0);
    assert_eq!(sponsor_root.get_field_u32(sf("sfSponsoringOwnerCount")), 0);
}

#[test]
fn delegate_set_delete_removes_existing_delegate() {
    let account = sample_account(0x41);
    let authorize = sample_account(0x42);
    let delegate = delegate_entry(account, authorize, &[65_540], 0, 0);
    let mut ledger = empty_ledger(vec![
        account_root(account, 1, 0),
        account_root(authorize, 0, 0),
        owner_dir_root(account, delegate.key().to_owned()),
        owner_dir_root(authorize, delegate.key().to_owned()),
        delegate,
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "PermissionDelegationV1_1",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = delegate_set_tx(account, authorize, &[]);

    let result = handle_real_dispatch(&mut view, &sttx, TxType::DELEGATE_SET, Some(1_000_000));

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    assert!(
        view.read(protocol::delegate_keylet(
            raw_account_id(account),
            raw_account_id(authorize),
        ))
        .expect("delegate read should succeed")
        .is_none()
    );
    let owner = view
        .read(account_keylet(raw_account_id(account)))
        .expect("owner read should succeed")
        .expect("owner should exist");
    assert_eq!(owner.get_field_u32(get_field_by_symbol("sfOwnerCount")), 0);
}

#[test]
fn batch_dispatch_returns_success_when_batch_feature_is_enabled() {
    let account = sample_account(0x61);
    let mut ledger = empty_ledger(vec![account_root(account, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_batch_v1_1()]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = batch_tx(account);

    let result = handle_real_dispatch(&mut view, &sttx, TxType::BATCH, None);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
}

#[test]
fn batch_submit_shell_applies_all_successful_inner_transactions() {
    let account = sample_account(0x61);
    let destination = sample_account(0x62);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000),
        account_root_with_balance(destination, 0, 0, 1_000_000),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_batch_v1_1()]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let first = inner_batch_payment_tx(account, destination, 2, 100);
    let second = inner_batch_payment_tx(account, destination, 3, 200);
    let batch = batch_tx_with_inner(account, protocol::tfIndependent, &[first, second]);

    let result = apply_submit_transactor_shell(&mut view, &batch, TxType::BATCH);

    assert_eq!(result, Ter::TES_SUCCESS);
    let source = view
        .read(account_keylet(raw_account_id(account)))
        .expect("source read should succeed")
        .expect("source should exist");
    let dest = view
        .read(account_keylet(raw_account_id(destination)))
        .expect("destination read should succeed")
        .expect("destination should exist");
    assert_eq!(source.get_field_u32(get_field_by_symbol("sfSequence")), 4);
    assert_eq!(
        source
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        999_690
    );
    assert_eq!(
        dest.get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000_300
    );
}

/// Parity: `../rippled/src/libxrpl/tx/transactors/system/Batch.cpp::Batch::preflight`
/// rejects non-empty inner `SigningPubKey`, and
/// `../rippled/src/libxrpl/tx/apply.cpp::applyBatchTransactions` reaches each
/// inner through `apply(..., parentBatchId, tx, TapBatch, ...)` before mutation.
#[test]
fn batch_submit_shell_rejects_invalid_inner_signature_before_mutating_batch_state() {
    let account = sample_account(0x63);
    let destination = sample_account(0x64);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000),
        account_root_with_balance(destination, 0, 0, 1_000_000),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_batch_v1_1()]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let first = inner_batch_payment_tx(account, destination, 2, 100);
    let mut invalid_inner = inner_batch_payment_tx(account, destination, 3, 200);
    invalid_inner.set_field_vl(get_field_by_symbol("sfSigningPubKey"), &[0x02; 33]);
    let batch = batch_tx_with_inner(account, protocol::tfAllOrNothing, &[first, invalid_inner]);

    let result = apply_submit_transactor_shell(&mut view, &batch, TxType::BATCH);

    assert_eq!(result, Ter::TEM_BAD_REGKEY);
    let source = view
        .read(account_keylet(raw_account_id(account)))
        .expect("source read should succeed")
        .expect("source should exist");
    let destination = view
        .read(account_keylet(raw_account_id(destination)))
        .expect("destination read should succeed")
        .expect("destination should exist");
    assert_eq!(source.get_field_u32(get_field_by_symbol("sfSequence")), 1);
    assert_eq!(
        source
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000_000
    );
    assert_eq!(
        destination
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000_000
    );
}

#[test]
fn batch_submit_shell_discards_inner_changes_in_all_or_nothing_mode() {
    let account = sample_account(0x63);
    let destination = sample_account(0x64);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000),
        account_root_with_balance(destination, 0, 0, 1_000_000),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_batch_v1_1()]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let first = inner_batch_payment_tx(account, destination, 2, 100);
    let second = inner_batch_payment_tx(account, destination, 3, 2_000_000);
    let batch = batch_tx_with_inner(account, protocol::tfAllOrNothing, &[first, second]);

    let result = apply_submit_transactor_shell(&mut view, &batch, TxType::BATCH);

    assert_eq!(result, Ter::TES_SUCCESS);
    let source = view
        .read(account_keylet(raw_account_id(account)))
        .expect("source read should succeed")
        .expect("source should exist");
    let dest = view
        .read(account_keylet(raw_account_id(destination)))
        .expect("destination read should succeed")
        .expect("destination should exist");
    assert_eq!(source.get_field_u32(get_field_by_symbol("sfSequence")), 2);
    assert_eq!(
        source
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        999_990
    );
    assert_eq!(
        dest.get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000_000
    );
}

#[test]
fn batch_submit_shell_stops_after_first_success_in_only_one_mode() {
    let account = sample_account(0x65);
    let destination = sample_account(0x66);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000),
        account_root_with_balance(destination, 0, 0, 1_000_000),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_batch_v1_1()]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let first = inner_batch_payment_tx(account, destination, 2, 100);
    let second = inner_batch_payment_tx(account, destination, 3, 200);
    let batch = batch_tx_with_inner(account, protocol::tfOnlyOne, &[first, second]);

    let result = apply_submit_transactor_shell(&mut view, &batch, TxType::BATCH);

    assert_eq!(result, Ter::TES_SUCCESS);
    let source = view
        .read(account_keylet(raw_account_id(account)))
        .expect("source read should succeed")
        .expect("source should exist");
    let dest = view
        .read(account_keylet(raw_account_id(destination)))
        .expect("destination read should succeed")
        .expect("destination should exist");
    assert_eq!(source.get_field_u32(get_field_by_symbol("sfSequence")), 3);
    assert_eq!(
        source
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        999_890
    );
    assert_eq!(
        dest.get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000_100
    );
}

#[test]
fn batch_submit_shell_applies_successful_prefix_until_failure() {
    let account = sample_account(0x67);
    let destination = sample_account(0x68);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000),
        account_root_with_balance(destination, 0, 0, 1_000_000),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_batch_v1_1()]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let first = inner_batch_payment_tx(account, destination, 2, 100);
    let second = inner_batch_payment_tx(account, destination, 3, 2_000_000);
    let third = inner_batch_payment_tx(account, destination, 4, 300);
    let batch = batch_tx_with_inner(account, protocol::tfUntilFailure, &[first, second, third]);

    let result = apply_submit_transactor_shell(&mut view, &batch, TxType::BATCH);

    assert_eq!(result, Ter::TES_SUCCESS);
    let source = view
        .read(account_keylet(raw_account_id(account)))
        .expect("source read should succeed")
        .expect("source should exist");
    let dest = view
        .read(account_keylet(raw_account_id(destination)))
        .expect("destination read should succeed")
        .expect("destination should exist");
    assert_eq!(source.get_field_u32(get_field_by_symbol("sfSequence")), 4);
    assert_eq!(
        source
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        999_890
    );
    assert_eq!(
        dest.get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000_100
    );
}

#[test]
fn loan_broker_set_create_mints_deterministic_pseudo_and_empty_holding() {
    let owner = sample_account(0x71);
    let issuer = sample_account(0x72);
    let vault_pseudo = sample_account(0x73);
    let currency = Currency::from_array([0x55; 20]);
    let vault_asset = Asset::Issue(Issue::new(currency, issuer));
    let vault = vault_entry(owner, vault_pseudo, 7, vault_asset);
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        vault,
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
    ]));
    let broker_keylet = protocol::loan_broker_keylet(raw_account_id(owner), 1);
    let expected_pseudo =
        pseudo_account_address(&ledger, broker_keylet.key).expect("pseudo account lookup");
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = loan_broker_set_tx(
        owner,
        protocol::vault_keylet(raw_account_id(owner), 7).key,
        1,
    );

    let result = handle_real_dispatch(&mut view, &sttx, TxType::LOAN_BROKER_SET, Some(1_000_000));

    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let broker = view
        .read(broker_keylet)
        .expect("broker read should succeed")
        .expect("broker should exist");
    assert_eq!(
        broker.get_field_h256(get_field_by_symbol("sfPreviousTxnID")),
        Uint256::zero(),
        "LoanBrokerSet do-apply must not pre-thread the new broker with its transaction ID"
    );
    assert_eq!(
        broker.get_account_id(get_field_by_symbol("sfAccount")),
        expected_pseudo
    );

    let pseudo = view
        .read(account_keylet(raw_account_id(expected_pseudo)))
        .expect("pseudo read should succeed")
        .expect("pseudo account should exist");
    assert_eq!(
        pseudo.get_field_h256(get_field_by_symbol("sfLoanBrokerID")),
        broker_keylet.key
    );
    assert_eq!(pseudo.get_field_u32(get_field_by_symbol("sfOwnerCount")), 1);

    let trust_line = view
        .read(line(issuer, expected_pseudo, currency))
        .expect("trust line read should succeed")
        .expect("trust line should exist");
    assert_eq!(trust_line.get_type(), LedgerEntryType::RippleState);
}

#[test]
fn loan_broker_set_create_rejects_no_default_ripple_before_mutation() {
    let owner = sample_account(0x6D);
    let issuer = sample_account(0x6E);
    let vault_pseudo = sample_account(0x6F);
    let currency = Currency::from_array([0x54; 20]);
    let vault_asset = Asset::Issue(Issue::new(currency, issuer));
    let vault = vault_entry(owner, vault_pseudo, 6, vault_asset);
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, 0),
        account_root(vault_pseudo, 0, 0),
        vault,
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
    ]));
    let broker_keylet = protocol::loan_broker_keylet(raw_account_id(owner), 1);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let sttx = loan_broker_set_tx(
        owner,
        protocol::vault_keylet(raw_account_id(owner), 6).key,
        1,
    );

    let result = handle_real_dispatch(&mut view, &sttx, TxType::LOAN_BROKER_SET, Some(1_000_000));

    assert_eq!(result, protocol::Ter::TER_NO_RIPPLE);
    assert!(
        view.read(broker_keylet)
            .expect("broker read should succeed")
            .is_none()
    );
    let owner_root = view
        .read(account_keylet(raw_account_id(owner)))
        .expect("owner read should succeed")
        .expect("owner should remain");
    assert_eq!(
        owner_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        0
    );
}

#[test]
fn loan_broker_set_update_rejects_non_owner_without_mutating() {
    let owner = sample_account(0x74);
    let other = sample_account(0x75);
    let vault_pseudo = sample_account(0x76);
    let broker_pseudo = sample_account(0x77);
    let vault_key = protocol::vault_keylet(raw_account_id(owner), 3).key;
    let broker_id = sample_uint256(0x78);
    let asset = Asset::Issue(xrp_issue());
    let mut broker = loan_broker_entry(
        broker_id,
        owner,
        broker_pseudo,
        vault_key,
        asset,
        10,
        0,
        0,
        0,
    );
    broker.set_field_vl(get_field_by_symbol("sfData"), b"old");
    let mut ledger = empty_ledger(vec![
        account_root(owner, 1, 0),
        account_root(other, 0, 0),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        vault_entry(owner, vault_pseudo, 3, asset),
        broker,
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = loan_broker_set_update_tx(other, vault_key, broker_id, None, Some(b"new"));
    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_BROKER_SET, Some(1_000_000));

    assert_eq!(result, protocol::Ter::TEC_NO_PERMISSION);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker.get_field_vl(get_field_by_symbol("sfData")),
        b"old".to_vec()
    );
}

#[test]
fn loan_broker_set_update_rejects_debt_maximum_below_current_debt() {
    let owner = sample_account(0x79);
    let vault_pseudo = sample_account(0x7A);
    let broker_pseudo = sample_account(0x7B);
    let vault_key = protocol::vault_keylet(raw_account_id(owner), 4).key;
    let broker_id = sample_uint256(0x7C);
    let asset = Asset::Issue(xrp_issue());
    let broker = loan_broker_entry(
        broker_id,
        owner,
        broker_pseudo,
        vault_key,
        asset,
        100,
        0,
        0,
        0,
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 1, 0),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        vault_entry(owner, vault_pseudo, 4, asset),
        broker,
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = loan_broker_set_update_tx(
        owner,
        vault_key,
        broker_id,
        Some(asset_number(asset, 50)),
        Some(b"new"),
    );
    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_BROKER_SET, Some(1_000_000));

    assert_eq!(result, protocol::Ter::TEC_LIMIT_EXCEEDED);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert!(!broker.is_field_present(get_field_by_symbol("sfDebtMaximum")));
    assert!(!broker.is_field_present(get_field_by_symbol("sfData")));
}

#[test]
fn loan_broker_set_update_rejects_unrepresentable_debt_maximum_without_mutating() {
    let owner = sample_account(0x7D);
    let issuer = sample_account(0x7E);
    let vault_pseudo = sample_account(0x7F);
    let broker_pseudo = sample_account(0x80);
    let vault_key = protocol::vault_keylet(raw_account_id(owner), 5).key;
    let broker_id = sample_uint256(0x81);
    let mpt_id = share_id_for(issuer, 1);
    let asset = Asset::MPTIssue(MPTIssue::new(mpt_id));
    let broker = loan_broker_entry(
        broker_id,
        owner,
        broker_pseudo,
        vault_key,
        asset,
        0,
        0,
        0,
        0,
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 1, 0),
        account_root(issuer, 1, 0),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        vault_entry(owner, vault_pseudo, 5, asset),
        broker,
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = loan_broker_set_update_tx(
        owner,
        vault_key,
        broker_id,
        Some(STNumber::from(
            RuntimeNumber::try_from_external_parts(15, -1, basics::number::get_mantissa_scale())
                .expect("fractional debt maximum should be a valid STNumber"),
        )),
        Some(b"new"),
    );
    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_BROKER_SET, Some(1_000_000));

    assert_eq!(result, protocol::Ter::TEC_PRECISION_LOSS);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert!(!broker.is_field_present(get_field_by_symbol("sfDebtMaximum")));
    assert!(!broker.is_field_present(get_field_by_symbol("sfData")));
}

#[test]
fn loan_broker_delete_cleans_empty_holding_and_pseudo_account() {
    let owner = sample_account(0x81);
    let issuer = sample_account(0x82);
    let vault_pseudo = sample_account(0x83);
    let currency = Currency::from_array([0x56; 20]);
    let vault_asset = Asset::Issue(Issue::new(currency, issuer));
    let vault_key = protocol::vault_keylet(raw_account_id(owner), 9).key;
    let broker_key = protocol::loan_broker_keylet(raw_account_id(owner), 1).key;
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        vault_entry(owner, vault_pseudo, 9, vault_asset),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let create = handle_real_dispatch(
        &mut view,
        &loan_broker_set_tx(owner, vault_key, 1),
        TxType::LOAN_BROKER_SET,
        Some(1_000_000),
    );
    assert_eq!(create, protocol::Ter::TES_SUCCESS);

    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_key))
        .expect("broker read should succeed")
        .expect("broker should exist");
    let pseudo = broker.get_account_id(get_field_by_symbol("sfAccount"));
    assert!(
        view.read(line(issuer, pseudo, currency))
            .expect("trust line read should succeed")
            .is_some()
    );

    let delete = handle_real_dispatch(
        &mut view,
        &loan_broker_delete_tx(owner, broker_key),
        TxType::LOAN_BROKER_DELETE,
        None,
    );
    assert_eq!(delete, protocol::Ter::TES_SUCCESS);
    assert!(
        view.read(protocol::loan_broker_keylet_from_key(broker_key))
            .expect("broker read should succeed")
            .is_none()
    );
    assert!(
        view.read(account_keylet(raw_account_id(pseudo)))
            .expect("pseudo read should succeed")
            .is_none()
    );
    assert!(
        view.read(line(issuer, pseudo, currency))
            .expect("trust line read should succeed")
            .is_none()
    );
    let owner_root = view
        .read(account_keylet(raw_account_id(owner)))
        .expect("owner read should succeed")
        .expect("owner should exist");
    assert_eq!(
        owner_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        0
    );
}

#[test]
fn loan_broker_entrypoints_reject_missing_broker_with_no_entry() {
    let owner = sample_account(0xB1);
    let issuer = sample_account(0xB2);
    let broker_id = sample_uint256(0xB3);
    let amount = STAmount::from_iou_amount(
        sf("sfAmount"),
        IOUAmount::from_parts(1, 0).expect("amount"),
        Issue::new(Currency::from_array([0xB4; 20]), issuer),
    );
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0), account_root(issuer, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_delete_tx(owner, broker_id),
            TxType::LOAN_BROKER_DELETE,
            None,
        ),
        protocol::Ter::TEC_NO_ENTRY
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_deposit_tx(owner, broker_id, amount.clone()),
            TxType::LOAN_BROKER_COVER_DEPOSIT,
            None,
        ),
        protocol::Ter::TEC_NO_ENTRY
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_withdraw_tx(owner, broker_id, amount.clone()),
            TxType::LOAN_BROKER_COVER_WITHDRAW,
            Some(1_000_000),
        ),
        protocol::Ter::TEC_NO_ENTRY
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_clawback_tx(issuer, broker_id, amount),
            TxType::LOAN_BROKER_COVER_CLAWBACK,
            None,
        ),
        protocol::Ter::TEC_NO_ENTRY
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_set_tx(owner, broker_id, 1, 1),
            TxType::LOAN_SET,
            Some(1_000_000),
        ),
        protocol::Ter::TEC_NO_ENTRY
    );
}

#[test]
fn loan_broker_delete_dispatch_rejects_zero_broker_id_before_lookup() {
    let owner = sample_account(0xB1);
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_delete_tx(owner, Uint256::zero()),
            TxType::LOAN_BROKER_DELETE,
            None,
        ),
        protocol::Ter::TEM_INVALID
    );
}

#[test]
fn loan_broker_cover_deposit_dispatch_rejects_malformed_before_lookup() {
    let owner = sample_account(0xB1);
    let issuer = sample_account(0xB2);
    let issue = Issue::new(Currency::from_array([0xB3; 20]), issuer);
    let zero_amount = STAmount::from_iou_amount(
        sf("sfAmount"),
        IOUAmount::from_parts(0, 0).expect("zero amount"),
        issue,
    );
    let positive_amount = iou_amount(sf("sfAmount"), issue, 1);
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0), account_root(issuer, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_deposit_tx(owner, Uint256::zero(), positive_amount),
            TxType::LOAN_BROKER_COVER_DEPOSIT,
            None,
        ),
        protocol::Ter::TEM_INVALID
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_deposit_tx(owner, sample_uint256(0xB4), zero_amount),
            TxType::LOAN_BROKER_COVER_DEPOSIT,
            None,
        ),
        protocol::Ter::TEM_BAD_AMOUNT
    );
}

#[test]
fn loan_broker_cover_withdraw_dispatch_rejects_malformed_before_lookup() {
    let owner = sample_account(0xB1);
    let issuer = sample_account(0xB2);
    let issue = Issue::new(Currency::from_array([0xB3; 20]), issuer);
    let zero_amount = STAmount::from_iou_amount(
        sf("sfAmount"),
        IOUAmount::from_parts(0, 0).expect("zero amount"),
        issue,
    );
    let positive_amount = iou_amount(sf("sfAmount"), issue, 1);
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0), account_root(issuer, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_withdraw_tx(owner, Uint256::zero(), positive_amount.clone()),
            TxType::LOAN_BROKER_COVER_WITHDRAW,
            Some(1_000_000),
        ),
        protocol::Ter::TEM_INVALID
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_withdraw_tx(owner, sample_uint256(0xB4), zero_amount),
            TxType::LOAN_BROKER_COVER_WITHDRAW,
            Some(1_000_000),
        ),
        protocol::Ter::TEM_BAD_AMOUNT
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_withdraw_to_tx(
                owner,
                AccountID::zero(),
                sample_uint256(0xB5),
                positive_amount,
            ),
            TxType::LOAN_BROKER_COVER_WITHDRAW,
            Some(1_000_000),
        ),
        protocol::Ter::TEM_MALFORMED
    );
}

#[test]
fn loan_broker_cover_withdraw_rejects_pseudo_destination_before_missing_broker() {
    let owner = sample_account(0xB6);
    let issuer = sample_account(0xB7);
    let pseudo_destination = sample_account(0xB8);
    let issue = Issue::new(Currency::from_array([0xB9; 20]), issuer);
    let amount = iou_amount(sf("sfAmount"), issue, 1);
    let mut pseudo_root = account_root(pseudo_destination, 0, 0);
    pseudo_root.set_field_h256(sf("sfVaultID"), sample_uint256(0xBA));
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, 0),
        pseudo_root,
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_withdraw_to_tx(
                owner,
                pseudo_destination,
                sample_uint256(0xBB),
                amount,
            ),
            TxType::LOAN_BROKER_COVER_WITHDRAW,
            Some(1_000_000),
        ),
        protocol::Ter::TEC_PSEUDO_ACCOUNT
    );
}

#[test]
fn loan_broker_cover_clawback_dispatch_rejects_malformed_before_lookup() {
    let issuer = sample_account(0xB1);
    let broker_id = sample_uint256(0xB2);
    let currency = Currency::from_array([0xB3; 20]);
    let issue = Issue::new(currency, issuer);
    let negative_amount = STAmount::from_iou_amount(
        sf("sfAmount"),
        IOUAmount::from_parts(-1, 0).expect("negative amount"),
        issue,
    );
    let native_amount = STAmount::from_xrp_amount(XRPAmount::from_drops(1));
    let self_issued_amount = iou_amount(sf("sfAmount"), issue, 1);
    let mut ledger = empty_ledger(vec![account_root(issuer, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_clawback_empty_tx(issuer),
            TxType::LOAN_BROKER_COVER_CLAWBACK,
            None,
        ),
        protocol::Ter::TEM_INVALID
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_clawback_tx(issuer, Uint256::zero(), self_issued_amount.clone()),
            TxType::LOAN_BROKER_COVER_CLAWBACK,
            None,
        ),
        protocol::Ter::TEM_INVALID
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_clawback_tx(issuer, broker_id, native_amount),
            TxType::LOAN_BROKER_COVER_CLAWBACK,
            None,
        ),
        protocol::Ter::TEM_BAD_AMOUNT
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_clawback_tx(issuer, broker_id, negative_amount),
            TxType::LOAN_BROKER_COVER_CLAWBACK,
            None,
        ),
        protocol::Ter::TEM_BAD_AMOUNT
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_cover_clawback_without_id_tx(issuer, self_issued_amount),
            TxType::LOAN_BROKER_COVER_CLAWBACK,
            None,
        ),
        protocol::Ter::TEM_INVALID
    );
}

#[test]
fn loan_broker_set_dispatch_rejects_preflight_malformed_before_lookup() {
    let owner = sample_account(0xB1);
    let vault_id = sample_uint256(0xB2);
    let broker_id = sample_uint256(0xB3);
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_set_tx(owner, Uint256::zero(), 1),
            TxType::LOAN_BROKER_SET,
            Some(1_000_000),
        ),
        protocol::Ter::TEM_INVALID
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_set_update_tx(owner, vault_id, Uint256::zero(), None, None),
            TxType::LOAN_BROKER_SET,
            Some(1_000_000),
        ),
        protocol::Ter::TEM_INVALID
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_set_update_with_management_fee_tx(owner, vault_id, broker_id, 1),
            TxType::LOAN_BROKER_SET,
            Some(1_000_000),
        ),
        protocol::Ter::TEM_INVALID
    );
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_broker_set_update_with_management_fee_tx(owner, vault_id, broker_id, 10_001),
            TxType::LOAN_BROKER_SET,
            Some(1_000_000),
        ),
        protocol::Ter::TEM_INVALID
    );
}

#[test]
fn loan_broker_delete_rejects_locked_mpt_cover_after_cleanup_3_2_0() {
    let owner = sample_account(0xB1);
    let issuer = sample_account(0xB2);
    let vault_pseudo = sample_account(0xB3);
    let broker_pseudo = sample_account(0xB4);
    let mpt_id = share_id_for(issuer, 7);
    let asset = Asset::MPTIssue(protocol::MPTIssue::new(mpt_id));
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 22).key;
    let broker_id = sample_uint256(0xB5);
    let mut broker = loan_broker_entry(
        broker_id,
        owner,
        broker_pseudo,
        vault_id,
        asset,
        0,
        5_000,
        0,
        0,
    );
    broker.set_field_u64(get_field_by_symbol("sfOwnerNode"), 0);
    broker.set_field_u64(get_field_by_symbol("sfVaultNode"), 0);
    let mut broker_cover = mptoken_entry(broker_pseudo, mpt_id, 5_000);
    broker_cover.set_field_u32(get_field_by_symbol("sfFlags"), protocol::lsfMPTLocked);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 2, 0),
        account_root(issuer, 0, 0),
        account_root(vault_pseudo, 1, 0),
        account_root_with_balance(broker_pseudo, 1, 0, 0),
        managed_vault_entry(owner, vault_pseudo, 22, asset, 0, 0, 0),
        broker,
        mpt_issuance_entry(
            issuer,
            7,
            5_000,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
        broker_cover,
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_delete_tx(owner, broker_id),
        TxType::LOAN_BROKER_DELETE,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_LOCKED);
    assert!(
        view.read(protocol::loan_broker_keylet_from_key(broker_id))
            .expect("broker read should succeed")
            .is_some()
    );
    assert!(
        view.read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(broker_pseudo),
        ))
        .expect("broker cover token read should succeed")
        .is_some()
    );
}

#[test]
fn loan_broker_delete_rejects_deep_frozen_owner_iou_cover() {
    let owner = sample_account(0xC1);
    let issuer = sample_account(0xC2);
    let vault_pseudo = sample_account(0xC3);
    let broker_pseudo = sample_account(0xC4);
    let currency = Currency::from_array([0xC5; 20]);
    let asset = Asset::Issue(Issue::new(currency, issuer));
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 24).key;
    let broker_id = sample_uint256(0xC6);
    let broker = loan_broker_entry(
        broker_id,
        owner,
        broker_pseudo,
        vault_id,
        asset,
        0,
        5_000,
        0,
        0,
    );
    let mut owner_line = trust_line_entry(owner, issuer, currency, 0);
    owner_line.set_field_u32(get_field_by_symbol("sfFlags"), protocol::lsfLowDeepFreeze);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 2, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 1, 0),
        account_root_with_balance(broker_pseudo, 1, 0, 0),
        owner_dir_root(owner, protocol::loan_broker_keylet_from_key(broker_id).key),
        owner_dir_root(
            vault_pseudo,
            protocol::loan_broker_keylet_from_key(broker_id).key,
        ),
        managed_vault_entry(owner, vault_pseudo, 24, asset, 0, 0, 0),
        broker,
        owner_line,
        trust_line_entry(issuer, broker_pseudo, currency, 5_000),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_delete_tx(owner, broker_id),
        TxType::LOAN_BROKER_DELETE,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_FROZEN);
    assert!(
        view.read(protocol::loan_broker_keylet_from_key(broker_id))
            .expect("broker read should succeed")
            .is_some()
    );
    assert!(
        view.read(account_keylet(raw_account_id(broker_pseudo)))
            .expect("broker pseudo read should succeed")
            .is_some()
    );
}

#[test]
fn loan_broker_delete_pays_unlocked_mpt_cover_and_cleans_pseudo_holding() {
    let owner = sample_account(0xB6);
    let issuer = sample_account(0xB7);
    let vault_pseudo = sample_account(0xB8);
    let broker_pseudo = sample_account(0xB9);
    let mpt_id = share_id_for(issuer, 8);
    let asset = Asset::MPTIssue(protocol::MPTIssue::new(mpt_id));
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 23).key;
    let broker_id = sample_uint256(0xBA);
    let broker = loan_broker_entry(
        broker_id,
        owner,
        broker_pseudo,
        vault_id,
        asset,
        0,
        5_000,
        0,
        0,
    );
    let broker_token_key =
        protocol::mptoken_keylet_from_mptid(mpt_id, raw_account_id(broker_pseudo));

    let mut ledger = empty_ledger(vec![
        account_root(owner, 2, 0),
        account_root(issuer, 0, 0),
        account_root(vault_pseudo, 1, 0),
        account_root_with_balance(broker_pseudo, 1, 0, 0),
        owner_dir_root(owner, protocol::loan_broker_keylet_from_key(broker_id).key),
        owner_dir_root(
            vault_pseudo,
            protocol::loan_broker_keylet_from_key(broker_id).key,
        ),
        owner_dir_root(broker_pseudo, broker_token_key.key),
        managed_vault_entry(owner, vault_pseudo, 23, asset, 0, 0, 0),
        broker,
        mpt_issuance_entry(issuer, 8, 5_000, MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG),
        mptoken_entry(broker_pseudo, mpt_id, 5_000),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_delete_tx(owner, broker_id),
        TxType::LOAN_BROKER_DELETE,
        None,
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    assert!(
        view.read(protocol::loan_broker_keylet_from_key(broker_id))
            .expect("broker read should succeed")
            .is_none()
    );
    assert!(
        view.read(account_keylet(raw_account_id(broker_pseudo)))
            .expect("broker pseudo read should succeed")
            .is_none()
    );
    assert!(
        view.read(broker_token_key)
            .expect("broker token read should succeed")
            .is_none()
    );
    let owner_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(owner),
        ))
        .expect("owner token read should succeed")
        .expect("owner should receive MPT cover");
    assert_eq!(
        owner_token.get_field_u64(get_field_by_symbol("sfMPTAmount")),
        5_000
    );
}

#[test]
fn loan_delete_removes_loan_and_keeps_broker_pseudo_lifecycle_intact() {
    let owner = sample_account(0x91);
    let borrower = sample_account(0x92);
    let issuer = sample_account(0x93);
    let vault_pseudo = sample_account(0x94);
    let currency = Currency::from_array([0x57; 20]);
    let vault_asset = Asset::Issue(Issue::new(currency, issuer));
    let vault_key = protocol::vault_keylet(raw_account_id(owner), 11).key;
    let broker_key = protocol::loan_broker_keylet(raw_account_id(owner), 1).key;
    let loan_id = sample_uint256(0x95);
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(borrower, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        vault_entry(owner, vault_pseudo, 11, vault_asset),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let create = handle_real_dispatch(
        &mut view,
        &loan_broker_set_tx(owner, vault_key, 1),
        TxType::LOAN_BROKER_SET,
        Some(1_000_000),
    );
    assert_eq!(create, protocol::Ter::TES_SUCCESS);

    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_key))
        .expect("broker read should succeed")
        .expect("broker should exist");
    let broker_pseudo = broker.get_account_id(get_field_by_symbol("sfAccount"));

    let broker_page = ledger::dir_insert(
        &mut view,
        &owner_dir_keylet(raw_account_id(broker_pseudo)),
        loan_id,
        &|_| {},
    )
    .expect("broker dir insert should succeed")
    .expect("broker dir page should exist");
    let borrower_page = ledger::dir_insert(
        &mut view,
        &owner_dir_keylet(raw_account_id(borrower)),
        loan_id,
        &|_| {},
    )
    .expect("borrower dir insert should succeed")
    .expect("borrower dir page should exist");

    let borrower_root = view
        .read(account_keylet(raw_account_id(borrower)))
        .expect("borrower read should succeed")
        .expect("borrower should exist");
    let _ = ledger::adjust_owner_count(&mut view, &borrower_root, 1);

    let mut broker_obj = broker.clone_as_object();
    broker_obj.set_field_u32(get_field_by_symbol("sfOwnerCount"), 1);
    let _ = view.update(Arc::new(STLedgerEntry::from_stobject(
        broker_obj,
        *broker.key(),
    )));

    let _ = view.insert(Arc::new(loan_entry(
        loan_id,
        borrower,
        broker_key,
        broker_page,
        borrower_page,
    )));

    let delete = handle_real_dispatch(
        &mut view,
        &loan_delete_tx(owner, loan_id),
        TxType::LOAN_DELETE,
        None,
    );
    assert_eq!(delete, protocol::Ter::TES_SUCCESS);
    assert!(
        view.read(protocol::loan_keylet_from_key(loan_id))
            .expect("loan read should succeed")
            .is_none()
    );

    let borrower_root = view
        .read(account_keylet(raw_account_id(borrower)))
        .expect("borrower read should succeed")
        .expect("borrower should exist");
    assert_eq!(
        borrower_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        0
    );

    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_key))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(broker.get_field_u32(get_field_by_symbol("sfOwnerCount")), 0);
    assert!(
        view.read(account_keylet(raw_account_id(broker_pseudo)))
            .expect("pseudo read should succeed")
            .is_some()
    );
    assert!(
        view.read(line(issuer, broker_pseudo, currency))
            .expect("trust line read should succeed")
            .is_some()
    );
}

#[test]
fn loan_delete_rejects_missing_active_and_unauthorized_loan() {
    let owner = sample_account(0xA0);
    let borrower = sample_account(0xA1);
    let other = sample_account(0xA2);
    let issuer = sample_account(0xA3);
    let vault_pseudo = sample_account(0xA4);
    let broker_pseudo = sample_account(0xA5);
    let currency = Currency::from_array([0xA6; 20]);
    let asset = Asset::Issue(Issue::new(currency, issuer));
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 41).key;
    let broker_id = sample_uint256(0xA7);
    let loan_id = sample_uint256(0xA8);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(borrower, 1, 0),
        account_root(other, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        managed_vault_entry(owner, vault_pseudo, 41, asset, 0, 0, 0),
        loan_broker_entry(broker_id, owner, broker_pseudo, vault_id, asset, 0, 0, 0, 0),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_delete_tx(owner, sample_uint256(0xB0)),
            TxType::LOAN_DELETE,
            None,
        ),
        protocol::Ter::TEC_NO_ENTRY
    );

    let mut active = loan_entry(loan_id, borrower, broker_id, 0, 0);
    active.set_field_u32(sf("sfPaymentRemaining"), 1);
    view.insert(Arc::new(active)).expect("insert active loan");
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_delete_tx(owner, loan_id),
            TxType::LOAN_DELETE,
            None,
        ),
        protocol::Ter::TEC_HAS_OBLIGATIONS
    );

    let mut paid = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan should exist")
        .clone_as_object();
    paid.set_field_u32(sf("sfPaymentRemaining"), 0);
    view.update(Arc::new(STLedgerEntry::from_stobject(
        paid,
        protocol::loan_keylet_from_key(loan_id).key,
    )))
    .expect("update paid loan");
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_delete_tx(other, loan_id),
            TxType::LOAN_DELETE,
            None,
        ),
        protocol::Ter::TEC_NO_PERMISSION
    );
}

#[test]
fn loan_broker_cover_deposit_rejects_zero_after_cover_scale_rounding() {
    let owner = sample_account(0x8A);
    let issuer = sample_account(0x8B);
    let vault_pseudo = sample_account(0x8C);
    let broker_pseudo = sample_account(0x8D);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 10).key;
    let broker_id = sample_uint256(0x8E);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        managed_vault_entry(owner, vault_pseudo, 10, asset, 10, 10, 0),
        loan_broker_entry(broker_id, owner, broker_pseudo, vault_id, asset, 0, 1, 0, 0),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(1_000_000_000_000_000, -96).expect("dust cover amount"),
        issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_deposit_tx(owner, broker_id, amount),
        TxType::LOAN_BROKER_COVER_DEPOSIT,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_PRECISION_LOSS);
    assert!(
        view.read(line(owner, broker_pseudo, currency))
            .expect("trust line read should succeed")
            .is_none()
    );
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(1)
    );
}

#[test]
fn loan_broker_cover_deposit_waives_iou_transfer_rate() {
    let owner = sample_account(0x8A);
    let issuer = sample_account(0x8B);
    let vault_pseudo = sample_account(0x8C);
    let broker_pseudo = sample_account(0x8D);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 13).key;
    let broker_id = sample_uint256(0x8F);
    let mut issuer_root = account_root(issuer, 2, lsfDefaultRipple);
    issuer_root.set_field_u32(get_field_by_symbol("sfTransferRate"), 2_000_000_000);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 1, 0),
        issuer_root,
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 1, 0),
        trust_line_entry(owner, issuer, currency, 100),
        trust_line_entry(issuer, broker_pseudo, currency, 0),
        managed_vault_entry(owner, vault_pseudo, 13, asset, 10, 10, 0),
        loan_broker_entry(broker_id, owner, broker_pseudo, vault_id, asset, 0, 0, 0, 0),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = iou_amount(get_field_by_symbol("sfAmount"), issue, 10);

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_deposit_tx(owner, broker_id, amount),
        TxType::LOAN_BROKER_COVER_DEPOSIT,
        None,
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let owner_line = view
        .read(line(owner, issuer, currency))
        .expect("owner line read should succeed")
        .expect("owner line should remain");
    assert_eq!(
        owner_line
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .iou(),
        IOUAmount::from_parts(90, 0).expect("owner post-deposit balance")
    );
    let broker_line = view
        .read(line(issuer, broker_pseudo, currency))
        .expect("broker line read should succeed")
        .expect("broker line should remain");
    assert_eq!(
        broker_line
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .iou(),
        IOUAmount::from_parts(-10, 0).expect("broker post-deposit balance")
    );
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(10)
    );
}

#[test]
fn loan_broker_cover_deposit_rejects_insufficient_iou_balance() {
    let owner = sample_account(0xBA);
    let issuer = sample_account(0xBB);
    let vault_pseudo = sample_account(0xBC);
    let broker_pseudo = sample_account(0xBD);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 28).key;
    let broker_id = sample_uint256(0xBE);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 1, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        trust_line_entry(owner, issuer, currency, 5),
        managed_vault_entry(owner, vault_pseudo, 28, asset, 10, 10, 0),
        loan_broker_entry(broker_id, owner, broker_pseudo, vault_id, asset, 0, 0, 0, 0),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(10, 0).expect("deposit amount"),
        issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_deposit_tx(owner, broker_id, amount),
        TxType::LOAN_BROKER_COVER_DEPOSIT,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_INSUFFICIENT_FUNDS);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::zero()
    );
    assert!(
        view.read(line(issuer, broker_pseudo, currency))
            .expect("broker pseudo line read should succeed")
            .is_none()
    );
}

#[test]
fn loan_broker_cover_deposit_requires_strong_iou_auth() {
    let owner = sample_account(0xBF);
    let issuer = sample_account(0xC0);
    let vault_pseudo = sample_account(0xC1);
    let broker_pseudo = sample_account(0xC2);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 29).key;
    let broker_id = sample_uint256(0xC3);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 1, 0),
        account_root(issuer, 0, protocol::lsfRequireAuth | lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        trust_line_entry(owner, issuer, currency, 100),
        managed_vault_entry(owner, vault_pseudo, 29, asset, 10, 10, 0),
        loan_broker_entry(broker_id, owner, broker_pseudo, vault_id, asset, 0, 0, 0, 0),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(10, 0).expect("deposit amount"),
        issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_deposit_tx(owner, broker_id, amount),
        TxType::LOAN_BROKER_COVER_DEPOSIT,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_NO_AUTH);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::zero()
    );
}

#[test]
fn loan_broker_cover_withdraw_rejects_zero_at_cover_scale() {
    let owner = sample_account(0x93);
    let issuer = sample_account(0x94);
    let vault_pseudo = sample_account(0x95);
    let broker_pseudo = sample_account(0x96);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 12).key;
    let broker_id = sample_uint256(0x97);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        managed_vault_entry(owner, vault_pseudo, 12, asset, 10, 10, 0),
        loan_broker_entry(
            broker_id,
            owner,
            broker_pseudo,
            vault_id,
            asset,
            0,
            10,
            0,
            0,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(1_000_000_000_000_000, -96).expect("dust cover amount"),
        issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_withdraw_tx(owner, broker_id, amount),
        TxType::LOAN_BROKER_COVER_WITHDRAW,
        Some(0),
    );

    assert_eq!(result, protocol::Ter::TEC_PRECISION_LOSS);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(10)
    );
}

#[test]
fn loan_broker_cover_withdraw_allows_nontransferable_mpt_recovery_after_cleanup_3_2_0() {
    let owner = sample_account(0xC1);
    let issuer = sample_account(0xC2);
    let vault_pseudo = sample_account(0xC3);
    let broker_pseudo = sample_account(0xC4);
    let mpt_id = share_id_for(issuer, 9);
    let issue = MPTIssue::new(mpt_id);
    let asset = Asset::MPTIssue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 24).key;
    let broker_id = sample_uint256(0xC5);
    let amount = STAmount::from_mpt_amount(
        get_field_by_symbol("sfAmount"),
        MPTAmount::from_value(5),
        issue,
    );

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, 0),
        account_root(vault_pseudo, 1, 0),
        account_root_with_balance(broker_pseudo, 1, 0, 0),
        managed_vault_entry(owner, vault_pseudo, 24, asset, 0, 0, 0),
        loan_broker_entry(broker_id, owner, broker_pseudo, vault_id, asset, 0, 5, 0, 0),
        mpt_issuance_entry(issuer, 9, 5, MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG),
        mptoken_entry(broker_pseudo, mpt_id, 5),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_withdraw_tx(owner, broker_id, amount),
        TxType::LOAN_BROKER_COVER_WITHDRAW,
        Some(0),
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let owner_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(owner),
        ))
        .expect("owner token read should succeed")
        .expect("owner token should be created");
    assert_eq!(
        owner_token.get_field_u64(get_field_by_symbol("sfMPTAmount")),
        5
    );
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::zero()
    );
}

#[test]
fn loan_broker_cover_withdraw_requires_strong_mpt_auth_for_third_party_destination() {
    let owner = sample_account(0xD1);
    let issuer = sample_account(0xD2);
    let destination = sample_account(0xD3);
    let vault_pseudo = sample_account(0xD4);
    let broker_pseudo = sample_account(0xD5);
    let mpt_id = share_id_for(issuer, 14);
    let issue = MPTIssue::new(mpt_id);
    let asset = Asset::MPTIssue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 27).key;
    let broker_id = sample_uint256(0xD6);
    let amount = STAmount::from_mpt_amount(
        get_field_by_symbol("sfAmount"),
        MPTAmount::from_value(5),
        issue,
    );

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, 0),
        account_root(destination, 0, 0),
        account_root(vault_pseudo, 1, 0),
        account_root_with_balance(broker_pseudo, 1, 0, 0),
        managed_vault_entry(owner, vault_pseudo, 27, asset, 0, 0, 0),
        loan_broker_entry(broker_id, owner, broker_pseudo, vault_id, asset, 0, 5, 0, 0),
        mpt_issuance_entry(
            issuer,
            14,
            5,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
        mptoken_entry(broker_pseudo, mpt_id, 5),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_withdraw_to_tx(owner, destination, broker_id, amount),
        TxType::LOAN_BROKER_COVER_WITHDRAW,
        Some(0),
    );

    assert_eq!(result, protocol::Ter::TEC_NO_AUTH);
    assert!(
        view.read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(destination),
        ))
        .expect("destination token read should succeed")
        .is_none()
    );
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(5)
    );
}

#[test]
fn loan_broker_cover_withdraw_rejects_insufficient_pseudo_iou_balance_before_mutation() {
    let owner = sample_account(0xC4);
    let issuer = sample_account(0xC5);
    let vault_pseudo = sample_account(0xC6);
    let broker_pseudo = sample_account(0xC7);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 30).key;
    let broker_id = sample_uint256(0xC8);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 1, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 1, 0),
        trust_line_entry_iou(
            issuer,
            broker_pseudo,
            currency,
            IOUAmount::from_parts(-5, 0).expect("broker cover balance"),
        ),
        managed_vault_entry(owner, vault_pseudo, 30, asset, 10, 10, 0),
        loan_broker_entry(
            broker_id,
            owner,
            broker_pseudo,
            vault_id,
            asset,
            0,
            10,
            0,
            0,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(10, 0).expect("withdraw amount"),
        issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_withdraw_tx(owner, broker_id, amount),
        TxType::LOAN_BROKER_COVER_WITHDRAW,
        Some(1_000_000),
    );

    assert_eq!(result, protocol::Ter::TEC_INSUFFICIENT_FUNDS);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(10)
    );
}

#[test]
fn loan_broker_cover_withdraw_requires_strong_iou_auth_for_third_party_destination() {
    let owner = sample_account(0xC9);
    let issuer = sample_account(0xCA);
    let destination = sample_account(0xCB);
    let vault_pseudo = sample_account(0xCC);
    let broker_pseudo = sample_account(0xCD);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 31).key;
    let broker_id = sample_uint256(0xCE);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 1, 0),
        account_root(issuer, 0, protocol::lsfRequireAuth | lsfDefaultRipple),
        account_root(destination, 1, 0),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 1, 0),
        trust_line_entry_iou(
            issuer,
            broker_pseudo,
            currency,
            IOUAmount::from_parts(-10, 0).expect("broker cover balance"),
        ),
        trust_line_entry(destination, issuer, currency, 0),
        managed_vault_entry(owner, vault_pseudo, 31, asset, 10, 10, 0),
        loan_broker_entry(
            broker_id,
            owner,
            broker_pseudo,
            vault_id,
            asset,
            0,
            10,
            0,
            0,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(5, 0).expect("withdraw amount"),
        issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_withdraw_to_tx(owner, destination, broker_id, amount),
        TxType::LOAN_BROKER_COVER_WITHDRAW,
        Some(1_000_000),
    );

    assert_eq!(result, protocol::Ter::TEC_NO_AUTH);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(10)
    );
}

#[test]
fn loan_broker_cover_clawback_rejects_zero_at_cover_scale() {
    let owner = sample_account(0x98);
    let issuer = sample_account(0x99);
    let vault_pseudo = sample_account(0x9A);
    let broker_pseudo = sample_account(0x9B);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 13).key;
    let broker_id = sample_uint256(0x9C);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        managed_vault_entry(owner, vault_pseudo, 13, asset, 10, 10, 0),
        loan_broker_entry(
            broker_id,
            owner,
            broker_pseudo,
            vault_id,
            asset,
            0,
            10,
            0,
            0,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(1_000_000_000_000_000, -96).expect("dust cover amount"),
        issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_clawback_tx(issuer, broker_id, amount),
        TxType::LOAN_BROKER_COVER_CLAWBACK,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_PRECISION_LOSS);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(10)
    );
}

#[test]
fn loan_broker_cover_clawback_caps_to_minimum_cover() {
    let owner = sample_account(0xA0);
    let issuer = sample_account(0xA1);
    let vault_pseudo = sample_account(0xA2);
    let broker_pseudo = sample_account(0xA3);
    let mpt_id = protocol::make_mpt_id(1, issuer);
    let issue = MPTIssue::new(mpt_id);
    let asset = Asset::MPTIssue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 14).key;
    let broker_id = sample_uint256(0xA4);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        managed_vault_entry(owner, vault_pseudo, 14, asset, 1_000, 1_000, 0),
        loan_broker_entry(
            broker_id,
            owner,
            broker_pseudo,
            vault_id,
            asset,
            1_000,
            150,
            10_000,
            0,
        ),
        mpt_issuance_entry(issuer, 1, 150, protocol::lsfMPTCanClawback),
        mptoken_entry(broker_pseudo, mpt_id, 150),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_mpt_amount(
        get_field_by_symbol("sfAmount"),
        MPTAmount::from_value(100),
        issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_clawback_tx(issuer, broker_id, amount),
        TxType::LOAN_BROKER_COVER_CLAWBACK,
        None,
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(100)
    );
}

#[test]
fn loan_broker_cover_clawback_derives_broker_from_iou_pseudo_holder() {
    let owner = sample_account(0xA5);
    let issuer = sample_account(0xA6);
    let vault_pseudo = sample_account(0xA7);
    let broker_pseudo = sample_account(0xA8);
    let currency = currency_from_string("USD");
    let vault_issue = Issue::new(currency, issuer);
    let holder_issue = Issue::new(currency, broker_pseudo);
    let asset = Asset::Issue(vault_issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 15).key;
    let broker_id = sample_uint256(0xA9);
    let mut broker_pseudo_root = account_root(broker_pseudo, 0, 0);
    broker_pseudo_root.set_field_h256(get_field_by_symbol("sfLoanBrokerID"), broker_id);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, protocol::lsfAllowTrustLineClawback),
        account_root(vault_pseudo, 0, 0),
        broker_pseudo_root,
        trust_line_entry(issuer, broker_pseudo, currency, -10),
        managed_vault_entry(owner, vault_pseudo, 15, asset, 1_000, 1_000, 0),
        loan_broker_entry(
            broker_id,
            owner,
            broker_pseudo,
            vault_id,
            asset,
            1_000,
            10,
            0,
            0,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(4, 0).expect("clawback amount"),
        holder_issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_clawback_without_id_tx(issuer, amount),
        TxType::LOAN_BROKER_COVER_CLAWBACK,
        None,
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(6)
    );
}

#[test]
fn loan_broker_cover_clawback_without_id_requires_pseudo_holder() {
    let owner = sample_account(0xAA);
    let issuer = sample_account(0xAB);
    let vault_pseudo = sample_account(0xAC);
    let not_pseudo = sample_account(0xAD);
    let currency = currency_from_string("USD");
    let asset = Asset::Issue(Issue::new(currency, issuer));
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 16).key;
    let broker_id = sample_uint256(0xAE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(1, 0).expect("clawback amount"),
        Issue::new(currency, not_pseudo),
    );

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, protocol::lsfAllowTrustLineClawback),
        account_root(vault_pseudo, 0, 0),
        account_root(not_pseudo, 0, 0),
        managed_vault_entry(owner, vault_pseudo, 16, asset, 1_000, 1_000, 0),
        loan_broker_entry(
            broker_id,
            owner,
            sample_account(0xAF),
            vault_id,
            asset,
            1_000,
            10,
            0,
            0,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_clawback_without_id_tx(issuer, amount),
        TxType::LOAN_BROKER_COVER_CLAWBACK,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_OBJECT_NOT_FOUND);
}

#[test]
fn loan_broker_cover_clawback_requires_iou_clawback_permission() {
    let owner = sample_account(0xB0);
    let issuer = sample_account(0xB1);
    let vault_pseudo = sample_account(0xB2);
    let broker_pseudo = sample_account(0xB3);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 17).key;
    let broker_id = sample_uint256(0xB4);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, 0),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        trust_line_entry(issuer, broker_pseudo, currency, -10),
        managed_vault_entry(owner, vault_pseudo, 17, asset, 1_000, 1_000, 0),
        loan_broker_entry(
            broker_id,
            owner,
            broker_pseudo,
            vault_id,
            asset,
            1_000,
            10,
            0,
            0,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(4, 0).expect("clawback amount"),
        issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_clawback_tx(issuer, broker_id, amount),
        TxType::LOAN_BROKER_COVER_CLAWBACK,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_NO_PERMISSION);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(10)
    );
}

#[test]
fn loan_broker_cover_clawback_rejects_cover_above_pseudo_iou_balance() {
    let owner = sample_account(0xBA);
    let issuer = sample_account(0xBB);
    let vault_pseudo = sample_account(0xBC);
    let broker_pseudo = sample_account(0xBD);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 19).key;
    let broker_id = sample_uint256(0xBE);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, protocol::lsfAllowTrustLineClawback),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        trust_line_entry(issuer, broker_pseudo, currency, -3),
        managed_vault_entry(owner, vault_pseudo, 19, asset, 1_000, 1_000, 0),
        loan_broker_entry(
            broker_id,
            owner,
            broker_pseudo,
            vault_id,
            asset,
            1_000,
            10,
            0,
            0,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        sf("sfAmount"),
        IOUAmount::from_parts(4, 0).expect("clawback amount"),
        issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_clawback_tx(issuer, broker_id, amount),
        TxType::LOAN_BROKER_COVER_CLAWBACK,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_INTERNAL);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker.get_field_number(sf("sfCoverAvailable")).value(),
        RuntimeNumber::from_i64(10)
    );
}

#[test]
fn loan_broker_cover_clawback_requires_mpt_can_clawback() {
    let owner = sample_account(0xB5);
    let issuer = sample_account(0xB6);
    let vault_pseudo = sample_account(0xB7);
    let broker_pseudo = sample_account(0xB8);
    let mpt_id = protocol::make_mpt_id(1, issuer);
    let issue = MPTIssue::new(mpt_id);
    let asset = Asset::MPTIssue(issue);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 18).key;
    let broker_id = sample_uint256(0xB9);

    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(vault_pseudo, 0, 0),
        account_root(broker_pseudo, 0, 0),
        managed_vault_entry(owner, vault_pseudo, 18, asset, 1_000, 1_000, 0),
        loan_broker_entry(
            broker_id,
            owner,
            broker_pseudo,
            vault_id,
            asset,
            1_000,
            150,
            0,
            0,
        ),
        mpt_issuance_entry(issuer, 1, 150, 0),
        mptoken_entry(broker_pseudo, mpt_id, 150),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_mpt_amount(
        get_field_by_symbol("sfAmount"),
        MPTAmount::from_value(25),
        issue,
    );

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_clawback_tx(issuer, broker_id, amount),
        TxType::LOAN_BROKER_COVER_CLAWBACK,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_NO_PERMISSION);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(150)
    );
}

#[test]
fn loan_broker_cover_withdraw_preserves_minimum_cover() {
    let owner = sample_account(0x8F);
    let vault_pseudo = sample_account(0x90);
    let broker_pseudo = sample_account(0x91);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 11).key;
    let broker_id = sample_uint256(0x92);

    let mut ledger = empty_ledger(vec![
        account_root_with_balance(owner, 0, 0, 1_000),
        account_root_with_balance(vault_pseudo, 0, 0, 0),
        account_root_with_balance(broker_pseudo, 0, 0, 100),
        managed_vault_entry(owner, vault_pseudo, 11, asset, 1_000, 1_000, 0),
        loan_broker_entry(
            broker_id,
            owner,
            broker_pseudo,
            vault_id,
            asset,
            1_000,
            100,
            10_000,
            0,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_broker_cover_withdraw_tx(
            owner,
            broker_id,
            STAmount::from_xrp_amount(XRPAmount::from_drops(1)),
        ),
        TxType::LOAN_BROKER_COVER_WITHDRAW,
        Some(1_000),
    );

    assert_eq!(result, protocol::Ter::TEC_INSUFFICIENT_FUNDS);
    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::from_i64(100)
    );
    let owner_root = view
        .read(account_keylet(raw_account_id(owner)))
        .expect("owner read should succeed")
        .expect("owner should exist");
    assert_eq!(
        owner_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000
    );
}

#[test]
fn loan_set_dispatch_creates_loan_and_updates_vault_and_broker() {
    let owner = sample_account(0x96);
    let borrower = sample_account(0x97);
    let vault_pseudo = sample_account(0x98);
    let broker_pseudo = sample_account(0x99);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 13).key;
    let broker_id = sample_uint256(0x9A);
    let ledger = ledger_with_header(
        LedgerHeader {
            seq: 1,
            parent_close_time: 500,
            ..LedgerHeader::default()
        },
        vec![
            account_root(owner, 0, 0),
            account_root_with_balance(borrower, 0, 0, 200_000_000),
            account_root_with_balance(vault_pseudo, 0, 0, 200_000_000),
            account_root_with_balance(broker_pseudo, 0, 0, 200_000_000),
            managed_vault_entry(owner, vault_pseudo, 13, asset, 200_000_000, 200_000_000, 0),
            loan_broker_entry(
                broker_id,
                owner,
                broker_pseudo,
                vault_id,
                asset,
                0,
                200_000_000,
                10_000,
                10_000,
            ),
        ],
    );
    let mut ledger = ledger;
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let mut loan_set = loan_set_tx(borrower, broker_id, 10_000_000, 1);
    loan_set.set_account_id(get_field_by_symbol("sfCounterparty"), owner);
    loan_set.make_field_absent(get_field_by_symbol("sfInterestRate"));
    loan_set.set_field_u32(get_field_by_symbol("sfGracePeriod"), 60);
    let result = handle_real_dispatch(&mut view, &loan_set, TxType::LOAN_SET, Some(1_000_000));
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let loan = view
        .read(protocol::loan_keylet(broker_id, 1))
        .expect("loan read should succeed")
        .expect("loan should exist");
    assert_eq!(
        loan.get_account_id(get_field_by_symbol("sfBorrower")),
        borrower
    );
    assert_eq!(
        loan.get_field_number(get_field_by_symbol("sfPrincipalOutstanding"))
            .value(),
        RuntimeNumber::from_i64(10_000_000)
    );
    assert_eq!(
        loan.get_field_u32(get_field_by_symbol("sfPaymentRemaining")),
        1
    );

    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsAvailable"))
            .value(),
        RuntimeNumber::from_i64(190_000_000)
    );

    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker.get_field_u32(get_field_by_symbol("sfLoanSequence")),
        2
    );
    assert_eq!(broker.get_field_u32(get_field_by_symbol("sfOwnerCount")), 1);

    let borrower_root = view
        .read(account_keylet(raw_account_id(borrower)))
        .expect("borrower read should succeed")
        .expect("borrower should exist");
    assert_eq!(
        borrower_root.get_field_u32(get_field_by_symbol("sfOwnerCount")),
        1
    );
}

#[test]
fn loan_set_dispatch_links_borrower_and_broker_pseudo_owner_dirs() {
    let owner = sample_account(0x9B);
    let borrower = sample_account(0x9C);
    let vault_pseudo = sample_account(0x9D);
    let broker_pseudo = sample_account(0x9E);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 14).key;
    let broker_id = sample_uint256(0x9F);
    let ledger = ledger_with_header(
        LedgerHeader {
            seq: 1,
            parent_close_time: 500,
            ..LedgerHeader::default()
        },
        vec![
            account_root(owner, 0, 0),
            account_root_with_balance(borrower, 0, 0, 1_000_000),
            account_root_with_balance(vault_pseudo, 0, 0, 10_000),
            account_root_with_balance(broker_pseudo, 0, 0, 10_000),
            managed_vault_entry(owner, vault_pseudo, 14, asset, 10_000, 10_000, 0),
            loan_broker_entry(
                broker_id,
                owner,
                broker_pseudo,
                vault_id,
                asset,
                0,
                10_000,
                100_000,
                100_000,
            ),
        ],
    );
    let mut ledger = ledger;
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_set_tx(borrower, broker_id, 1_000, 1),
        TxType::LOAN_SET,
        Some(1_000_000),
    );
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let loan_key = protocol::loan_keylet(broker_id, 1).key;
    let loan = view
        .read(protocol::loan_keylet_from_key(loan_key))
        .expect("loan read should succeed")
        .expect("loan should exist");
    assert_eq!(
        loan.get_field_u64(get_field_by_symbol("sfLoanBrokerNode")),
        0
    );
    assert_eq!(loan.get_field_u64(get_field_by_symbol("sfOwnerNode")), 0);

    let broker_dir = view
        .read(owner_dir_keylet(raw_account_id(broker_pseudo)))
        .expect("broker dir read should succeed")
        .expect("broker dir should exist");
    assert_eq!(
        broker_dir.get_account_id(get_field_by_symbol("sfOwner")),
        broker_pseudo
    );
    assert!(
        broker_dir
            .get_field_v256(get_field_by_symbol("sfIndexes"))
            .value()
            .contains(&loan_key)
    );

    let borrower_dir = view
        .read(owner_dir_keylet(raw_account_id(borrower)))
        .expect("borrower dir read should succeed")
        .expect("borrower dir should exist");
    assert_eq!(
        borrower_dir.get_account_id(get_field_by_symbol("sfOwner")),
        borrower
    );
    assert!(
        borrower_dir
            .get_field_v256(get_field_by_symbol("sfIndexes"))
            .value()
            .contains(&loan_key)
    );
}

#[test]
fn loan_set_dispatch_with_origination_fee_pays_owner_and_updates_debt_total() {
    let owner = sample_account(0xA0);
    let borrower = sample_account(0xA7);
    let vault_pseudo = sample_account(0xA8);
    let broker_pseudo = sample_account(0xA9);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 15).key;
    let broker_id = sample_uint256(0xAA);
    let ledger = ledger_with_header(
        LedgerHeader {
            seq: 1,
            parent_close_time: 500,
            ..LedgerHeader::default()
        },
        vec![
            account_root_with_balance(owner, 0, 0, 1_000),
            account_root_with_balance(borrower, 0, 0, 1_000_000),
            account_root_with_balance(vault_pseudo, 0, 0, 10_000),
            account_root_with_balance(broker_pseudo, 0, 0, 10_000),
            managed_vault_entry(owner, vault_pseudo, 15, asset, 10_000, 10_000, 0),
            loan_broker_entry(
                broker_id,
                owner,
                broker_pseudo,
                vault_id,
                asset,
                0,
                10_000,
                100_000,
                100_000,
            ),
        ],
    );
    let mut ledger = ledger;
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_set_tx_with_origination_fee(borrower, broker_id, 1_000, 25, 1),
        TxType::LOAN_SET,
        Some(1_000_000),
    );
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let owner_root = view
        .read(account_keylet(raw_account_id(owner)))
        .expect("owner read should succeed")
        .expect("owner should exist");
    assert_eq!(
        owner_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_025
    );

    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfDebtTotal"))
            .value(),
        RuntimeNumber::from_i64(1_000)
    );
    assert_eq!(
        broker.get_field_u32(get_field_by_symbol("sfLoanSequence")),
        2
    );
}

#[test]
fn loan_manage_default_updates_vault_broker_loan_and_moves_cover() {
    let owner = sample_account(0xA1);
    let borrower = sample_account(0xA2);
    let vault_pseudo = sample_account(0xA3);
    let broker_pseudo = sample_account(0xA4);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 17).key;
    let broker_id = sample_uint256(0xA5);
    let loan_id = sample_uint256(0xA6);
    let ledger = ledger_with_header(
        LedgerHeader {
            seq: 1,
            parent_close_time: 50,
            ..LedgerHeader::default()
        },
        vec![
            account_root(owner, 0, 0),
            account_root(borrower, 0, 0),
            account_root_with_balance(vault_pseudo, 0, 0, 100),
            account_root_with_balance(broker_pseudo, 0, 0, 100),
            managed_vault_entry(owner, vault_pseudo, 17, asset, 500, 100, 0),
            loan_broker_entry(
                broker_id,
                owner,
                broker_pseudo,
                vault_id,
                asset,
                100,
                20,
                100_000,
                100_000,
            ),
            managed_loan_entry(loan_id, borrower, broker_id, 60, 50, 10, 1, 10),
        ],
    );
    let mut ledger = ledger;
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_manage_tx(owner, loan_id, tfLoanDefault),
        TxType::LOAN_MANAGE,
        None,
    );
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsTotal"))
            .value(),
        RuntimeNumber::from_i64(470)
    );
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsAvailable"))
            .value(),
        RuntimeNumber::from_i64(120)
    );

    let broker = view
        .read(protocol::loan_broker_keylet_from_key(broker_id))
        .expect("broker read should succeed")
        .expect("broker should remain");
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfDebtTotal"))
            .value(),
        RuntimeNumber::from_i64(50)
    );
    assert_eq!(
        broker
            .get_field_number(get_field_by_symbol("sfCoverAvailable"))
            .value(),
        RuntimeNumber::zero()
    );

    let loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read should succeed")
        .expect("loan should remain");
    assert!(loan.is_flag(protocol::lsfLoanDefault));
    assert_eq!(
        loan.get_field_number(get_field_by_symbol("sfTotalValueOutstanding"))
            .value(),
        RuntimeNumber::zero()
    );
    assert_eq!(
        loan.get_field_u32(get_field_by_symbol("sfPaymentRemaining")),
        0
    );
    assert_eq!(
        loan.get_field_u32(get_field_by_symbol("sfNextPaymentDueDate")),
        0
    );

    let vault_pseudo_root = view
        .read(account_keylet(raw_account_id(vault_pseudo)))
        .expect("vault pseudo read should succeed")
        .expect("vault pseudo should exist");
    let broker_pseudo_root = view
        .read(account_keylet(raw_account_id(broker_pseudo)))
        .expect("broker pseudo read should succeed")
        .expect("broker pseudo should exist");
    assert_eq!(
        vault_pseudo_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        120
    );
    assert_eq!(
        broker_pseudo_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        80
    );
}

#[test]
fn loan_manage_and_pay_reject_missing_loan_with_no_entry() {
    let account = sample_account(0xB5);
    let issuer = sample_account(0xB6);
    let loan_id = sample_uint256(0xB7);
    let amount = STAmount::from_iou_amount(
        sf("sfAmount"),
        IOUAmount::from_parts(1, 0).expect("amount"),
        Issue::new(Currency::from_array([0xB8; 20]), issuer),
    );
    let mut ledger = empty_ledger(vec![
        account_root(account, 0, 0),
        account_root(issuer, 0, 0),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("LendingProtocol"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &loan_manage_tx(account, loan_id, protocol::tfLoanImpair),
            TxType::LOAN_MANAGE,
            None,
        ),
        protocol::Ter::TEC_NO_ENTRY
    );

    let pay = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_h256(sf("sfLoanID"), loan_id);
        tx.set_field_amount(sf("sfAmount"), amount);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });
    assert_eq!(
        handle_real_dispatch(&mut view, &pay, TxType::LOAN_PAY, None),
        protocol::Ter::TEC_NO_ENTRY
    );
}

#[test]
fn loan_manage_impair_updates_vault_loss_and_due_date() {
    let owner = sample_account(0xB1);
    let borrower = sample_account(0xB2);
    let vault_pseudo = sample_account(0xB3);
    let broker_pseudo = sample_account(0xB4);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 19).key;
    let broker_id = sample_uint256(0xB5);
    let loan_id = sample_uint256(0xB6);
    let mut ledger = ledger_with_header(
        LedgerHeader {
            seq: 1,
            parent_close_time: 200,
            ..LedgerHeader::default()
        },
        vec![
            account_root(owner, 0, 0),
            account_root(borrower, 0, 0),
            account_root(vault_pseudo, 0, 0),
            account_root(broker_pseudo, 0, 0),
            managed_vault_entry(owner, vault_pseudo, 19, asset, 500, 300, 10),
            loan_broker_entry(
                broker_id,
                owner,
                broker_pseudo,
                vault_id,
                asset,
                100,
                0,
                100_000,
                100_000,
            ),
            managed_loan_entry(loan_id, borrower, broker_id, 125, 100, 25, 1, 250),
        ],
    );
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_manage_tx(owner, loan_id, tfLoanImpair),
        TxType::LOAN_MANAGE,
        None,
    );
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfLossUnrealized"))
            .value(),
        RuntimeNumber::from_i64(110)
    );

    let loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read should succeed")
        .expect("loan should remain");
    assert!(loan.is_flag(lsfLoanImpaired));
    assert_eq!(
        loan.get_field_u32(get_field_by_symbol("sfNextPaymentDueDate")),
        200
    );
}

#[test]
fn loan_manage_unimpair_reverses_loss_and_restores_due_date() {
    let owner = sample_account(0xC1);
    let borrower = sample_account(0xC2);
    let vault_pseudo = sample_account(0xC3);
    let broker_pseudo = sample_account(0xC4);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 23).key;
    let broker_id = sample_uint256(0xC5);
    let loan_id = sample_uint256(0xC6);
    let mut loan = managed_loan_entry(loan_id, borrower, broker_id, 125, 100, 25, 1, 250);
    loan.set_flag(lsfLoanImpaired);
    let mut ledger = ledger_with_header(
        LedgerHeader {
            seq: 1,
            parent_close_time: 200,
            ..LedgerHeader::default()
        },
        vec![
            account_root(owner, 0, 0),
            account_root(borrower, 0, 0),
            account_root(vault_pseudo, 0, 0),
            account_root(broker_pseudo, 0, 0),
            managed_vault_entry(owner, vault_pseudo, 23, asset, 500, 300, 150),
            loan_broker_entry(
                broker_id,
                owner,
                broker_pseudo,
                vault_id,
                asset,
                100,
                0,
                100_000,
                100_000,
            ),
            loan,
        ],
    );
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &loan_manage_tx(owner, loan_id, tfLoanUnimpair),
        TxType::LOAN_MANAGE,
        None,
    );
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfLossUnrealized"))
            .value(),
        RuntimeNumber::from_i64(50)
    );

    let loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read should succeed")
        .expect("loan should remain");
    assert!(!loan.is_flag(lsfLoanImpaired));
    assert_eq!(
        loan.get_field_u32(get_field_by_symbol("sfNextPaymentDueDate")),
        230
    );
}

#[test]
fn vault_create_dispatch_creates_vault_pseudo_and_share_issuance() {
    let owner = sample_account(0xD1);
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_create_tx(owner, Asset::Issue(xrp_issue()), 1),
        TxType::VAULT_CREATE,
        None,
    );
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let vault = view
        .read(protocol::vault_keylet(raw_account_id(owner), 1))
        .expect("vault read should succeed")
        .expect("vault should exist");
    let pseudo = vault.get_account_id(get_field_by_symbol("sfAccount"));
    let share_id = vault.get_field_h192(get_field_by_symbol("sfShareMPTID"));

    let pseudo_root = view
        .read(account_keylet(raw_account_id(pseudo)))
        .expect("pseudo read should succeed")
        .expect("pseudo should exist");
    assert_eq!(
        pseudo_root.get_field_h256(get_field_by_symbol("sfVaultID")),
        *vault.key()
    );
    assert!(!pseudo_root.is_field_present(get_field_by_symbol("sfRegularKey")));
    assert!(
        view.read(protocol::mpt_issuance_keylet_from_mptid(share_id))
            .expect("issuance read should succeed")
            .is_some()
    );
}

#[test]
fn vault_create_dispatch_requires_mptokens_v1_before_apply() {
    let owner = sample_account(0xB1);
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = dispatch_with_pre_fee_balance(
        &mut view,
        &vault_create_tx(owner, Asset::Issue(xrp_issue()), 1),
        TxType::VAULT_CREATE,
    );

    assert_eq!(result, protocol::Ter::TEM_DISABLED);
    assert!(
        view.read(protocol::vault_keylet(raw_account_id(owner), 1))
            .expect("vault read should succeed")
            .is_none()
    );
}

#[test]
fn vault_create_sets_share_asset_scale_and_reference_holding_for_iou_after_cleanup_3_2_0() {
    let owner = sample_account(0xC1);
    let issuer = sample_account(0xC2);
    let currency = currency_from_string("USD");
    let asset = Asset::Issue(Issue::new(currency, issuer));
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_create_tx_with_scale(owner, asset, 1, Some(8)),
        TxType::VAULT_CREATE,
        None,
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let vault = view
        .read(protocol::vault_keylet(raw_account_id(owner), 1))
        .expect("vault read should succeed")
        .expect("vault should exist");
    let pseudo = vault.get_account_id(get_field_by_symbol("sfAccount"));
    let share = view
        .read(protocol::mpt_issuance_keylet_from_mptid(
            vault.get_field_h192(get_field_by_symbol("sfShareMPTID")),
        ))
        .expect("share issuance read should succeed")
        .expect("share issuance should exist");

    assert_eq!(share.get_field_u8(get_field_by_symbol("sfAssetScale")), 8);
    assert_eq!(vault.get_field_u8(get_field_by_symbol("sfScale")), 8);
    assert_eq!(
        share.get_field_h256(get_field_by_symbol("sfReferenceHolding")),
        line(pseudo, issuer, currency).key
    );
    assert!(
        view.read(line(pseudo, issuer, currency))
            .expect("reference holding read should succeed")
            .is_some()
    );
}

#[test]
fn vault_create_persists_default_iou_scale_when_omitted() {
    let owner = sample_account(0xC6);
    let issuer = sample_account(0xC7);
    let currency = currency_from_string("USD");
    let asset = Asset::Issue(Issue::new(currency, issuer));
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_create_issue_tx(owner, asset, 1),
        TxType::VAULT_CREATE,
        None,
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let vault = view
        .read(protocol::vault_keylet(raw_account_id(owner), 1))
        .expect("vault read should succeed")
        .expect("vault should exist");
    assert_eq!(
        vault.get_field_u8(get_field_by_symbol("sfScale")),
        protocol::VAULT_DEFAULT_IOU_SCALE
    );
    let share = view
        .read(protocol::mpt_issuance_keylet_from_mptid(
            vault.get_field_h192(get_field_by_symbol("sfShareMPTID")),
        ))
        .expect("share issuance read should succeed")
        .expect("share issuance should exist");
    assert_eq!(
        share.get_field_u8(get_field_by_symbol("sfAssetScale")),
        protocol::VAULT_DEFAULT_IOU_SCALE
    );
}

#[test]
fn vault_create_sets_share_reference_holding_for_mpt_after_cleanup_3_2_0() {
    let owner = sample_account(0xC3);
    let issuer = sample_account(0xC4);
    let underlying_id = share_id_for(issuer, 1);
    let asset = Asset::MPTIssue(MPTIssue::new(underlying_id));
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, 0),
        mpt_issuance_entry(issuer, 1, 0, protocol::lsfMPTCanTransfer),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = dispatch_with_pre_fee_balance(
        &mut view,
        &vault_create_tx(owner, asset, 1),
        TxType::VAULT_CREATE,
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let vault = view
        .read(protocol::vault_keylet(raw_account_id(owner), 1))
        .expect("vault read should succeed")
        .expect("vault should exist");
    assert_eq!(
        vault
            .get_field_issue(get_field_by_symbol("sfAsset"))
            .asset(),
        asset
    );
    let pseudo = vault.get_account_id(get_field_by_symbol("sfAccount"));
    let expected_holding =
        protocol::mptoken_keylet_from_mptid(underlying_id, raw_account_id(pseudo));
    let share = view
        .read(protocol::mpt_issuance_keylet_from_mptid(
            vault.get_field_h192(get_field_by_symbol("sfShareMPTID")),
        ))
        .expect("share issuance read should succeed")
        .expect("share issuance should exist");

    assert_eq!(share.get_field_u8(get_field_by_symbol("sfAssetScale")), 0);
    assert_eq!(
        share.get_field_h256(get_field_by_symbol("sfReferenceHolding")),
        expected_holding.key
    );
    assert!(
        view.read(expected_holding)
            .expect("reference holding read should succeed")
            .is_some()
    );
}

#[test]
fn vault_create_leaves_reference_holding_absent_for_xrp_and_pre_cleanup() {
    let xrp_owner = sample_account(0xC5);
    let mut xrp_ledger = empty_ledger(vec![account_root(xrp_owner, 0, 0)]);
    xrp_ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut xrp_view = ApplyViewImpl::new(Arc::new(xrp_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut xrp_view,
            &vault_create_tx(xrp_owner, Asset::Issue(xrp_issue()), 1),
            TxType::VAULT_CREATE,
            None,
        ),
        protocol::Ter::TES_SUCCESS
    );
    let xrp_vault = xrp_view
        .read(protocol::vault_keylet(raw_account_id(xrp_owner), 1))
        .expect("xrp vault read should succeed")
        .expect("xrp vault should exist");
    let xrp_share = xrp_view
        .read(protocol::mpt_issuance_keylet_from_mptid(
            xrp_vault.get_field_h192(get_field_by_symbol("sfShareMPTID")),
        ))
        .expect("xrp share read should succeed")
        .expect("xrp share should exist");
    assert_eq!(
        xrp_share.get_field_u8(get_field_by_symbol("sfAssetScale")),
        0
    );
    assert!(!xrp_share.is_field_present(get_field_by_symbol("sfReferenceHolding")));

    let owner = sample_account(0xC6);
    let issuer = sample_account(0xC7);
    let currency = currency_from_string("EUR");
    let asset = Asset::Issue(Issue::new(currency, issuer));
    let mut legacy_ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
    ]);
    legacy_ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut legacy_view = ApplyViewImpl::new(Arc::new(legacy_ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut legacy_view,
            &vault_create_tx_with_scale(owner, asset, 1, Some(4)),
            TxType::VAULT_CREATE,
            None,
        ),
        protocol::Ter::TES_SUCCESS
    );
    let legacy_vault = legacy_view
        .read(protocol::vault_keylet(raw_account_id(owner), 1))
        .expect("legacy vault read should succeed")
        .expect("legacy vault should exist");
    let legacy_share = legacy_view
        .read(protocol::mpt_issuance_keylet_from_mptid(
            legacy_vault.get_field_h192(get_field_by_symbol("sfShareMPTID")),
        ))
        .expect("legacy share read should succeed")
        .expect("legacy share should exist");
    assert_eq!(
        legacy_share.get_field_u8(get_field_by_symbol("sfAssetScale")),
        4
    );
    assert!(!legacy_share.is_field_present(get_field_by_symbol("sfReferenceHolding")));
}

#[test]
fn vault_set_dispatch_updates_assets_maximum() {
    let owner = sample_account(0xD2);
    let pseudo = sample_account(0xD3);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 7).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 7, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 50),
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(pseudo, 1, 0),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            0,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_set_tx(owner, vault_id, 250),
        TxType::VAULT_SET,
        None,
    );
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsMaximum"))
            .value(),
        RuntimeNumber::from_i64(250)
    );
}

#[test]
fn vault_set_dispatch_rejects_missing_vault_with_no_entry() {
    let owner = sample_account(0xE1);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 77).key;
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_set_tx(owner, vault_id, 250),
        TxType::VAULT_SET,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_NO_ENTRY);
}

#[test]
fn vault_set_dispatch_rejects_domain_without_permissioned_domains_before_lookup() {
    let owner = sample_account(0xB2);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 177).key;
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_set_domain_tx(owner, vault_id, sample_uint256(0xB3)),
        TxType::VAULT_SET,
        None,
    );

    assert_eq!(result, protocol::Ter::TEM_DISABLED);
}

#[test]
fn vault_set_dispatch_rejects_zero_vault_id_before_lookup() {
    let owner = sample_account(0xB4);
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("PermissionedDomains"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_set_tx(owner, sample_uint256(0x00), 250),
        TxType::VAULT_SET,
        None,
    );

    assert_eq!(result, protocol::Ter::TEM_MALFORMED);
}

#[test]
fn vault_set_dispatch_rejects_assets_maximum_below_total_before_mutation() {
    let owner = sample_account(0xE2);
    let pseudo = sample_account(0xE3);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 78).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 78, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 500),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsMaximum"),
        asset_number(asset, 1_000),
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(pseudo, 1, 0),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            0,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("PermissionedDomains"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_set_tx(owner, vault_id, 250),
        TxType::VAULT_SET,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_LIMIT_EXCEEDED);
    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsMaximum"))
            .value(),
        RuntimeNumber::from_i64(1_000)
    );
}

#[test]
fn vault_set_dispatch_rejects_domain_on_public_vault() {
    let owner = sample_account(0xE4);
    let pseudo = sample_account(0xE5);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 79).key;
    let domain = permissioned_domain_keylet(raw_account_id(owner), 1).key;
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(pseudo, 1, 0),
        vault_entry_with_share(owner, pseudo, 79, asset, share_id),
        mpt_issuance_entry(
            pseudo,
            1,
            0,
            MPT_CAN_ESCROW_FLAG
                | MPT_CAN_TRADE_FLAG
                | MPT_CAN_TRANSFER_FLAG
                | protocol::lsfMPTRequireAuth,
        ),
        permissioned_domain_entry(owner, 1, 0, &[]),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("PermissionedDomains"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_set_domain_tx(owner, vault_id, domain),
        TxType::VAULT_SET,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_NO_PERMISSION);
}

#[test]
fn vault_set_dispatch_rejects_missing_domain() {
    let owner = sample_account(0xE6);
    let pseudo = sample_account(0xE7);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 80).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 80, asset, share_id);
    vault.set_field_u32(get_field_by_symbol("sfFlags"), VAULT_PRIVATE_FLAG);
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(pseudo, 1, 0),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            0,
            MPT_CAN_ESCROW_FLAG
                | MPT_CAN_TRADE_FLAG
                | MPT_CAN_TRANSFER_FLAG
                | protocol::lsfMPTRequireAuth,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("PermissionedDomains"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_set_domain_tx(owner, vault_id, sample_uint256(0xDD)),
        TxType::VAULT_SET,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_OBJECT_NOT_FOUND);
}

#[test]
fn vault_delete_dispatch_removes_vault_and_share_issuance() {
    let owner = sample_account(0xD4);
    let pseudo = sample_account(0xD5);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 9).key;
    let ledger = {
        let vault = vault_entry_with_share(owner, pseudo, 9, asset, share_id);
        let owner_token = mptoken_entry(owner, share_id, 0);
        let mut pseudo_root = account_root_with_balance(pseudo, 1, 0, 0);
        pseudo_root.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        let mut owner_root = account_root(owner, 1, 0);
        owner_root.set_field_u32(get_field_by_symbol("sfOwnerCount"), 1);
        let mut ledger = empty_ledger(vec![
            owner_root,
            pseudo_root,
            vault,
            mpt_issuance_entry(
                pseudo,
                1,
                0,
                MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
            ),
            owner_token,
            owner_dir_root(
                owner,
                protocol::mptoken_keylet_from_mptid(share_id, raw_account_id(owner)).key,
            ),
            owner_dir_root(
                pseudo,
                protocol::mpt_issuance_keylet(1, raw_account_id(pseudo)).key,
            ),
        ]);
        ledger.set_rules(protocol::Rules::new([protocol::feature_id(
            "SingleAssetVault",
        )]));
        ledger
    };
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_delete_tx(owner, vault_id),
        TxType::VAULT_DELETE,
        None,
    );
    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    assert!(
        view.read(protocol::vault_keylet_from_key(vault_id))
            .expect("vault read should succeed")
            .is_none()
    );
    assert!(
        view.read(protocol::mpt_issuance_keylet_from_mptid(share_id))
            .expect("issuance read should succeed")
            .is_none()
    );
}

#[test]
fn vault_delete_dispatch_rejects_missing_vault_with_no_entry() {
    let owner = sample_account(0xE8);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 81).key;
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_delete_tx(owner, vault_id),
        TxType::VAULT_DELETE,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_NO_ENTRY);
}

#[test]
fn vault_delete_dispatch_rejects_zero_vault_id_before_lookup() {
    let owner = sample_account(0xB5);
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_delete_tx(owner, sample_uint256(0x00)),
        TxType::VAULT_DELETE,
        None,
    );

    assert_eq!(result, protocol::Ter::TEM_MALFORMED);
}

#[test]
fn vault_delete_dispatch_rejects_nonempty_vault_before_cleanup() {
    let owner = sample_account(0xE9);
    let pseudo = sample_account(0xEA);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 82).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 82, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 1),
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(pseudo, 1, 0),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            0,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_delete_tx(owner, vault_id),
        TxType::VAULT_DELETE,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_HAS_OBLIGATIONS);
    assert!(
        view.read(protocol::mpt_issuance_keylet_from_mptid(share_id))
            .expect("issuance read should succeed")
            .is_some()
    );
}

#[test]
fn vault_delete_dispatch_rejects_missing_share_issuance() {
    let owner = sample_account(0xEB);
    let pseudo = sample_account(0xEC);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 83).key;
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(pseudo, 1, 0),
        vault_entry_with_share(owner, pseudo, 83, asset, share_id),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_delete_tx(owner, vault_id),
        TxType::VAULT_DELETE,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_OBJECT_NOT_FOUND);
}

#[test]
fn vault_delete_dispatch_rejects_outstanding_shares_before_cleanup() {
    let owner = sample_account(0xED);
    let pseudo = sample_account(0xEE);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 84).key;
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(pseudo, 1, 0),
        vault_entry_with_share(owner, pseudo, 84, asset, share_id),
        mpt_issuance_entry(
            pseudo,
            1,
            5,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
        mptoken_entry(owner, share_id, 5),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_delete_tx(owner, vault_id),
        TxType::VAULT_DELETE,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_HAS_OBLIGATIONS);
    assert!(
        view.read(protocol::mptoken_keylet_from_mptid(
            share_id,
            raw_account_id(owner),
        ))
        .expect("owner token read should succeed")
        .is_some()
    );
}

#[test]
fn vault_deposit_dispatch_updates_vault_and_mints_shares() {
    let owner = sample_account(0xD6);
    let depositor = sample_account(0xD7);
    let pseudo = sample_account(0xD8);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 11).key;
    let ledger = {
        let vault = vault_entry_with_share(owner, pseudo, 11, asset, share_id);
        let mut ledger = empty_ledger(vec![
            account_root(owner, 0, 0),
            account_root_with_balance(depositor, 0, 0, 1_000),
            account_root(pseudo, 1, 0),
            vault,
            mpt_issuance_entry(
                pseudo,
                1,
                0,
                MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
            ),
        ]);
        ledger.set_rules(protocol::Rules::new([protocol::feature_id(
            "SingleAssetVault",
        )]));
        ledger
    };
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_deposit_tx(depositor, vault_id, 500),
        TxType::VAULT_DEPOSIT,
        None,
    );
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsTotal"))
            .value(),
        RuntimeNumber::from_i64(500)
    );
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsAvailable"))
            .value(),
        RuntimeNumber::from_i64(500)
    );
    let token = view
        .read(protocol::mptoken_keylet_from_mptid(
            share_id,
            raw_account_id(depositor),
        ))
        .expect("token read should succeed")
        .expect("depositor token should exist");
    assert_eq!(token.get_field_u64(get_field_by_symbol("sfMPTAmount")), 500);
}

#[test]
fn vault_deposit_dispatch_rejects_missing_vault_with_no_entry() {
    let depositor = sample_account(0xE9);
    let missing_vault = sample_uint256(0xEA);
    let ledger = {
        let mut ledger = empty_ledger(vec![account_root_with_balance(depositor, 0, 0, 1_000)]);
        ledger.set_rules(protocol::Rules::new([protocol::feature_id(
            "SingleAssetVault",
        )]));
        ledger
    };
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_deposit_tx(depositor, missing_vault, 500),
        TxType::VAULT_DEPOSIT,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_NO_ENTRY);
}

#[test]
fn vault_deposit_dispatch_rejects_zero_vault_id_before_lookup() {
    let depositor = sample_account(0xB6);
    let mut ledger = empty_ledger(vec![account_root_with_balance(depositor, 0, 0, 1_000)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_deposit_tx(depositor, sample_uint256(0x00), 500),
        TxType::VAULT_DEPOSIT,
        None,
    );

    assert_eq!(result, protocol::Ter::TEM_MALFORMED);
}

#[test]
fn vault_deposit_dispatch_rejects_nonpositive_amount_before_lookup() {
    let depositor = sample_account(0xB7);
    let mut ledger = empty_ledger(vec![account_root_with_balance(depositor, 0, 0, 1_000)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_deposit_tx(depositor, sample_uint256(0xB8), 0),
        TxType::VAULT_DEPOSIT,
        None,
    );

    assert_eq!(result, protocol::Ter::TEM_BAD_AMOUNT);
}

#[test]
fn vault_deposit_dispatch_rejects_assets_maximum_before_mutation() {
    let owner = sample_account(0xEB);
    let depositor = sample_account(0xEC);
    let pseudo = sample_account(0xED);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 33).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 33, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsMaximum"),
        asset_number(asset, 400),
    );
    let ledger = {
        let mut ledger = empty_ledger(vec![
            account_root(owner, 0, 0),
            account_root_with_balance(depositor, 0, 0, 1_000),
            account_root_with_balance(pseudo, 1, 0, 0),
            vault,
            mpt_issuance_entry(
                pseudo,
                1,
                0,
                MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
            ),
        ]);
        ledger.set_rules(protocol::Rules::new([protocol::feature_id(
            "SingleAssetVault",
        )]));
        ledger
    };
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_deposit_tx(depositor, vault_id, 500),
        TxType::VAULT_DEPOSIT,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_LIMIT_EXCEEDED);
    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsTotal"))
            .value(),
        RuntimeNumber::zero()
    );
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsAvailable"))
            .value(),
        RuntimeNumber::zero()
    );
    assert!(
        view.read(protocol::mptoken_keylet_from_mptid(
            share_id,
            raw_account_id(depositor),
        ))
        .expect("token read should succeed")
        .is_none()
    );
    let depositor_root = view
        .read(account_keylet(raw_account_id(depositor)))
        .expect("depositor read should succeed")
        .expect("depositor should remain");
    assert_eq!(
        depositor_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000
    );
    let pseudo_root = view
        .read(account_keylet(raw_account_id(pseudo)))
        .expect("pseudo read should succeed")
        .expect("pseudo should remain");
    assert_eq!(
        pseudo_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        0
    );
}

#[test]
fn vault_deposit_empty_iou_vault_mints_scale_adjusted_shares() {
    let gateway = sample_account(0xC8);
    let owner = sample_account(0xC9);
    let depositor = sample_account(0xCA);
    let pseudo = sample_account(0xCB);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, gateway);
    let asset = Asset::Issue(issue);
    let share_id = share_id_for(pseudo, 1);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 25).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 25, asset, share_id);
    vault.set_field_u8(
        get_field_by_symbol("sfScale"),
        protocol::VAULT_DEFAULT_IOU_SCALE,
    );
    let mut gateway_root = account_root(gateway, 1, lsfDefaultRipple);
    gateway_root.set_field_u32(get_field_by_symbol("sfTransferRate"), 2_000_000_000);
    let depositor_balance =
        IOUAmount::from_parts(-1_000, 0).expect("gateway owes depositor before deposit");
    let mut ledger = empty_ledger(vec![
        gateway_root,
        account_root(owner, 0, 0),
        account_root(depositor, 1, 0),
        account_root(pseudo, 1, 0),
        trust_line_entry_iou(gateway, depositor, currency, depositor_balance),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            0,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(500, 0).expect("deposit amount"),
        issue,
    );
    let tx = STTx::new(TxType::VAULT_DEPOSIT, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), depositor);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_amount(get_field_by_symbol("sfAmount"), amount);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });

    let result = dispatch_with_pre_fee_balance(&mut view, &tx, TxType::VAULT_DEPOSIT);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let share = view
        .read(protocol::mptoken_keylet_from_mptid(
            share_id,
            raw_account_id(depositor),
        ))
        .expect("share token read should succeed")
        .expect("depositor share token should exist");
    assert_eq!(
        share.get_field_u64(get_field_by_symbol("sfMPTAmount")),
        500 * 10_u64.pow(u32::from(protocol::VAULT_DEFAULT_IOU_SCALE))
    );
    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should exist");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsTotal"))
            .value(),
        RuntimeNumber::from_i64(500)
    );
    let depositor_line = view
        .read(line(gateway, depositor, currency))
        .expect("depositor line read should succeed")
        .expect("depositor line should remain");
    assert_eq!(
        depositor_line
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .iou(),
        IOUAmount::from_parts(-500, 0).expect("remaining depositor balance")
    );
}

#[test]
fn vault_deposit_dispatch_rejects_zero_shares_after_precision_rounding() {
    let owner = sample_account(0xE1);
    let depositor = sample_account(0xE2);
    let pseudo = sample_account(0xE3);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 17).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 17, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 1_000),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 1_000),
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root_with_balance(depositor, 0, 0, 100),
        account_root_with_balance(pseudo, 1, 0, 1_000),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            1,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_deposit_tx(depositor, vault_id, 1),
        TxType::VAULT_DEPOSIT,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_PRECISION_LOSS);
}

#[test]
fn vault_deposit_dispatch_rejects_zero_after_vault_scale_rounding() {
    let owner = sample_account(0xE4);
    let depositor = sample_account(0xE5);
    let pseudo = sample_account(0xE6);
    let issuer = sample_account(0xE7);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let share_id = share_id_for(pseudo, 1);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 18).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 18, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 10),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 10),
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(depositor, 0, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(pseudo, 1, 0),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            10,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let dust = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(1_000_000_000_000_000, -96).expect("dust vault amount"),
        issue,
    );
    let tx = STTx::new(TxType::VAULT_DEPOSIT, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), depositor);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_amount(get_field_by_symbol("sfAmount"), dust);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::VAULT_DEPOSIT, None);

    assert_eq!(result, protocol::Ter::TEC_PRECISION_LOSS);
    assert!(
        view.read(line(depositor, pseudo, currency))
            .expect("trust line read should succeed")
            .is_none()
    );
}

#[test]
fn vault_deposit_dispatch_rejects_zero_at_depositor_trustline_scale() {
    let owner = sample_account(0xF1);
    let depositor = sample_account(0xF2);
    let pseudo = sample_account(0xF3);
    let issuer = sample_account(0xF7);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let share_id = share_id_for(pseudo, 1);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 20).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 20, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number_parts(asset, 1_000_000_000_000_000, -30),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number_parts(asset, 1_000_000_000_000_000, -30),
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root(depositor, 1, 0),
        account_root(issuer, 0, lsfDefaultRipple),
        account_root(pseudo, 1, 0),
        trust_line_entry_iou(
            depositor,
            issuer,
            currency,
            IOUAmount::from_parts(1_000_000_000_000_000, -14).expect("depositor balance"),
        ),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            10,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(5_000_000_000_000_000, -30).expect("half ulp deposit"),
        issue,
    );
    let tx = STTx::new(TxType::VAULT_DEPOSIT, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), depositor);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_amount(get_field_by_symbol("sfAmount"), amount);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::VAULT_DEPOSIT, None);

    assert_eq!(result, protocol::Ter::TEC_PRECISION_LOSS);
    assert!(
        view.read(protocol::mptoken_keylet_from_mptid(
            share_id,
            raw_account_id(depositor),
        ))
        .expect("share token read should succeed")
        .is_none()
    );
}

#[test]
fn vault_deposit_dispatch_allows_full_balance_from_opposite_limit_after_cleanup_3_2_0() {
    let gateway = sample_account(0x21);
    let owner = sample_account(0x31);
    let depositor = sample_account(0x41);
    let pseudo = sample_account(0x51);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, gateway);
    let asset = Asset::Issue(issue);
    let share_id = share_id_for(pseudo, 1);
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 24).key;
    let vault = vault_entry_with_share(owner, pseudo, 24, asset, share_id);
    let depositor_balance =
        IOUAmount::from_parts(-100, 0).expect("gateway owes depositor 100 before deposit");
    let mut ledger = empty_ledger(vec![
        account_root(gateway, 1, lsfDefaultRipple),
        account_root(owner, 0, 0),
        account_root(depositor, 1, 0),
        account_root(pseudo, 1, 0),
        trust_line_entry_iou(gateway, depositor, currency, depositor_balance),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            0,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let amount = STAmount::from_iou_amount(
        get_field_by_symbol("sfAmount"),
        IOUAmount::from_parts(500, 0).expect("deposit amount"),
        issue,
    );
    let tx = STTx::new(TxType::VAULT_DEPOSIT, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), depositor);
        object.set_field_h256(get_field_by_symbol("sfVaultID"), vault_id);
        object.set_field_amount(get_field_by_symbol("sfAmount"), amount);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::VAULT_DEPOSIT, None);

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let share = view
        .read(protocol::mptoken_keylet_from_mptid(
            share_id,
            raw_account_id(depositor),
        ))
        .expect("share token read should succeed")
        .expect("depositor share token should exist");
    assert_eq!(share.get_field_u64(get_field_by_symbol("sfMPTAmount")), 500);
    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should exist");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsTotal"))
            .value(),
        RuntimeNumber::from_i64(500)
    );
}

#[test]
fn vault_withdraw_dispatch_redeems_shares_and_pays_account() {
    let owner = sample_account(0xD9);
    let holder = sample_account(0xDA);
    let pseudo = sample_account(0xDB);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 13).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 13, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 500),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 500),
    );
    let ledger = {
        let mut ledger = empty_ledger(vec![
            account_root(owner, 0, 0),
            account_root_with_balance(holder, 0, 0, 100),
            account_root_with_balance(pseudo, 1, 0, 500),
            vault,
            mpt_issuance_entry(
                pseudo,
                1,
                500,
                MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
            ),
            mptoken_entry(holder, share_id, 500),
        ]);
        ledger.set_rules(protocol::Rules::new([protocol::feature_id(
            "SingleAssetVault",
        )]));
        ledger
    };
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_withdraw_share_tx(holder, vault_id, share_id, 200),
        TxType::VAULT_WITHDRAW,
        None,
    );
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let holder_root = view
        .read(account_keylet(raw_account_id(holder)))
        .expect("holder read should succeed")
        .expect("holder should remain");
    assert_eq!(
        holder_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        300
    );
    let token = view
        .read(protocol::mptoken_keylet_from_mptid(
            share_id,
            raw_account_id(holder),
        ))
        .expect("token read should succeed")
        .expect("holder token should remain");
    assert_eq!(token.get_field_u64(get_field_by_symbol("sfMPTAmount")), 300);
}

#[test]
fn vault_withdraw_dispatch_rejects_missing_vault_with_no_entry() {
    let holder = sample_account(0xEE);
    let missing_vault = sample_uint256(0xEF);
    let ledger = {
        let mut ledger = empty_ledger(vec![account_root_with_balance(holder, 0, 0, 1_000)]);
        ledger.set_rules(protocol::Rules::new([protocol::feature_id(
            "SingleAssetVault",
        )]));
        ledger
    };
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_withdraw_asset_tx(holder, missing_vault, 500),
        TxType::VAULT_WITHDRAW,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_NO_ENTRY);
}

#[test]
fn vault_withdraw_dispatch_rejects_zero_vault_id_before_lookup() {
    let holder = sample_account(0xB9);
    let mut ledger = empty_ledger(vec![account_root_with_balance(holder, 0, 0, 1_000)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_withdraw_asset_tx(holder, sample_uint256(0x00), 500),
        TxType::VAULT_WITHDRAW,
        None,
    );

    assert_eq!(result, protocol::Ter::TEM_MALFORMED);
}

#[test]
fn vault_withdraw_dispatch_rejects_nonpositive_amount_before_lookup() {
    let holder = sample_account(0xBA);
    let mut ledger = empty_ledger(vec![account_root_with_balance(holder, 0, 0, 1_000)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_withdraw_asset_tx(holder, sample_uint256(0xBB), 0),
        TxType::VAULT_WITHDRAW,
        None,
    );

    assert_eq!(result, protocol::Ter::TEM_BAD_AMOUNT);
}

#[test]
fn vault_withdraw_dispatch_rejects_zero_destination_before_lookup() {
    let holder = sample_account(0xBC);
    let mut tx = vault_withdraw_asset_tx(holder, sample_uint256(0xBD), 500);
    tx.set_account_id(
        get_field_by_symbol("sfDestination"),
        AccountID::from_array([0; 20]),
    );
    let mut ledger = empty_ledger(vec![account_root_with_balance(holder, 0, 0, 1_000)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(&mut view, &tx, TxType::VAULT_WITHDRAW, None);

    assert_eq!(result, protocol::Ter::TEM_MALFORMED);
}

#[test]
fn vault_withdraw_dispatch_rejects_zero_shares_after_precision_rounding() {
    let owner = sample_account(0xE4);
    let holder = sample_account(0xE5);
    let pseudo = sample_account(0xE6);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 19).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 19, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 1_000),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 1_000),
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root_with_balance(holder, 0, 0, 100),
        account_root_with_balance(pseudo, 1, 0, 1_000),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            1,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
        mptoken_entry(holder, share_id, 1),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_withdraw_asset_tx(holder, vault_id, 1),
        TxType::VAULT_WITHDRAW,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_PRECISION_LOSS);
}

#[test]
fn vault_withdraw_sole_shareholder_keeps_future_value_shares_after_loss() {
    let owner = sample_account(0xA7);
    let holder = sample_account(0xA8);
    let pseudo = sample_account(0xA9);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 21).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 21, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 1_000),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 700),
    );
    vault.set_field_number(
        get_field_by_symbol("sfLossUnrealized"),
        asset_number(asset, 300),
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root_with_balance(holder, 1, 0, 100),
        account_root_with_balance(pseudo, 1, 0, 700),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            1_000,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
        mptoken_entry(holder, share_id, 1_000),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_withdraw_asset_tx(holder, vault_id, 700),
        TxType::VAULT_WITHDRAW,
        None,
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let token = view
        .read(protocol::mptoken_keylet_from_mptid(
            share_id,
            raw_account_id(holder),
        ))
        .expect("token read should succeed")
        .expect("holder should retain future-value shares");
    assert_eq!(token.get_field_u64(get_field_by_symbol("sfMPTAmount")), 300);

    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(share_id))
        .expect("issuance read should succeed")
        .expect("share issuance should remain");
    assert_eq!(
        issuance.get_field_u64(get_field_by_symbol("sfOutstandingAmount")),
        300
    );

    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsTotal"))
            .value(),
        RuntimeNumber::from_i64(300)
    );
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsAvailable"))
            .value(),
        RuntimeNumber::zero()
    );
}

#[test]
fn vault_withdraw_sole_shareholder_full_shares_with_loss_is_insufficient() {
    let owner = sample_account(0xB7);
    let holder = sample_account(0xB8);
    let pseudo = sample_account(0xB9);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 22).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 22, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 1_000),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 700),
    );
    vault.set_field_number(
        get_field_by_symbol("sfLossUnrealized"),
        asset_number(asset, 300),
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root_with_balance(holder, 1, 0, 100),
        account_root_with_balance(pseudo, 1, 0, 700),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            1_000,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
        mptoken_entry(holder, share_id, 1_000),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_withdraw_share_tx(holder, vault_id, share_id, 1_000),
        TxType::VAULT_WITHDRAW,
        None,
    );

    assert_eq!(result, protocol::Ter::TEC_INSUFFICIENT_FUNDS);
    let token = view
        .read(protocol::mptoken_keylet_from_mptid(
            share_id,
            raw_account_id(holder),
        ))
        .expect("token read should succeed")
        .expect("holder token should remain");
    assert_eq!(
        token.get_field_u64(get_field_by_symbol("sfMPTAmount")),
        1_000
    );
}

#[test]
fn vault_withdraw_sole_shareholder_clean_full_exit_zeroes_vault() {
    let owner = sample_account(0xBA);
    let holder = sample_account(0xBB);
    let pseudo = sample_account(0xBC);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 23).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 23, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 700),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 700),
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root_with_balance(holder, 1, 0, 100),
        account_root_with_balance(pseudo, 1, 0, 700),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            700,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
        mptoken_entry(holder, share_id, 700),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_withdraw_share_tx(holder, vault_id, share_id, 700),
        TxType::VAULT_WITHDRAW,
        None,
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsTotal"))
            .value(),
        RuntimeNumber::zero()
    );
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsAvailable"))
            .value(),
        RuntimeNumber::zero()
    );
}

#[test]
fn vault_withdraw_sole_shareholder_clean_full_asset_exit_zeroes_vault() {
    let owner = sample_account(0xFA);
    let holder = sample_account(0xFB);
    let pseudo = sample_account(0xFC);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 29).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 29, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 700),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 700),
    );
    let mut ledger = empty_ledger(vec![
        account_root(owner, 0, 0),
        account_root_with_balance(holder, 1, 0, 100),
        account_root_with_balance(pseudo, 1, 0, 700),
        vault,
        mpt_issuance_entry(
            pseudo,
            1,
            700,
            MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
        ),
        mptoken_entry(holder, share_id, 700),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_withdraw_asset_tx(holder, vault_id, 700),
        TxType::VAULT_WITHDRAW,
        None,
    );

    assert_eq!(result, protocol::Ter::TES_SUCCESS);
    let holder = view
        .read(account_keylet(raw_account_id(holder)))
        .expect("holder read should succeed")
        .expect("holder should remain");
    assert_eq!(
        holder
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        800
    );
    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsTotal"))
            .value(),
        RuntimeNumber::zero()
    );
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsAvailable"))
            .value(),
        RuntimeNumber::zero()
    );
}

#[test]
fn vault_clawback_dispatch_burns_holder_shares() {
    let owner = sample_account(0xDC);
    let holder = sample_account(0xDD);
    let pseudo = sample_account(0xDE);
    let share_id = share_id_for(pseudo, 1);
    let asset = Asset::Issue(xrp_issue());
    let vault_id = protocol::vault_keylet(raw_account_id(owner), 15).key;
    let mut vault = vault_entry_with_share(owner, pseudo, 15, asset, share_id);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 500),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 500),
    );
    let ledger = {
        let mut ledger = empty_ledger(vec![
            account_root(owner, 0, 0),
            account_root(holder, 1, 0),
            account_root_with_balance(pseudo, 1, 0, 500),
            vault,
            mpt_issuance_entry(
                pseudo,
                1,
                500,
                MPT_CAN_ESCROW_FLAG | MPT_CAN_TRADE_FLAG | MPT_CAN_TRANSFER_FLAG,
            ),
            mptoken_entry(holder, share_id, 500),
        ]);
        ledger.set_rules(protocol::Rules::new([protocol::feature_id(
            "SingleAssetVault",
        )]));
        ledger
    };
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_clawback_share_tx(owner, holder, vault_id, share_id),
        TxType::VAULT_CLAWBACK,
        None,
    );
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    assert!(
        view.read(protocol::mptoken_keylet_from_mptid(
            share_id,
            raw_account_id(holder)
        ))
        .expect("token read should succeed")
        .is_none()
    );
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(share_id))
        .expect("issuance read should succeed")
        .expect("issuance should remain");
    assert_eq!(
        issuance.get_field_u64(get_field_by_symbol("sfOutstandingAmount")),
        0
    );
}

#[test]
fn vault_clawback_dispatch_rejects_zero_vault_id_before_lookup() {
    let owner = sample_account(0xBE);
    let holder = sample_account(0xBF);
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0), account_root(holder, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_clawback_asset_tx(owner, holder, sample_uint256(0x00), 500),
        TxType::VAULT_CLAWBACK,
        None,
    );

    assert_eq!(result, protocol::Ter::TEM_MALFORMED);
}

#[test]
fn vault_clawback_dispatch_rejects_negative_amount_before_lookup() {
    let owner = sample_account(0xC0);
    let holder = sample_account(0xC1);
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0), account_root(holder, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_clawback_asset_tx(owner, holder, sample_uint256(0xC2), -1),
        TxType::VAULT_CLAWBACK,
        None,
    );

    assert_eq!(result, protocol::Ter::TEM_BAD_AMOUNT);
}

#[test]
fn vault_clawback_dispatch_rejects_xrp_amount_before_lookup() {
    let owner = sample_account(0xC3);
    let holder = sample_account(0xC4);
    let mut ledger = empty_ledger(vec![account_root(owner, 0, 0), account_root(holder, 0, 0)]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id(
        "SingleAssetVault",
    )]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let result = handle_real_dispatch(
        &mut view,
        &vault_clawback_asset_tx(owner, holder, sample_uint256(0xC5), 500),
        TxType::VAULT_CLAWBACK,
        None,
    );

    assert_eq!(result, protocol::Ter::TEM_MALFORMED);
}

#[test]
fn loan_pay_dispatch_reduces_outstanding_balance() {
    let borrower = sample_account(0xE1);
    let broker_owner = sample_account(0xE2);
    let broker_pseudo = sample_account(0xE3);
    let vault_pseudo = sample_account(0xE4);
    let loan_id = sample_uint256(0xF1);
    let broker_id = sample_uint256(0xF2);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let loan = managed_loan_entry(
        loan_id,
        borrower,
        broker_id,
        500_000_000,
        500_000_000,
        0,
        10,
        120,
    );

    let broker = loan_broker_entry(
        broker_id,
        broker_owner,
        broker_pseudo,
        vault_id,
        asset,
        500_000_000,
        0,
        0,
        0,
    );

    let mut vault = vault_entry(broker_owner, vault_pseudo, 1, asset);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 0),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 500_000_000),
    );

    let mut ledger = empty_ledger(vec![
        account_root_with_balance(borrower, 0, 0, 1_000_000_000),
        account_root_with_balance(vault_pseudo, 0, 0, 0),
        account_root_with_balance(broker_pseudo, 0, 0, 0),
        loan,
        broker,
        vault,
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));

    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(100_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    // Verify outstanding reduced on the real loan fields.
    let updated_loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan should still exist");
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfPrincipalOutstanding"))
            .value(),
        RuntimeNumber::from_i64(400_000_000)
    );
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfTotalValueOutstanding"))
            .value(),
        RuntimeNumber::from_i64(400_000_000)
    );

    // Verify payments remaining decremented
    assert_eq!(
        updated_loan.get_field_u32(get_field_by_symbol("sfPaymentRemaining")),
        9
    );
}

#[test]
fn loan_pay_dispatch_rejects_zero_vault_credit_after_rounding_before_transfer() {
    let borrower = sample_account(0xD1);
    let broker_owner = sample_account(0xD2);
    let broker_pseudo = sample_account(0xD3);
    let vault_pseudo = sample_account(0xD4);
    let issuer = sample_account(0xD5);
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);
    let loan_id = sample_uint256(0xD6);
    let broker_id = sample_uint256(0xD7);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;

    let mut loan = loan_entry(loan_id, borrower, broker_id, 0, 0);
    loan.set_field_i32(get_field_by_symbol("sfLoanScale"), 0);
    loan.set_field_number(
        get_field_by_symbol("sfTotalValueOutstanding"),
        asset_number(asset, 1),
    );
    loan.set_field_number(
        get_field_by_symbol("sfPrincipalOutstanding"),
        asset_number(asset, 1),
    );
    loan.set_field_number(
        get_field_by_symbol("sfManagementFeeOutstanding"),
        asset_number(asset, 0),
    );
    loan.set_field_number(
        get_field_by_symbol("sfPeriodicPayment"),
        asset_number(asset, 1),
    );
    loan.set_field_u32(get_field_by_symbol("sfPaymentRemaining"), 1);
    loan.set_field_u32(get_field_by_symbol("sfNextPaymentDueDate"), 120);

    let broker = loan_broker_entry(
        broker_id,
        broker_owner,
        broker_pseudo,
        vault_id,
        asset,
        1,
        0,
        0,
        0,
    );

    let mut vault = vault_entry(broker_owner, vault_pseudo, 1, asset);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 0),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number_parts(asset, 1, 30),
    );

    let mut ledger = empty_ledger(vec![
        account_root_with_balance(borrower, 0, 0, 1_000_000_000),
        account_root_with_balance(vault_pseudo, 0, 0, 0),
        account_root_with_balance(broker_pseudo, 0, 0, 0),
        account_root(issuer, 0, 0),
        loan,
        broker,
        vault,
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_iou_amount(
                get_field_by_symbol("sfAmount"),
                IOUAmount::from_parts(1, 0).expect("amount"),
                issue,
            ),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);

    assert_eq!(result, protocol::Ter::TEC_PRECISION_LOSS);
    assert!(
        view.read(line(borrower, vault_pseudo, currency))
            .expect("trust line read should succeed")
            .is_none()
    );
    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read should succeed")
        .expect("vault should remain");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsAvailable"))
            .value(),
        RuntimeNumber::zero()
    );
}

#[test]
fn amm_vote_dispatch_updates_vote_slots_and_weighted_fee() {
    let voter = sample_account(0x11);
    let existing_lp = sample_account(0x12);
    let amm_account = sample_account(0x22);
    let usd_issuer = sample_account(0x31);
    let eur_issuer = sample_account(0x32);
    let usd = Issue::new(currency_from_string("USD"), usd_issuer);
    let eur = Issue::new(currency_from_string("EUR"), eur_issuer);
    let lpt_currency = amm_lpt_currency(usd.currency, eur.currency);

    let amm = amm_entry(
        amm_account,
        usd,
        eur,
        1_000,
        vec![amm_vote_entry(existing_lp, 20, 40_000)],
        2,
    );
    let mut ledger = empty_ledger(vec![
        account_root(amm_account, 0, 0),
        account_root(voter, 0, 0),
        account_root(existing_lp, 0, 0),
        amm,
        trust_line_entry(voter, amm_account, lpt_currency, 600),
        trust_line_entry(existing_lp, amm_account, lpt_currency, 400),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("AMM")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::AMM_VOTE, |tx| {
        tx.set_account_id(sf("sfAccount"), voter);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(usd)),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(eur)),
        );
        tx.set_field_u16(sf("sfTradingFee"), 50);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_VOTE, None);
    assert_eq!(result, Ter::TES_SUCCESS);

    let amm_entry = view
        .read(protocol::keylet::amm(Asset::Issue(usd), Asset::Issue(eur)))
        .expect("amm read")
        .expect("amm should remain");
    assert_eq!(amm_entry.get_field_u16(sf("sfTradingFee")), 38);
    let votes = amm_entry.get_field_array(sf("sfVoteSlots"));
    assert_eq!(votes.len(), 2);
    let new_vote = votes
        .iter()
        .find(|entry| entry.get_account_id(sf("sfAccount")) == voter)
        .expect("new vote should be present");
    assert_eq!(new_vote.get_field_u16(sf("sfTradingFee")), 50);
    assert_eq!(new_vote.get_field_u32(sf("sfVoteWeight")), 60_000);
    let existing_vote = votes
        .iter()
        .find(|entry| entry.get_account_id(sf("sfAccount")) == existing_lp)
        .expect("existing vote should remain");
    assert_eq!(existing_vote.get_field_u16(sf("sfTradingFee")), 20);
    assert_eq!(existing_vote.get_field_u32(sf("sfVoteWeight")), 40_000);
    let auction_slot = amm_entry.get_field_object(sf("sfAuctionSlot"));
    assert_eq!(auction_slot.get_field_u16(sf("sfDiscountedFee")), 3);
}

#[test]
fn amm_deposit_clears_stale_auth_accounts_after_empty_pool_reinit() {
    let depositor = sample_account(0x11);
    let stale_auth = sample_account(0x12);
    let amm_account = sample_account(0x22);
    let usd_issuer = sample_account(0x31);
    let eur_issuer = sample_account(0x32);
    let usd = Issue::new(currency_from_string("USD"), usd_issuer);
    let eur = Issue::new(currency_from_string("EUR"), eur_issuer);

    let mut amm = amm_entry(amm_account, usd, eur, 0, vec![], 2);
    amm.set_field_amount(sf("sfAmount"), iou_amount(sf("sfAmount"), usd, 0));

    let mut auction_slot = amm.get_field_object(sf("sfAuctionSlot"));
    let mut auth_accounts = STArray::new(sf("sfAuthAccounts"));
    let mut auth_account = STObject::make_inner_object(sf("sfAuthAccount"));
    auth_account.set_account_id(sf("sfAccount"), stale_auth);
    auth_accounts.push_back(auth_account);
    auction_slot.set_field_array(sf("sfAuthAccounts"), auth_accounts);
    amm.set_field_object(sf("sfAuctionSlot"), auction_slot);

    let mut ledger = empty_ledger(vec![
        account_root(depositor, 0, 0),
        account_root(usd_issuer, 0, 0),
        account_root(eur_issuer, 0, 0),
        account_root(amm_account, 0, 0),
        amm,
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("AMM"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::AMM_DEPOSIT, |tx| {
        tx.set_account_id(sf("sfAccount"), depositor);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(usd)),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(eur)),
        );
        tx.set_field_amount(sf("sfAmount"), iou_amount(sf("sfAmount"), usd, 100));
        tx.set_field_amount(sf("sfAmount2"), iou_amount(sf("sfAmount2"), eur, 100));
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfFlags"), 0x0080_0000);
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_DEPOSIT, None);
    assert_eq!(result, Ter::TES_SUCCESS);

    let updated = view
        .read(protocol::keylet::amm(Asset::Issue(usd), Asset::Issue(eur)))
        .expect("amm read")
        .expect("amm should remain");
    let updated_slot = updated.get_field_object(sf("sfAuctionSlot"));
    assert!(!updated_slot.is_field_present(sf("sfAuthAccounts")));
    assert_eq!(updated_slot.get_account_id(sf("sfAccount")), depositor);
    assert_eq!(
        updated_slot.get_field_u32(sf("sfExpiration")),
        view.header()
            .parent_close_time
            .saturating_add(protocol::TOTAL_TIME_SLOT_SECS)
    );
    assert_eq!(updated_slot.get_field_amount(sf("sfPrice")).signum(), 0);
    assert!(!updated_slot.is_field_present(sf("sfDiscountedFee")));
    assert!(!updated.is_field_present(sf("sfTradingFee")));
    let votes = updated.get_field_array(sf("sfVoteSlots"));
    assert_eq!(votes.len(), 1);
    let vote = votes.iter().next().expect("one vote slot");
    assert_eq!(vote.get_account_id(sf("sfAccount")), depositor);
    assert_eq!(
        vote.get_field_u32(sf("sfVoteWeight")),
        protocol::VOTE_WEIGHT_SCALE_FACTOR
    );
    assert!(!vote.is_field_present(sf("sfTradingFee")));
}

#[test]
fn amm_deposit_submit_shell_preserves_pool_invariant() {
    let depositor = sample_account(0x41);
    let amm_account = sample_account(0x42);
    let usd_issuer = sample_account(0x51);
    let eur_issuer = sample_account(0x52);
    let usd = Issue::new(currency_from_string("USD"), usd_issuer);
    let eur = Issue::new(currency_from_string("EUR"), eur_issuer);

    let mut ledger = empty_ledger(vec![
        account_root_with_balance(depositor, 0, 0, 1_000_000_000),
        account_root(usd_issuer, 0, 0),
        account_root(eur_issuer, 0, 0),
        account_root(amm_account, 0, 0),
        amm_entry(amm_account, usd, eur, 1_000, vec![], 0),
        trust_line_entry(amm_account, usd_issuer, usd.currency, 1_000),
        trust_line_entry(amm_account, eur_issuer, eur.currency, 1_000),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("AMM"),
        protocol::fix_ammv1_3(),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::AMM_DEPOSIT, |tx| {
        tx.set_account_id(sf("sfAccount"), depositor);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(usd)),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(eur)),
        );
        tx.set_field_amount(sf("sfAmount"), iou_amount(sf("sfAmount"), usd, 100));
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfFlags"), 0x0008_0000);
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = apply_submit_transactor_shell(&mut view, &tx, TxType::AMM_DEPOSIT);

    assert_eq!(result, Ter::TES_SUCCESS);
}

#[test]
fn amm_create_rejects_locked_mpt_asset_before_creating_pool() {
    let account = sample_account(0x13);
    let issuer = sample_account(0x14);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_amount = STAmount::from_mpt_amount(
        sf("sfAmount"),
        protocol::MPTAmount::from_value(25),
        mpt_issue,
    );
    let xrp_amount = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade | protocol::lsfMPTLocked,
        ),
        mptoken_entry(account, mpt_id, 50),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_CREATE, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_amount(sf("sfAmount"), mpt_amount);
        tx.set_field_amount(sf("sfAmount2"), xrp_amount);
        tx.set_field_u16(sf("sfTradingFee"), 50);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = tx::run_dex_read_view_preclaim(&view, &tx, TxType::AMM_CREATE)
        .expect("AMMCreate must have a typed preclaim");

    assert_eq!(result, Ter::TEC_LOCKED);
}

#[test]
fn amm_create_rejects_non_holder_of_requested_iou() {
    let account = sample_account(0x35);
    let issuer = sample_account(0x36);
    let currency = currency_from_string("TST");
    let issue = Issue::new(currency, issuer);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000_000),
        account_root(issuer, 0, lsfDefaultRipple),
        trust_line_entry(account, issuer, currency, 0),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("AMM")]));
    let view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_CREATE, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_amount(
            sf("sfAmount"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10_000_000)),
        );
        tx.set_field_amount(sf("sfAmount2"), iou_amount(sf("sfAmount2"), issue, 5_000));
        tx.set_field_u16(sf("sfTradingFee"), 500);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = tx::run_dex_read_view_preclaim(&view, &tx, TxType::AMM_CREATE)
        .expect("AMMCreate must have a typed preclaim");

    assert_eq!(result, Ter::TEC_UNFUNDED_AMM);
    assert!(
        view.read(protocol::keylet::amm(
            Asset::Issue(issue),
            Asset::Issue(xrp_issue()),
        ))
        .expect("AMM read should succeed")
        .is_none()
    );
}

#[test]
fn amm_create_rejects_mpt_asset_without_holder_token() {
    let account = sample_account(0x33);
    let issuer = sample_account(0x34);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_amount = STAmount::from_mpt_amount(
        sf("sfAmount"),
        protocol::MPTAmount::from_value(25),
        mpt_issue,
    );
    let xrp_amount = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_CREATE, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_amount(sf("sfAmount"), mpt_amount);
        tx.set_field_amount(sf("sfAmount2"), xrp_amount);
        tx.set_field_u16(sf("sfTradingFee"), 50);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_CREATE, None);

    assert_eq!(result, Ter::TEC_NO_AUTH);
}

#[test]
fn amm_create_allows_mpt_issuer_without_holder_token() {
    let issuer = sample_account(0x39);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_amount = STAmount::from_mpt_amount(
        sf("sfAmount"),
        protocol::MPTAmount::from_value(25),
        mpt_issue,
    );
    let xrp_amount = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(issuer, 0, 0, 1_000_000_000),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
        ),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_CREATE, |tx| {
        tx.set_account_id(sf("sfAccount"), issuer);
        tx.set_field_amount(sf("sfAmount"), mpt_amount);
        tx.set_field_amount(sf("sfAmount2"), xrp_amount);
        tx.set_field_u16(sf("sfTradingFee"), 50);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_CREATE, None);

    assert_eq!(result, Ter::TES_SUCCESS);
}

#[test]
fn amm_create_uses_pre_fee_reserve_decision_at_exact_boundary() {
    let account = sample_account(0x3C);
    let issuer = sample_account(0x3D);
    let issue = Issue::new(currency_from_string("USD"), issuer);
    let xrp_amount = test_xrp(53_599_956);
    let iou_amount = iou_amount(sf("sfAmount2"), issue, 500_000_000);

    // Regression for ledger 20,151,057 transaction 62B46F...F99B8C.
    // AMMCreate preclaim evaluates xrpLiquid(view, account, 1) before the
    // transaction fee is deducted.  The account's 55,099,976-drop balance
    // minus its 1,500,020-drop next-owner reserve is exactly the requested
    // 53,599,956 drops. doApply must not repeat that decision after the
    // 200,000-drop fee has reduced the balance to 54,899,976.
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 1, 0, 55_099_976),
        account_root(issuer, 0, lsfDefaultRipple),
        trust_line_entry(account, issuer, issue.currency, 1_000_000_000),
    ]);
    ledger.set_fees(Fees {
        base: 200_000,
        reserve: 1_000_000,
        increment: 250_010,
    });
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("AMM")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_CREATE, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_amount(sf("sfAmount"), xrp_amount.clone());
        tx.set_field_amount(sf("sfAmount2"), iou_amount.clone());
        tx.set_field_u16(sf("sfTradingFee"), 500);
        tx.set_field_amount(sf("sfFee"), test_xrp(200_000));
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        tx::run_dex_read_view_preclaim(&view, &tx, TxType::AMM_CREATE),
        Some(Ter::TES_SUCCESS),
        "the immutable pre-fee view has exactly enough liquid XRP"
    );

    // Model the common Transactor preamble before doApply: the fee is burned
    // after preclaim succeeds. AMMCreate doApply must trust that saved result.
    let account_keylet = account_keylet(raw_account_id(account));
    let account_root = view
        .peek(account_keylet)
        .expect("account read")
        .expect("account exists");
    let mut post_fee =
        STLedgerEntry::from_stobject(account_root.clone_as_object(), account_keylet.key);
    post_fee.set_field_amount(sf("sfBalance"), test_xrp(54_899_976));
    view.update(Arc::new(post_fee))
        .expect("post-fee balance update");

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::AMM_CREATE, Some(55_099_976)),
        Ter::TES_SUCCESS
    );
    assert!(
        view.read(protocol::keylet::amm(
            xrp_amount.asset(),
            iou_amount.asset()
        ))
        .expect("AMM read")
        .is_some()
    );
}

#[test]
fn amm_create_initializes_mpt_pool_holder_with_amm_authorized_flags() {
    let account = sample_account(0x3A);
    let issuer = sample_account(0x3B);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_amount = STAmount::from_mpt_amount(
        sf("sfAmount"),
        protocol::MPTAmount::from_value(25),
        mpt_issue,
    );
    let xrp_amount = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        mpt_issuance_entry(
            issuer,
            1,
            50,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
        ),
        mptoken_entry(account, mpt_id, 50),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_CREATE, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_amount(sf("sfAmount"), mpt_amount.clone());
        tx.set_field_amount(sf("sfAmount2"), xrp_amount.clone());
        tx.set_field_u16(sf("sfTradingFee"), 50);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_CREATE, None);

    assert_eq!(result, Ter::TES_SUCCESS);
    let amm_keylet = protocol::keylet::amm(mpt_amount.asset(), xrp_amount.asset());
    let amm = view
        .read(amm_keylet)
        .expect("amm read")
        .expect("amm should be created");
    let amm_account = amm.get_account_id(sf("sfAccount"));
    let amm_root = view
        .read(account_keylet(raw_account_id(amm_account)))
        .expect("amm account read")
        .expect("amm pseudo account should be created");
    assert_eq!(amm_root.get_field_h256(sf("sfAMMID")), amm_keylet.key);
    assert_eq!(
        amm.get_field_amount(sf("sfLPTokenBalance")).issue(),
        protocol::amm_lpt_issue_from_assets(mpt_amount.asset(), xrp_amount.asset(), amm_account)
    );
    assert_eq!(owner_count(&view, account), 1);
    assert_eq!(amm.get_field_u16(sf("sfTradingFee")), 50);
    let votes = amm.get_field_array(sf("sfVoteSlots"));
    assert_eq!(votes.len(), 1);
    let vote = votes.get(0).expect("creator vote");
    assert_eq!(vote.get_account_id(sf("sfAccount")), account);
    assert_eq!(
        vote.get_field_u32(sf("sfVoteWeight")),
        protocol::VOTE_WEIGHT_SCALE_FACTOR
    );
    assert_eq!(vote.get_field_u16(sf("sfTradingFee")), 50);
    let auction = amm.get_field_object(sf("sfAuctionSlot"));
    assert_eq!(auction.get_account_id(sf("sfAccount")), account);
    assert_eq!(
        auction.get_field_u32(sf("sfExpiration")),
        protocol::TOTAL_TIME_SLOT_SECS
    );
    assert_eq!(auction.get_field_u16(sf("sfDiscountedFee")), 5);
    let price = auction.get_field_amount(sf("sfPrice"));
    assert_eq!(price.signum(), 0);
    assert_eq!(
        price.issue(),
        protocol::amm_lpt_issue_from_assets(mpt_amount.asset(), xrp_amount.asset(), amm_account)
    );

    let amm_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(amm_account),
        ))
        .expect("amm token read")
        .expect("amm mptoken should be created");
    assert_eq!(amm_token.get_field_u64(sf("sfMPTAmount")), 25);
    assert!(amm_token.is_flag(protocol::lsfMPTAMM));
    assert!(amm_token.is_flag(protocol::lsfMPTAuthorized));

    let source_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(account),
        ))
        .expect("source token read")
        .expect("source mptoken should remain");
    assert_eq!(source_token.get_field_u64(sf("sfMPTAmount")), 25);
}

#[test]
fn amm_deposit_rejects_locked_mpt_asset_before_pool_mutation() {
    let account = sample_account(0x15);
    let issuer = sample_account(0x16);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset = STAmount::from_mpt_amount(
        sf("sfAsset"),
        protocol::MPTAmount::from_value(25),
        mpt_issue,
    );
    let xrp_asset = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade | protocol::lsfMPTLocked,
        ),
        mptoken_entry(account, mpt_id, 50),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_DEPOSIT, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), mpt_asset.asset()),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), xrp_asset.asset()),
        );
        tx.set_field_amount(
            sf("sfAmount"),
            STAmount::from_mpt_amount(
                sf("sfAmount"),
                protocol::MPTAmount::from_value(50),
                mpt_issue,
            ),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfFlags"), 0x0008_0000);
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_DEPOSIT, None);

    assert_eq!(result, Ter::TEC_LOCKED);
}

#[test]
fn amm_deposit_rechecks_calculated_xrp_liquidity_on_post_fee_view() {
    let account = sample_account(0x17);
    let issuer = sample_account(0x18);
    let amm_account = sample_account(0x19);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset = Asset::MPTIssue(mpt_issue);
    let xrp_asset = Asset::Issue(xrp_issue());

    let mut ledger = empty_ledger(vec![
        // This is already the post-fee balance. With no LP line, the next
        // owner reserve is 250 drops and only 99 drops are liquid.
        account_root_with_balance(account, 0, 0, 349),
        account_root(issuer, 1, 0),
        account_root_with_balance(amm_account, 0, 0, 100),
        mpt_issuance_entry(
            issuer,
            1,
            1_000,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
        ),
        mptoken_entry(account, mpt_id, 1),
        mptoken_entry(amm_account, mpt_id, 100),
        amm_mpt_xrp_entry(amm_account, mpt_issue, 100, 100),
    ]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 200,
        increment: 50,
    });
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_DEPOSIT, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), mpt_asset),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), xrp_asset),
        );
        tx.set_field_amount(sf("sfAmount"), test_xrp(100));
        tx.set_field_amount(sf("sfFee"), test_xrp(10));
        tx.set_field_u32(sf("sfFlags"), protocol::AMM_SINGLE_ASSET_FLAG);
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::AMM_DEPOSIT, None),
        Ter::TEC_UNFUNDED_AMM
    );
}

#[test]
fn amm_deposit_rejects_locked_mpt_pool_holding_before_pool_mutation() {
    let account = sample_account(0x3A);
    let issuer = sample_account(0x3B);
    let amm_account = sample_account(0x3C);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset =
        STAmount::from_mpt_amount(sf("sfAsset"), protocol::MPTAmount::from_value(0), mpt_issue);
    let xrp_asset = STAmount::from_xrp_amount(XRPAmount::from_drops(0));
    let mut amm_holding = mptoken_entry(amm_account, mpt_id, 100);
    amm_holding.set_field_u32(sf("sfFlags"), protocol::lsfMPTLocked);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        account_root(amm_account, 0, 0),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
        ),
        mptoken_entry(account, mpt_id, 50),
        amm_holding,
        amm_mpt_xrp_entry(amm_account, mpt_issue, 100, 100),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_DEPOSIT, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), mpt_asset.asset()),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), xrp_asset.asset()),
        );
        tx.set_field_amount(
            sf("sfAmount"),
            STAmount::from_mpt_amount(
                sf("sfAmount"),
                protocol::MPTAmount::from_value(50),
                mpt_issue,
            ),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfFlags"), 0x0008_0000);
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_DEPOSIT, None);

    assert_eq!(result, Ter::TEC_LOCKED);
}

#[test]
fn amm_deposit_rejects_mpt_deposit_amount_without_holder_token() {
    let account = sample_account(0x35);
    let issuer = sample_account(0x36);
    let amm_account = sample_account(0x37);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset =
        STAmount::from_mpt_amount(sf("sfAsset"), protocol::MPTAmount::from_value(0), mpt_issue);
    let xrp_asset = STAmount::from_xrp_amount(XRPAmount::from_drops(0));
    let amm = amm_mpt_xrp_entry(amm_account, mpt_issue, 100, 100);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        account_root(amm_account, 0, 0),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
        ),
        amm,
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_DEPOSIT, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), mpt_asset.asset()),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), xrp_asset.asset()),
        );
        tx.set_field_amount(
            sf("sfAmount"),
            STAmount::from_mpt_amount(
                sf("sfAmount"),
                protocol::MPTAmount::from_value(50),
                mpt_issue,
            ),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfFlags"), 0x0008_0000);
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_DEPOSIT, None);

    assert_eq!(result, Ter::TEC_NO_AUTH);
}

#[test]
fn amm_bid_finds_mpt_xrp_pool_by_full_asset_key() {
    let bidder = sample_account(0x41);
    let issuer = sample_account(0x42);
    let amm_account = sample_account(0x43);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let lp_issue = Issue::new(currency_from_string("LPT"), amm_account);
    let mpt_asset =
        STAmount::from_mpt_amount(sf("sfAsset"), protocol::MPTAmount::from_value(0), mpt_issue);
    let xrp_asset = STAmount::from_xrp_amount(XRPAmount::from_drops(0));
    let mut amm = amm_mpt_xrp_entry(amm_account, mpt_issue, 100, 100);
    let mut auction_slot = amm.get_field_object(sf("sfAuctionSlot"));
    auction_slot.set_account_id(sf("sfAccount"), sample_account(0x44));
    auction_slot.set_field_u32(sf("sfExpiration"), protocol::TOTAL_TIME_SLOT_SECS);
    amm.set_field_object(sf("sfAuctionSlot"), auction_slot);

    let mut ledger = empty_ledger(vec![
        account_root_with_balance(bidder, 1, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        account_root_with_balance(amm_account, 1, 0, 1_000_000_000),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
        ),
        mptoken_entry(amm_account, mpt_id, 100),
        trust_line_entry_iou(
            bidder,
            amm_account,
            lp_issue.currency,
            IOUAmount::from_parts(10, 0).expect("bidder lp balance"),
        ),
        amm,
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_BID, |tx| {
        tx.set_account_id(sf("sfAccount"), bidder);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), mpt_asset.asset()),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), xrp_asset.asset()),
        );
        tx.set_field_amount(
            sf("sfBidMin"),
            STAmount::from_iou_amount(
                sf("sfBidMin"),
                IOUAmount::from_parts(1, 0).expect("bid min"),
                lp_issue,
            ),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_BID, None);

    assert_eq!(result, Ter::TES_SUCCESS);
    let amm = view
        .read(protocol::keylet::amm(mpt_asset.asset(), xrp_asset.asset()))
        .expect("amm read")
        .expect("amm should remain");
    assert_eq!(
        amm.get_field_object(sf("sfAuctionSlot"))
            .get_account_id(sf("sfAccount")),
        bidder
    );
    assert_eq!(
        amm.get_field_amount(sf("sfLPTokenBalance")),
        STAmount::from_iou_amount(
            sf_generic(),
            IOUAmount::from_parts(99, 0).expect("updated lp balance"),
            lp_issue,
        )
    );
    let bidder_line = view
        .read(line(bidder, amm_account, lp_issue.currency))
        .expect("bidder line read")
        .expect("bidder lp line should remain");
    assert_eq!(
        bidder_line.get_field_amount(sf("sfBalance")).iou(),
        IOUAmount::from_parts(9, 0).expect("bidder lp post-bid")
    );
}

#[test]
fn amm_bid_rejects_mpt_asset_without_mptokens_v2() {
    let bidder = sample_account(0x49);
    let issuer = sample_account(0x4A);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset =
        STAmount::from_mpt_amount(sf("sfAsset"), protocol::MPTAmount::from_value(0), mpt_issue);
    let xrp_asset = STAmount::from_xrp_amount(XRPAmount::from_drops(0));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(bidder, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("AMM")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_BID, |tx| {
        tx.set_account_id(sf("sfAccount"), bidder);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), mpt_asset.asset()),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), xrp_asset.asset()),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::AMM_BID, None),
        Ter::TEM_DISABLED
    );
}

#[test]
fn amm_delete_rejects_mpt_asset_without_mptokens_v2() {
    let owner = sample_account(0x4B);
    let issuer = sample_account(0x4C);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset =
        STAmount::from_mpt_amount(sf("sfAsset"), protocol::MPTAmount::from_value(0), mpt_issue);
    let xrp_asset = STAmount::from_xrp_amount(XRPAmount::from_drops(0));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(owner, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("AMM")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_DELETE, |tx| {
        tx.set_account_id(sf("sfAccount"), owner);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), mpt_asset.asset()),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), xrp_asset.asset()),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::AMM_DELETE, None),
        Ter::TEM_DISABLED
    );
}

#[test]
fn amm_delete_makes_bounded_progress_and_continues_on_reapply() {
    let sender = sample_account(0x4D);
    let amm_account = sample_account(0x60);
    let line_issuer = sample_account(0x70);
    let usd_issuer = sample_account(0x71);
    let eur_issuer = sample_account(0x72);
    let usd = Issue::new(currency_from_string("USD"), usd_issuer);
    let eur = Issue::new(currency_from_string("EUR"), eur_issuer);

    let mut amm = amm_entry(amm_account, usd, eur, 0, vec![], 0);
    amm.set_field_u64(sf("sfOwnerNode"), 0);
    let amm_key = *amm.key();
    let mut amm_children = vec![amm_key];
    let mut issuer_children = Vec::new();
    let mut entries = vec![
        account_root(sender, 0, 0),
        account_root(amm_account, 514, 0),
        account_root(line_issuer, 513, 0),
        account_root(usd_issuer, 0, 0),
        account_root(eur_issuer, 0, 0),
        amm,
    ];
    for index in 0..513 {
        let currency = currency_from_string(&format!("{index:03X}"));
        let mut trustline = trust_line_entry(amm_account, line_issuer, currency, 0);
        trustline.set_field_u64(sf("sfLowNode"), 0);
        trustline.set_field_u64(sf("sfHighNode"), 0);
        amm_children.push(*trustline.key());
        issuer_children.push(*trustline.key());
        entries.push(trustline);
    }
    entries.push(owner_dir_root_with_children(amm_account, amm_children));
    entries.push(owner_dir_root_with_children(line_issuer, issuer_children));

    let mut ledger = empty_ledger(entries);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("AMM")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_DELETE, |tx| {
        tx.set_account_id(sf("sfAccount"), sender);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(usd)),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(eur)),
        );
        tx.set_field_amount(sf("sfFee"), test_xrp(10));
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    assert_eq!(
        apply_submit_transactor_shell(&mut view, &tx, TxType::AMM_DELETE),
        Ter::TEC_INCOMPLETE
    );
    assert!(
        view.read(protocol::keylet::amm(Asset::Issue(usd), Asset::Issue(eur)))
            .expect("AMM read after partial delete")
            .is_some()
    );
    let remaining_after_first = (0..513)
        .filter(|index| {
            let currency = currency_from_string(&format!("{index:03X}"));
            view.read(line(amm_account, line_issuer, currency))
                .expect("trust line read after partial delete")
                .is_some()
        })
        .count();
    assert_eq!(remaining_after_first, 2);

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::AMM_DELETE, None),
        Ter::TES_SUCCESS
    );
    assert!(
        view.read(protocol::keylet::amm(Asset::Issue(usd), Asset::Issue(eur)))
            .expect("AMM read after completed delete")
            .is_none()
    );
    assert!(
        view.read(account_keylet(raw_account_id(amm_account)))
            .expect("AMM account read after completed delete")
            .is_none()
    );
}

#[test]
fn amm_deposit_waives_mpt_transfer_fee() {
    let account = sample_account(0x45);
    let issuer = sample_account(0x46);
    let amm_account = sample_account(0x47);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset =
        STAmount::from_mpt_amount(sf("sfAsset"), protocol::MPTAmount::from_value(0), mpt_issue);
    let xrp_asset = STAmount::from_xrp_amount(XRPAmount::from_drops(0));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        account_root_with_balance(amm_account, 0, 0, 1_000_000_000),
        mpt_issuance_entry_with_transfer_fee(
            issuer,
            1,
            200,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
            10_000,
        ),
        mptoken_entry(account, mpt_id, 50),
        mptoken_entry(amm_account, mpt_id, 100),
        amm_mpt_xrp_entry(amm_account, mpt_issue, 100, 100),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_DEPOSIT, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), mpt_asset.asset()),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), xrp_asset.asset()),
        );
        tx.set_field_amount(
            sf("sfAmount"),
            STAmount::from_mpt_amount(
                sf("sfAmount"),
                protocol::MPTAmount::from_value(10),
                mpt_issue,
            ),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfFlags"), 0x0008_0000);
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_DEPOSIT, None);

    assert_eq!(result, Ter::TES_SUCCESS);
    let account_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(account),
        ))
        .expect("account token read")
        .expect("account token should remain");
    assert_eq!(account_token.get_field_u64(sf("sfMPTAmount")), 40);
    let amm_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(amm_account),
        ))
        .expect("amm token read")
        .expect("amm token should remain");
    assert_eq!(amm_token.get_field_u64(sf("sfMPTAmount")), 110);
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read")
        .expect("issuance should remain");
    assert_eq!(issuance.get_field_u64(sf("sfOutstandingAmount")), 200);
}

#[test]
fn amm_deposit_uses_active_auction_slot_discount_for_single_asset_math() {
    let account = sample_account(0x48);
    let non_owner = sample_account(0x49);
    let issuer = sample_account(0x4A);
    let amm_account = sample_account(0x4B);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset = Asset::MPTIssue(mpt_issue);
    let xrp_asset = Asset::Issue(xrp_issue());

    let make_view = |slot_owner: AccountID| {
        let mut amm = amm_mpt_xrp_entry(amm_account, mpt_issue, 1_000_000, 1_000_000);
        amm.set_field_u16(sf("sfTradingFee"), 400);
        let mut slot = amm.get_field_object(sf("sfAuctionSlot"));
        slot.set_account_id(sf("sfAccount"), slot_owner);
        slot.set_field_u16(sf("sfDiscountedFee"), 40);
        amm.set_field_object(sf("sfAuctionSlot"), slot);

        let mut ledger = empty_ledger(vec![
            account_root_with_balance(account, 0, 0, 1_000_000_000),
            account_root(issuer, 1, 0),
            account_root_with_balance(amm_account, 0, 0, 1_000_000_000),
            mpt_issuance_entry(
                issuer,
                1,
                2_000_000,
                protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
            ),
            mptoken_entry(account, mpt_id, 1_000_000),
            mptoken_entry(amm_account, mpt_id, 1_000_000),
            amm,
        ]);
        ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
        ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE)
    };

    let tx = STTx::new(TxType::AMM_DEPOSIT, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), mpt_asset),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), xrp_asset),
        );
        tx.set_field_amount(
            sf("sfAmount"),
            STAmount::from_mpt_amount(
                sf("sfAmount"),
                protocol::MPTAmount::from_value(500_000),
                mpt_issue,
            ),
        );
        tx.set_field_amount(sf("sfFee"), test_xrp(10));
        tx.set_field_u32(sf("sfFlags"), protocol::AMM_SINGLE_ASSET_FLAG);
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let mut discounted = make_view(account);
    let mut regular = make_view(non_owner);
    assert_eq!(
        handle_real_dispatch(&mut discounted, &tx, TxType::AMM_DEPOSIT, None),
        Ter::TES_SUCCESS
    );
    assert_eq!(
        handle_real_dispatch(&mut regular, &tx, TxType::AMM_DEPOSIT, None),
        Ter::TES_SUCCESS
    );

    let amm_key = protocol::keylet::amm(mpt_asset, xrp_asset);
    let discounted_lp = discounted
        .read(amm_key)
        .expect("discounted AMM read")
        .expect("discounted AMM")
        .get_field_amount(sf("sfLPTokenBalance"));
    let regular_lp = regular
        .read(amm_key)
        .expect("regular AMM read")
        .expect("regular AMM")
        .get_field_amount(sf("sfLPTokenBalance"));

    assert!(discounted_lp > regular_lp);
}

#[test]
fn amm_withdraw_fix_v1_2_creates_missing_mpt_holding_only_after_amendment() {
    let account = sample_account(0x17);
    let issuer = sample_account(0x18);
    let amm_account = sample_account(0x40);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset = STAmount::from_mpt_amount(
        sf("sfAsset"),
        protocol::MPTAmount::from_value(25),
        mpt_issue,
    );
    let xrp_asset = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let tx = STTx::new(TxType::AMM_WITHDRAW, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_u32(sf("sfFlags"), protocol::AMM_LP_TOKEN_FLAG);
        tx.set_field_amount(sf("sfAsset"), mpt_asset);
        tx.set_field_amount(sf("sfAsset2"), xrp_asset);
        tx.set_field_amount(
            sf("sfLPTokenIn"),
            STAmount::from_iou_amount(
                sf("sfLPTokenIn"),
                IOUAmount::from_parts(1, 0).expect("lp amount"),
                Issue::new(currency_from_string("LPT"), amm_account),
            ),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    for (fix_enabled, owner_count, pre_fee_balance, expected, holding_created) in [
        (false, 0, 1_000_000_000, Ter::TEC_NO_AUTH, false),
        (true, 0, 1_000_000_000, Ter::TES_SUCCESS, true),
        // MPT reserve uses the captured pre-fee balance, not the larger
        // current balance. With two existing objects this must fail reserve.
        (true, 2, 0, Ter::TEC_INSUFFICIENT_RESERVE, false),
    ] {
        let mut ledger = empty_ledger(vec![
            account_root_with_balance(account, owner_count, 0, 1_000_000_000),
            account_root(issuer, 1, 0),
            account_root(amm_account, 0, 0),
            mpt_issuance_entry(issuer, 1, 100, protocol::lsfMPTCanTrade),
            mptoken_entry(amm_account, mpt_id, 100),
            trust_line_entry_iou(
                account,
                amm_account,
                currency_from_string("LPT"),
                IOUAmount::from_parts(1, 0).expect("lp trustline balance"),
            ),
            amm_mpt_xrp_entry(amm_account, mpt_issue, 100, 100),
        ]);
        ledger.set_fees(Fees {
            base: 10,
            reserve: 200,
            increment: 50,
        });
        let mut amendments = vec![protocol::feature_id("MPTokensV2")];
        if fix_enabled {
            amendments.push(protocol::feature_id("fixAMMv1_2"));
        }
        ledger.set_rules(protocol::Rules::new(amendments));
        let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
        let result =
            handle_real_dispatch(&mut view, &tx, TxType::AMM_WITHDRAW, Some(pre_fee_balance));
        assert_eq!(result, expected, "fixAMMv1_2 enabled={fix_enabled}");
        let holding = view
            .read(protocol::mptoken_keylet_from_mptid(
                mpt_id,
                Uint160::from_void(account.data()),
            ))
            .expect("holder MPToken read");
        assert_eq!(holding.is_some(), holding_created);
    }
}

#[test]
fn amm_withdraw_rejects_require_auth_mpt_asset_without_authorization() {
    let account = sample_account(0x38);
    let issuer = sample_account(0x39);
    let amm_account = sample_account(0x3A);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset = STAmount::from_mpt_amount(
        sf("sfAsset"),
        protocol::MPTAmount::from_value(25),
        mpt_issue,
    );
    let xrp_asset = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        account_root(amm_account, 0, 0),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTrade | protocol::lsfMPTRequireAuth,
        ),
        mptoken_entry(amm_account, mpt_id, 100),
        amm_mpt_xrp_entry(amm_account, mpt_issue, 100, 100),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_WITHDRAW, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_amount(sf("sfAsset"), mpt_asset);
        tx.set_field_amount(sf("sfAsset2"), xrp_asset);
        tx.set_field_amount(
            sf("sfLPTokenIn"),
            STAmount::from_iou_amount(
                sf("sfLPTokenIn"),
                IOUAmount::from_parts(1, 0).expect("lp amount"),
                Issue::new(currency_from_string("LPT"), amm_account),
            ),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_WITHDRAW, Some(1_000_000_000));

    assert_eq!(result, Ter::TEC_NO_AUTH);
}

#[test]
fn amm_withdraw_rejects_locked_mpt_asset_before_pool_mutation() {
    let account = sample_account(0x19);
    let issuer = sample_account(0x1A);
    let amm_account = sample_account(0x1B);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset = STAmount::from_mpt_amount(
        sf("sfAsset"),
        protocol::MPTAmount::from_value(25),
        mpt_issue,
    );
    let xrp_asset = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        account_root(amm_account, 0, 0),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade | protocol::lsfMPTLocked,
        ),
        mptoken_entry(account, mpt_id, 50),
        mptoken_entry(amm_account, mpt_id, 100),
        amm_mpt_xrp_entry(amm_account, mpt_issue, 100, 100),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_WITHDRAW, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_amount(sf("sfAsset"), mpt_asset);
        tx.set_field_amount(sf("sfAsset2"), xrp_asset);
        tx.set_field_amount(
            sf("sfLPTokenIn"),
            STAmount::from_iou_amount(
                sf("sfLPTokenIn"),
                IOUAmount::from_parts(1, 0).expect("lp amount"),
                Issue::new(currency_from_string("LPT"), amm_account),
            ),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_WITHDRAW, Some(1_000_000_000));

    assert_eq!(result, Ter::TEC_LOCKED);
}

#[test]
fn amm_withdraw_rejects_locked_mpt_pool_holding_before_pool_mutation() {
    let account = sample_account(0x3D);
    let issuer = sample_account(0x3E);
    let amm_account = sample_account(0x3F);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let mpt_asset =
        STAmount::from_mpt_amount(sf("sfAsset"), protocol::MPTAmount::from_value(0), mpt_issue);
    let xrp_asset = STAmount::from_xrp_amount(XRPAmount::from_drops(0));
    let mut amm_holding = mptoken_entry(amm_account, mpt_id, 100);
    amm_holding.set_field_u32(sf("sfFlags"), protocol::lsfMPTLocked);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(account, 0, 0, 1_000_000_000),
        account_root(issuer, 1, 0),
        account_root(amm_account, 0, 0),
        mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTCanTrade,
        ),
        mptoken_entry(account, mpt_id, 50),
        amm_holding,
        amm_mpt_xrp_entry(amm_account, mpt_issue, 100, 100),
    ]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("MPTokensV2")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_WITHDRAW, |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_amount(sf("sfAsset"), mpt_asset);
        tx.set_field_amount(sf("sfAsset2"), xrp_asset);
        tx.set_field_amount(
            sf("sfLPTokenIn"),
            STAmount::from_iou_amount(
                sf("sfLPTokenIn"),
                IOUAmount::from_parts(1, 0).expect("lp amount"),
                Issue::new(currency_from_string("LPT"), amm_account),
            ),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::AMM_WITHDRAW, Some(1_000_000_000));

    assert_eq!(result, Ter::TEC_LOCKED);
}

#[test]
fn amm_clawback_with_amount_withdraws_from_pool_burns_lp_and_claws_primary_asset() {
    let issuer = sample_account(0x50);
    let holder = sample_account(0x30);
    let amm_account = sample_account(0x40);
    let usd = Issue::new(currency_from_string("USD"), issuer);
    let eur = Issue::new(currency_from_string("EUR"), issuer);
    let lpt_currency = amm_lpt_currency(usd.currency, eur.currency);
    let mut issuer_root = account_root(issuer, 0, protocol::lsfAllowTrustLineClawback);
    issuer_root.set_field_u32(sf("sfTransferRate"), 2_000_000_000);

    let ledger = empty_ledger(vec![
        issuer_root,
        account_root(holder, 0, 0),
        account_root(amm_account, 0, 0),
        amm_entry(amm_account, usd, eur, 100, vec![], 0),
        trust_line_entry(amm_account, issuer, usd.currency, 1_000),
        trust_line_entry(amm_account, issuer, eur.currency, 2_000),
        trust_line_entry(holder, issuer, usd.currency, 0),
        trust_line_entry(holder, issuer, eur.currency, 0),
        trust_line_entry(holder, amm_account, lpt_currency, 10),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_CLAWBACK, |tx| {
        tx.set_account_id(sf("sfAccount"), issuer);
        tx.set_account_id(sf("sfHolder"), holder);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(usd)),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(eur)),
        );
        tx.set_field_amount(sf("sfAmount"), iou_amount(sf("sfAmount"), usd, 50));
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = dispatch_with_pre_fee_balance(&mut view, &tx, TxType::AMM_CLAWBACK);

    assert_eq!(result, Ter::TES_SUCCESS);
    let amm = view
        .read(protocol::keylet::amm(Asset::Issue(usd), Asset::Issue(eur)))
        .expect("amm read should succeed")
        .expect("amm should remain");
    assert_eq!(
        amm.get_field_amount(sf("sfLPTokenBalance")).iou(),
        IOUAmount::from_parts(95, 0).expect("remaining lp")
    );
    assert_eq!(
        view.read(line(amm_account, issuer, usd.currency))
            .expect("amm usd line read")
            .expect("amm usd line")
            .get_field_amount(sf("sfBalance"))
            .iou(),
        IOUAmount::from_parts(950, 0).expect("amm usd")
    );
    assert_eq!(
        view.read(line(amm_account, issuer, eur.currency))
            .expect("amm eur line read")
            .expect("amm eur line")
            .get_field_amount(sf("sfBalance"))
            .iou(),
        IOUAmount::from_parts(1_900, 0).expect("amm eur")
    );
    assert_eq!(
        view.read(line(holder, issuer, usd.currency))
            .expect("holder usd line read")
            .expect("holder usd line")
            .get_field_amount(sf("sfBalance"))
            .iou(),
        IOUAmount::new()
    );
    assert_eq!(
        view.read(line(holder, issuer, eur.currency))
            .expect("holder eur line read")
            .expect("holder eur line")
            .get_field_amount(sf("sfBalance"))
            .iou(),
        IOUAmount::from_parts(100, 0).expect("holder paired asset")
    );
    assert_eq!(
        view.read(line(holder, amm_account, lpt_currency))
            .expect("holder lp line read")
            .expect("holder lp line")
            .get_field_amount(sf("sfBalance"))
            .iou(),
        IOUAmount::from_parts(5, 0).expect("holder lp")
    );
}

#[test]
fn amm_clawback_fix_v1_2_recreates_authorized_mpt_then_redeems_to_issuer() {
    let issuer = sample_account(0x61);
    let holder = sample_account(0x62);
    let amm_account = sample_account(0x63);
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = MPTIssue::new(mpt_id);
    let xrp = xrp_issue();
    let lpt_currency = currency_from_string("LPT");

    let mut ledger = empty_ledger(vec![
        account_root(issuer, 0, 0),
        account_root_with_balance(holder, 0, 0, 1_000),
        account_root_with_balance(amm_account, 0, 0, 100),
        mpt_issuance_entry(
            issuer,
            1,
            200,
            protocol::lsfMPTCanClawback | protocol::lsfMPTRequireAuth,
        ),
        mptoken_entry(amm_account, mpt_id, 100),
        trust_line_entry(holder, amm_account, lpt_currency, 10),
        amm_mpt_xrp_entry(amm_account, mpt_issue, 100, 100),
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("MPTokensV2"),
        protocol::feature_id("fixAMMv1_2"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_CLAWBACK, |tx| {
        tx.set_account_id(sf("sfAccount"), issuer);
        tx.set_account_id(sf("sfHolder"), holder);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), Asset::MPTIssue(mpt_issue)),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(xrp)),
        );
        tx.set_field_amount(
            sf("sfAmount"),
            STAmount::from_mpt_amount(sf("sfAmount"), MPTAmount::from_value(5), mpt_issue),
        );
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(sf("sfSequence"), 1);
    });

    let result = dispatch_with_pre_fee_balance(&mut view, &tx, TxType::AMM_CLAWBACK);

    assert_eq!(result, Ter::TES_SUCCESS);
    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("issuance read should succeed")
        .expect("issuance should remain");
    assert_eq!(issuance.get_field_u64(sf("sfOutstandingAmount")), 195);
    let holder_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(holder),
        ))
        .expect("holder token read should succeed")
        .expect("holder token should remain");
    assert_eq!(holder_token.get_field_u64(sf("sfMPTAmount")), 0);
    assert!(holder_token.is_flag(protocol::lsfMPTAuthorized));
    let amm_token = view
        .read(protocol::mptoken_keylet_from_mptid(
            mpt_id,
            raw_account_id(amm_account),
        ))
        .expect("amm token read should succeed")
        .expect("amm token should remain");
    assert_eq!(amm_token.get_field_u64(sf("sfMPTAmount")), 95);
    let holder_root = view
        .read(account_keylet(raw_account_id(holder)))
        .expect("holder read should succeed")
        .expect("holder should remain");
    assert_eq!(
        holder_root.get_field_amount(sf("sfBalance")).xrp().drops(),
        1_005
    );
}

#[test]
fn amm_clawback_mpt_amount_requires_mptokens_v2_before_amount_validation() {
    let issuer = sample_account(0x64);
    let holder = sample_account(0x65);
    let mpt_issue = MPTIssue::new(share_id_for(issuer, 1));
    let usd = Issue::new(currency_from_string("USD"), issuer);
    let eur = Issue::new(currency_from_string("EUR"), issuer);
    let ledger = empty_ledger(Vec::new());
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    let tx = STTx::new(TxType::AMM_CLAWBACK, |tx| {
        tx.set_account_id(sf("sfAccount"), issuer);
        tx.set_account_id(sf("sfHolder"), holder);
        tx.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(usd)),
        );
        tx.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(eur)),
        );
        tx.set_field_amount(
            sf("sfAmount"),
            STAmount::from_mpt_amount(sf("sfAmount"), MPTAmount::from_value(1), mpt_issue),
        );
    });

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::AMM_CLAWBACK, Some(0)),
        Ter::TEM_DISABLED
    );
}

// ============================================================================
// LOAN_PAY mode tests: Late, Full, Overpayment
// ============================================================================

fn loan_pay_ledger(
    borrower: AccountID,
    broker_owner: AccountID,
    broker_pseudo: AccountID,
    vault_pseudo: AccountID,
    loan_id: Uint256,
    broker_id: Uint256,
    vault_id: Uint256,
    asset: Asset,
    principal: i64,
    periodic_payment: i64,
    debt_total: i64,
    payment_remaining: u32,
) -> Ledger {
    loan_pay_ledger_with_parent_close_time(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        principal,
        periodic_payment,
        debt_total,
        payment_remaining,
        0,
    )
}

fn loan_pay_ledger_with_parent_close_time(
    borrower: AccountID,
    broker_owner: AccountID,
    broker_pseudo: AccountID,
    vault_pseudo: AccountID,
    loan_id: Uint256,
    broker_id: Uint256,
    vault_id: Uint256,
    asset: Asset,
    principal: i64,
    periodic_payment: i64,
    debt_total: i64,
    payment_remaining: u32,
    parent_close_time: u32,
) -> Ledger {
    let mut loan = managed_loan_entry(
        loan_id,
        borrower,
        broker_id,
        principal,
        principal,
        0,
        payment_remaining,
        120,
    );
    loan.set_field_number(
        get_field_by_symbol("sfPeriodicPayment"),
        asset_number(asset, periodic_payment),
    );

    let broker = loan_broker_entry(
        broker_id,
        broker_owner,
        broker_pseudo,
        vault_id,
        asset,
        debt_total,
        0,
        0,
        0,
    );

    let mut vault = vault_entry(broker_owner, vault_pseudo, 1, asset);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 0),
    );
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, principal),
    );

    let mut ledger = ledger_with_header(
        LedgerHeader {
            seq: 1,
            parent_close_time,
            ..LedgerHeader::default()
        },
        vec![
            account_root_with_balance(borrower, 0, 0, 1_000_000_000),
            account_root_with_balance(vault_pseudo, 0, 0, 0),
            account_root_with_balance(broker_pseudo, 0, 0, 0),
            loan,
            broker,
            vault,
        ],
    );
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
    ]));
    ledger
}

#[test]
fn loan_pay_late_mode_reduces_principal_and_decrements_payment_remaining() {
    let borrower = sample_account(0xE5);
    let broker_owner = sample_account(0xE6);
    let broker_pseudo = sample_account(0xE7);
    let vault_pseudo = sample_account(0xE8);
    let loan_id = sample_uint256(0xF5);
    let broker_id = sample_uint256(0xF6);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger_with_parent_close_time(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        500_000_000,
        50_000_000,
        500_000_000,
        10,
        121,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    // LOAN_LATE_PAYMENT_FLAG = 0x0004_0000
    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(50_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_LATE_PAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let updated_loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan should still exist");
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfPrincipalOutstanding"))
            .value(),
        RuntimeNumber::from_i64(450_000_000)
    );
    assert_eq!(
        updated_loan.get_field_u32(get_field_by_symbol("sfPaymentRemaining")),
        9
    );
}

#[test]
fn loan_pay_late_mode_rejects_before_due_date_expires() {
    let borrower = sample_account(0xD0);
    let broker_owner = sample_account(0xD1);
    let broker_pseudo = sample_account(0xD2);
    let vault_pseudo = sample_account(0xD3);
    let loan_id = sample_uint256(0xD4);
    let broker_id = sample_uint256(0xD5);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        500_000_000,
        50_000_000,
        500_000_000,
        10,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(50_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_LATE_PAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TEC_TOO_SOON);
}

#[test]
fn loan_pay_late_mode_pays_late_fee_in_addition_to_service_fee() {
    let borrower = sample_account(0xD6);
    let broker_owner = sample_account(0xD7);
    let broker_pseudo = sample_account(0xD8);
    let vault_pseudo = sample_account(0xD9);
    let loan_id = sample_uint256(0xDA);
    let broker_id = sample_uint256(0xDB);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger_with_parent_close_time(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        500_000_000,
        50_000_000,
        500_000_000,
        10,
        121,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    view.insert(Arc::new(account_root_with_balance(
        broker_owner,
        0,
        0,
        1_000_000,
    )))
    .expect("insert broker owner");
    let loan_key = protocol::loan_keylet_from_key(loan_id);
    let loan = view
        .peek(loan_key)
        .expect("loan read")
        .expect("loan exists");
    let mut updated_loan = STLedgerEntry::from_stobject(loan.clone_as_object(), *loan.key());
    updated_loan.set_field_number(
        get_field_by_symbol("sfLoanServiceFee"),
        asset_number(asset, 5_000_000),
    );
    updated_loan.set_field_number(
        get_field_by_symbol("sfLatePaymentFee"),
        asset_number(asset, 10_000_000),
    );
    view.update(Arc::new(updated_loan)).expect("update loan");

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(65_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_LATE_PAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let broker_root = view
        .read(protocol::account_keylet(raw_account_id(broker_owner)))
        .expect("broker owner read")
        .expect("broker owner exists");
    assert_eq!(
        broker_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        16_000_000
    );
}

#[test]
fn loan_pay_routes_fee_to_pseudo_when_iou_broker_owner_deep_frozen() {
    let issuer = sample_account(0x10);
    let borrower = sample_account(0x20);
    let broker_owner = sample_account(0x30);
    let broker_pseudo = sample_account(0x40);
    let vault_pseudo = sample_account(0x50);
    let loan_id = sample_uint256(0x51);
    let broker_id = sample_uint256(0x52);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let currency = currency_from_string("USD");
    let issue = Issue::new(currency, issuer);
    let asset = Asset::Issue(issue);

    let ledger = loan_pay_ledger_with_parent_close_time(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        500,
        50,
        500,
        10,
        121,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    view.insert(Arc::new(account_root(issuer, 4, lsfDefaultRipple)))
        .expect("insert issuer");
    view.insert(Arc::new(account_root(broker_owner, 1, 0)))
        .expect("insert broker owner");

    view.insert(Arc::new(trust_line_entry_iou(
        issuer,
        borrower,
        currency,
        IOUAmount::from_parts(-1_000, 0).expect("borrower balance"),
    )))
    .expect("insert borrower line");
    view.insert(Arc::new(trust_line_entry_iou(
        issuer,
        vault_pseudo,
        currency,
        IOUAmount::new(),
    )))
    .expect("insert vault pseudo line");
    view.insert(Arc::new(trust_line_entry_iou(
        issuer,
        broker_pseudo,
        currency,
        IOUAmount::new(),
    )))
    .expect("insert broker pseudo line");
    let mut owner_line = trust_line_entry_iou(issuer, broker_owner, currency, IOUAmount::new());
    owner_line.set_field_u32(get_field_by_symbol("sfFlags"), lsfLowDeepFreeze);
    view.insert(Arc::new(owner_line))
        .expect("insert broker owner line");

    let loan_key = protocol::loan_keylet_from_key(loan_id);
    let loan = view
        .peek(loan_key)
        .expect("loan read")
        .expect("loan exists");
    let mut updated_loan = STLedgerEntry::from_stobject(loan.clone_as_object(), *loan.key());
    updated_loan.set_field_number(
        get_field_by_symbol("sfLoanServiceFee"),
        asset_number(asset, 5),
    );
    updated_loan.set_field_number(
        get_field_by_symbol("sfLatePaymentFee"),
        asset_number(asset, 10),
    );
    view.update(Arc::new(updated_loan)).expect("update loan");

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_iou_amount(
                get_field_by_symbol("sfAmount"),
                IOUAmount::from_parts(65, 0).expect("payment amount"),
                issue,
            ),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_LATE_PAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let owner_line = view
        .read(line(issuer, broker_owner, currency))
        .expect("owner line read")
        .expect("owner line exists");
    let pseudo_line = view
        .read(line(issuer, broker_pseudo, currency))
        .expect("pseudo line read")
        .expect("pseudo line exists");
    assert_eq!(
        owner_line
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .signum(),
        0
    );
    assert_ne!(
        pseudo_line
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .signum(),
        0
    );
}

#[test]
fn loan_pay_late_mode_applies_overdue_interest_and_management_fee_split() {
    let borrower = sample_account(0xE2);
    let broker_owner = sample_account(0xE3);
    let broker_pseudo = sample_account(0xE4);
    let vault_pseudo = sample_account(0xE5);
    let loan_id = sample_uint256(0xE6);
    let broker_id = sample_uint256(0xE7);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger_with_parent_close_time(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        500_000_000,
        50_000_000,
        500_000_000,
        10,
        31_536_120,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    view.insert(Arc::new(account_root_with_balance(
        broker_owner,
        0,
        0,
        1_000_000,
    )))
    .expect("insert broker owner");

    let loan_key = protocol::loan_keylet_from_key(loan_id);
    let loan = view
        .peek(loan_key)
        .expect("loan read")
        .expect("loan exists");
    let mut updated_loan = STLedgerEntry::from_stobject(loan.clone_as_object(), *loan.key());
    updated_loan.set_field_u32(get_field_by_symbol("sfLateInterestRate"), 10_000);
    view.update(Arc::new(updated_loan)).expect("update loan");

    let broker_key = protocol::loan_broker_keylet_from_key(broker_id);
    let broker = view
        .peek(broker_key)
        .expect("broker read")
        .expect("broker exists");
    let mut updated_broker = STLedgerEntry::from_stobject(broker.clone_as_object(), *broker.key());
    updated_broker.set_field_u16(get_field_by_symbol("sfManagementFeeRate"), 10_000);
    view.update(Arc::new(updated_broker))
        .expect("update broker");

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(100_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_LATE_PAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let vault_root = view
        .read(protocol::account_keylet(raw_account_id(vault_pseudo)))
        .expect("vault pseudo read")
        .expect("vault pseudo exists");
    assert_eq!(
        vault_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        95_000_000
    );
    let broker_root = view
        .read(protocol::account_keylet(raw_account_id(broker_owner)))
        .expect("broker owner read")
        .expect("broker owner exists");
    assert_eq!(
        broker_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        6_000_000
    );
    let updated_loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan exists");
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfTotalValueOutstanding"))
            .value(),
        RuntimeNumber::from_i64(450_000_000)
    );
    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read")
        .expect("vault exists");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsTotal"))
            .value(),
        RuntimeNumber::from_i64(545_000_000)
    );
}

#[test]
fn loan_pay_base_fee_uses_loan_scale_and_upward_periodic_rounding() {
    let borrower = sample_account(0xA1);
    let broker_owner = sample_account(0xA2);
    let broker_pseudo = sample_account(0xA3);
    let vault_pseudo = sample_account(0xA4);
    let issuer = sample_account(0xA5);
    let loan_id = sample_uint256(0xA6);
    let broker_id = sample_uint256(0xA7);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let issue = Issue {
        currency: currency_from_string("USD"),
        account: issuer,
    };
    let asset = Asset::Issue(issue);

    let mut loan = loan_entry(loan_id, borrower, broker_id, 0, 0);
    loan.set_field_i32(get_field_by_symbol("sfLoanScale"), -2);
    loan.set_field_number(
        get_field_by_symbol("sfTotalValueOutstanding"),
        asset_number(asset, 100),
    );
    loan.set_field_number(
        get_field_by_symbol("sfPrincipalOutstanding"),
        asset_number(asset, 100),
    );
    loan.set_field_number(
        get_field_by_symbol("sfManagementFeeOutstanding"),
        asset_number(asset, 0),
    );
    loan.set_field_number(
        get_field_by_symbol("sfPeriodicPayment"),
        asset_number_parts(asset, 101, -2),
    );
    loan.set_field_u32(get_field_by_symbol("sfPaymentRemaining"), 10);
    loan.set_field_u32(get_field_by_symbol("sfNextPaymentDueDate"), 120);

    let broker = loan_broker_entry(
        broker_id,
        broker_owner,
        broker_pseudo,
        vault_id,
        asset,
        100,
        0,
        0,
        0,
    );
    let mut vault = vault_entry(broker_owner, vault_pseudo, 1, asset);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsTotal"),
        asset_number(asset, 100),
    );

    let mut ledger = empty_ledger(vec![loan, broker, vault]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("fixSecurity3_1_3"),
    ]));

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_iou_amount(
                get_field_by_symbol("sfAmount"),
                IOUAmount::from_parts(6, 0).expect("iou amount"),
                issue,
            ),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    assert_eq!(calculate_loan_pay_base_fee(&ledger, &tx, 10), Ok(10));
}

#[test]
fn loan_pay_regular_mode_processes_multiple_scheduled_periods() {
    let borrower = sample_account(0xB8);
    let broker_owner = sample_account(0xB9);
    let broker_pseudo = sample_account(0xBA);
    let vault_pseudo = sample_account(0xBB);
    let loan_id = sample_uint256(0xBC);
    let broker_id = sample_uint256(0xBD);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        500_000_000,
        50_000_000,
        500_000_000,
        10,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(150_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let updated_loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan should still exist");
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfPrincipalOutstanding"))
            .value(),
        RuntimeNumber::from_i64(350_000_000)
    );
    assert_eq!(
        updated_loan.get_field_u32(get_field_by_symbol("sfPaymentRemaining")),
        7
    );
}

#[test]
fn loan_pay_regular_service_fee_does_not_reduce_total_value_outstanding() {
    let borrower = sample_account(0xBE);
    let broker_owner = sample_account(0xBF);
    let broker_pseudo = sample_account(0xC0);
    let vault_pseudo = sample_account(0xC1);
    let loan_id = sample_uint256(0xC2);
    let broker_id = sample_uint256(0xC3);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        500_000_000,
        50_000_000,
        500_000_000,
        10,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    view.insert(Arc::new(account_root_with_balance(
        broker_owner,
        0,
        0,
        1_000_000,
    )))
    .expect("insert broker owner");
    let loan_key = protocol::loan_keylet_from_key(loan_id);
    let loan = view
        .peek(loan_key)
        .expect("loan read")
        .expect("loan exists");
    let mut updated_loan = STLedgerEntry::from_stobject(loan.clone_as_object(), *loan.key());
    updated_loan.set_field_number(
        get_field_by_symbol("sfLoanServiceFee"),
        asset_number(asset, 10_000_000),
    );
    view.update(Arc::new(updated_loan)).expect("update loan");

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(60_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let updated_loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan should still exist");
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfTotalValueOutstanding"))
            .value(),
        RuntimeNumber::from_i64(450_000_000)
    );
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfPrincipalOutstanding"))
            .value(),
        RuntimeNumber::from_i64(450_000_000)
    );
    let broker_root = view
        .read(protocol::account_keylet(raw_account_id(broker_owner)))
        .expect("broker owner read")
        .expect("broker owner exists");
    assert_eq!(
        broker_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        11_000_000
    );
}

#[test]
fn loan_pay_regular_mpt_interest_payment_keeps_integer_principal_after_cleanup_3_2_0() {
    let borrower = sample_account(0xB1);
    let broker_owner = sample_account(0xB2);
    let broker_pseudo = sample_account(0xB3);
    let vault_pseudo = sample_account(0xB4);
    let issuer = sample_account(0xB5);
    let loan_id = sample_uint256(0xB6);
    let broker_id = sample_uint256(0xB7);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let mpt_id = share_id_for(issuer, 1);
    let mpt_issue = protocol::MPTIssue::new(mpt_id);
    let asset = Asset::MPTIssue(mpt_issue);

    let mut loan = loan_entry(loan_id, borrower, broker_id, 0, 0);
    loan.set_field_i32(get_field_by_symbol("sfLoanScale"), 0);
    loan.set_field_number(
        get_field_by_symbol("sfTotalValueOutstanding"),
        asset_number(asset, 3),
    );
    loan.set_field_number(
        get_field_by_symbol("sfPrincipalOutstanding"),
        asset_number(asset, 1),
    );
    loan.set_field_number(
        get_field_by_symbol("sfManagementFeeOutstanding"),
        asset_number(asset, 0),
    );
    loan.set_field_number(
        get_field_by_symbol("sfPeriodicPayment"),
        asset_number(asset, 1),
    );
    loan.set_field_u32(get_field_by_symbol("sfPaymentRemaining"), 3);
    loan.set_field_u32(get_field_by_symbol("sfNextPaymentDueDate"), 120);
    loan.set_field_u32(get_field_by_symbol("sfPreviousPaymentDueDate"), 120);
    loan.set_field_u32(get_field_by_symbol("sfStartDate"), 100);
    loan.set_field_u32(get_field_by_symbol("sfPaymentInterval"), 31_536_000);
    loan.set_field_u32(get_field_by_symbol("sfInterestRate"), 200_000);

    let broker = loan_broker_entry(
        broker_id,
        broker_owner,
        broker_pseudo,
        vault_id,
        asset,
        3,
        0,
        0,
        0,
    );

    let mut vault = vault_entry(broker_owner, vault_pseudo, 1, asset);
    vault.set_field_number(
        get_field_by_symbol("sfAssetsAvailable"),
        asset_number(asset, 0),
    );
    vault.set_field_number(get_field_by_symbol("sfAssetsTotal"), asset_number(asset, 3));

    let mut ledger = empty_ledger(vec![
        account_root_with_balance(borrower, 0, 0, 1_000_000_000),
        account_root_with_balance(vault_pseudo, 0, 0, 0),
        account_root_with_balance(broker_pseudo, 0, 0, 0),
        account_root(issuer, 1, 0),
        mpt_issuance_entry(issuer, 1, 10, protocol::lsfMPTCanTransfer),
        mptoken_entry(borrower, mpt_id, 3),
        // A Vault pseudo-account owns its asset holding from VaultCreate.
        // Pinned accountSendMulti does not synthesize a missing destination
        // holding during LoanPay.
        mptoken_entry(vault_pseudo, mpt_id, 0),
        loan,
        broker,
        vault,
    ]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("LendingProtocol"),
        protocol::feature_id("SingleAssetVault"),
        protocol::feature_id("MPTokensV1"),
        protocol::feature_id("fixCleanup3_2_0"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_mpt_amount(
                get_field_by_symbol("sfAmount"),
                protocol::MPTAmount::from_value(1),
                mpt_issue,
            ),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let updated_loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan should still exist");
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfPrincipalOutstanding"))
            .value(),
        RuntimeNumber::from_i64(1)
    );
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfTotalValueOutstanding"))
            .value(),
        RuntimeNumber::from_i64(2)
    );
    assert_eq!(
        updated_loan.get_field_u32(get_field_by_symbol("sfPaymentRemaining")),
        2
    );
}

#[test]
fn loan_pay_full_mode_clears_principal_and_payment_remaining() {
    let borrower = sample_account(0xE9);
    let broker_owner = sample_account(0xEA);
    let broker_pseudo = sample_account(0xEB);
    let vault_pseudo = sample_account(0xEC);
    let loan_id = sample_uint256(0xF7);
    let broker_id = sample_uint256(0xF8);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        500_000_000,
        50_000_000,
        500_000_000,
        10,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    // LOAN_FULL_PAYMENT_FLAG = 0x0002_0000
    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(500_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_FULL_PAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let updated_loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan should still exist");
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfPrincipalOutstanding"))
            .value(),
        RuntimeNumber::zero()
    );
    assert_eq!(
        updated_loan.get_field_u32(get_field_by_symbol("sfPaymentRemaining")),
        0
    );
}

#[test]
fn loan_pay_full_mode_pays_close_fee_without_service_fee() {
    let borrower = sample_account(0xCA);
    let broker_owner = sample_account(0xCB);
    let broker_pseudo = sample_account(0xCC);
    let vault_pseudo = sample_account(0xCD);
    let loan_id = sample_uint256(0xCE);
    let broker_id = sample_uint256(0xCF);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        500_000_000,
        50_000_000,
        500_000_000,
        10,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    view.insert(Arc::new(account_root_with_balance(
        broker_owner,
        0,
        0,
        1_000_000,
    )))
    .expect("insert broker owner");
    let loan_key = protocol::loan_keylet_from_key(loan_id);
    let loan = view
        .peek(loan_key)
        .expect("loan read")
        .expect("loan exists");
    let mut updated_loan = STLedgerEntry::from_stobject(loan.clone_as_object(), *loan.key());
    updated_loan.set_field_number(
        get_field_by_symbol("sfLoanServiceFee"),
        asset_number(asset, 20_000_000),
    );
    updated_loan.set_field_number(
        get_field_by_symbol("sfClosePaymentFee"),
        asset_number(asset, 10_000_000),
    );
    view.update(Arc::new(updated_loan)).expect("update loan");

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(510_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_FULL_PAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let updated_loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan should still exist");
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfTotalValueOutstanding"))
            .value(),
        RuntimeNumber::zero()
    );
    let broker_root = view
        .read(protocol::account_keylet(raw_account_id(broker_owner)))
        .expect("broker owner read")
        .expect("broker owner exists");
    assert_eq!(
        broker_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        11_000_000
    );
}

#[test]
fn loan_pay_full_mode_applies_close_interest_and_management_fee_split() {
    let borrower = sample_account(0xDC);
    let broker_owner = sample_account(0xDD);
    let broker_pseudo = sample_account(0xDE);
    let vault_pseudo = sample_account(0xDF);
    let loan_id = sample_uint256(0xE0);
    let broker_id = sample_uint256(0xE1);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        500_000_000,
        50_000_000,
        500_000_000,
        10,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    view.insert(Arc::new(account_root_with_balance(
        broker_owner,
        0,
        0,
        1_000_000,
    )))
    .expect("insert broker owner");

    let loan_key = protocol::loan_keylet_from_key(loan_id);
    let loan = view
        .peek(loan_key)
        .expect("loan read")
        .expect("loan exists");
    let mut updated_loan = STLedgerEntry::from_stobject(loan.clone_as_object(), *loan.key());
    updated_loan.set_field_u32(get_field_by_symbol("sfCloseInterestRate"), 10_000);
    view.update(Arc::new(updated_loan)).expect("update loan");

    let broker_key = protocol::loan_broker_keylet_from_key(broker_id);
    let broker = view
        .peek(broker_key)
        .expect("broker read")
        .expect("broker exists");
    let mut updated_broker = STLedgerEntry::from_stobject(broker.clone_as_object(), *broker.key());
    updated_broker.set_field_u16(get_field_by_symbol("sfManagementFeeRate"), 10_000);
    view.update(Arc::new(updated_broker))
        .expect("update broker");

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(550_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_FULL_PAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let vault_root = view
        .read(protocol::account_keylet(raw_account_id(vault_pseudo)))
        .expect("vault pseudo read")
        .expect("vault pseudo exists");
    assert_eq!(
        vault_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        545_000_000
    );
    let broker_root = view
        .read(protocol::account_keylet(raw_account_id(broker_owner)))
        .expect("broker owner read")
        .expect("broker owner exists");
    assert_eq!(
        broker_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        6_000_000
    );

    let vault = view
        .read(protocol::vault_keylet_from_key(vault_id))
        .expect("vault read")
        .expect("vault exists");
    assert_eq!(
        vault
            .get_field_number(get_field_by_symbol("sfAssetsTotal"))
            .value(),
        RuntimeNumber::from_i64(545_000_000)
    );
}

#[test]
fn loan_pay_full_mode_rejects_final_scheduled_payment() {
    let borrower = sample_account(0xC4);
    let broker_owner = sample_account(0xC5);
    let broker_pseudo = sample_account(0xC6);
    let vault_pseudo = sample_account(0xC7);
    let loan_id = sample_uint256(0xC8);
    let broker_id = sample_uint256(0xC9);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        50_000_000,
        50_000_000,
        50_000_000,
        1,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(50_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_FULL_PAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TEC_KILLED);
}

#[test]
fn loan_pay_overpayment_mode_reduces_principal_by_multiple_periods() {
    let borrower = sample_account(0xED);
    let broker_owner = sample_account(0xEE);
    let broker_pseudo = sample_account(0xEF);
    let vault_pseudo = sample_account(0xF0);
    let loan_id = sample_uint256(0xF9);
    let broker_id = sample_uint256(0xFA);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        500_000_000,
        50_000_000,
        500_000_000,
        10,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let loan_key = protocol::loan_keylet_from_key(loan_id);
    let loan = view
        .peek(loan_key)
        .expect("loan read")
        .expect("loan exists");
    let mut updated_loan = STLedgerEntry::from_stobject(loan.clone_as_object(), *loan.key());
    updated_loan.set_field_u32(get_field_by_symbol("sfFlags"), protocol::lsfLoanOverpayment);
    view.update(Arc::new(updated_loan)).expect("update loan");

    // LOAN_OVERPAYMENT_FLAG = 0x0001_0000 — pay 3 periods at once
    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(150_000_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_OVERPAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let updated_loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan should still exist");
    // 3 periods × 50M = 150M paid → 500M - 150M = 350M remaining
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfPrincipalOutstanding"))
            .value(),
        RuntimeNumber::from_i64(350_000_000)
    );
    assert_eq!(
        updated_loan.get_field_u32(get_field_by_symbol("sfPaymentRemaining")),
        7
    );
}

#[test]
fn loan_pay_overpayment_applies_penalty_fee_management_split_and_reamortizes() {
    let borrower = sample_account(0xD1);
    let broker_owner = sample_account(0xD2);
    let broker_pseudo = sample_account(0xD3);
    let vault_pseudo = sample_account(0xD4);
    let loan_id = sample_uint256(0xD5);
    let broker_id = sample_uint256(0xD6);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        10_000,
        2_500,
        10_000,
        4,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    view.insert(Arc::new(account_root_with_balance(
        broker_owner,
        0,
        0,
        1_000_000,
    )))
    .expect("insert broker owner");

    let loan_key = protocol::loan_keylet_from_key(loan_id);
    let loan = view
        .peek(loan_key)
        .expect("loan read")
        .expect("loan exists");
    let mut updated_loan = STLedgerEntry::from_stobject(loan.clone_as_object(), *loan.key());
    updated_loan.set_field_u32(get_field_by_symbol("sfFlags"), protocol::lsfLoanOverpayment);
    updated_loan.set_field_u32(get_field_by_symbol("sfOverpaymentFee"), 5_000);
    updated_loan.set_field_u32(get_field_by_symbol("sfOverpaymentInterestRate"), 20_000);
    view.update(Arc::new(updated_loan)).expect("update loan");

    let broker_key = protocol::loan_broker_keylet_from_key(broker_id);
    let broker = view
        .peek(broker_key)
        .expect("broker read")
        .expect("broker exists");
    let mut updated_broker = STLedgerEntry::from_stobject(broker.clone_as_object(), *broker.key());
    updated_broker.set_field_u16(get_field_by_symbol("sfManagementFeeRate"), 10_000);
    view.update(Arc::new(updated_broker))
        .expect("update broker");

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(4_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_OVERPAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let updated_loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan should still exist");
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfPrincipalOutstanding"))
            .value(),
        RuntimeNumber::from_i64(6_375)
    );
    assert!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfPeriodicPayment"))
            .value()
            < RuntimeNumber::from_i64(3_334)
    );
    assert_eq!(
        updated_loan.get_field_u32(get_field_by_symbol("sfPaymentRemaining")),
        3
    );

    let broker_root = view
        .read(protocol::account_keylet(raw_account_id(broker_owner)))
        .expect("broker owner read")
        .expect("broker owner exists");
    assert_eq!(
        broker_root
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        1_000_105
    );
}

#[test]
fn loan_pay_overpayment_skips_invalid_reamortization_guard() {
    let borrower = sample_account(0x91);
    let broker_owner = sample_account(0x92);
    let broker_pseudo = sample_account(0x93);
    let vault_pseudo = sample_account(0x94);
    let loan_id = sample_uint256(0x95);
    let broker_id = sample_uint256(0x96);
    let vault_id = protocol::vault_keylet(raw_account_id(broker_owner), 1).key;
    let asset = Asset::Issue(xrp_issue());

    let ledger = loan_pay_ledger(
        borrower,
        broker_owner,
        broker_pseudo,
        vault_pseudo,
        loan_id,
        broker_id,
        vault_id,
        asset,
        10_000,
        3_333,
        10_000,
        3,
    );
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let loan_key = protocol::loan_keylet_from_key(loan_id);
    let loan = view
        .peek(loan_key)
        .expect("loan read")
        .expect("loan exists");
    let mut updated_loan = STLedgerEntry::from_stobject(loan.clone_as_object(), *loan.key());
    updated_loan.set_field_u32(get_field_by_symbol("sfFlags"), protocol::lsfLoanOverpayment);
    updated_loan.set_field_u32(get_field_by_symbol("sfOverpaymentFee"), 5_000);
    updated_loan.set_field_u32(get_field_by_symbol("sfOverpaymentInterestRate"), 20_000);
    view.update(Arc::new(updated_loan)).expect("update loan");

    let broker_key = protocol::loan_broker_keylet_from_key(broker_id);
    let broker = view
        .peek(broker_key)
        .expect("broker read")
        .expect("broker exists");
    let mut updated_broker = STLedgerEntry::from_stobject(broker.clone_as_object(), *broker.key());
    updated_broker.set_field_u16(get_field_by_symbol("sfManagementFeeRate"), 10_000);
    view.update(Arc::new(updated_broker))
        .expect("update broker");

    let tx = STTx::new(TxType::LOAN_PAY, |tx| {
        tx.set_account_id(get_field_by_symbol("sfAccount"), borrower);
        tx.set_field_h256(get_field_by_symbol("sfLoanID"), loan_id);
        tx.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(5_000, false),
        );
        tx.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::new_native(10, false),
        );
        tx.set_field_u32(get_field_by_symbol("sfSequence"), 1);
        tx.set_field_u32(
            get_field_by_symbol("sfFlags"),
            protocol::LOAN_OVERPAYMENT_FLAG,
        );
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::LOAN_PAY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let updated_loan = view
        .read(protocol::loan_keylet_from_key(loan_id))
        .expect("loan read")
        .expect("loan should still exist");
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfPrincipalOutstanding"))
            .value(),
        RuntimeNumber::from_i64(6_667)
    );
    assert_eq!(
        updated_loan
            .get_field_number(get_field_by_symbol("sfPeriodicPayment"))
            .value(),
        RuntimeNumber::from_i64(3_333)
    );
}

#[test]
fn mptoken_issuance_set_dispatch_lock_only_changes_holder_lock_state() {
    // Regression: C++ doApply has no sfSetFlag/sfClearFlag fallback.
    // Without capability-enable flags, the only flag mutation is lock/unlock.
    let issuer = sample_account(0xB1);
    let mpt_id = share_id_for(issuer, 1);
    let issuance = mpt_issuance_entry(
        issuer,
        1,
        0,
        protocol::lsfMPTCanLock | protocol::lsfMPTCanTransfer,
    );
    let original_flags = issuance.get_field_u32(get_field_by_symbol("sfFlags"));
    let mut ledger = empty_ledger(vec![account_root(issuer, 1, 0), issuance]);
    ledger.set_rules(protocol::Rules::new([
        protocol::feature_id("DynamicMPT"),
        protocol::feature_id("PermissionedDomains"),
        protocol::feature_id("SingleAssetVault"),
    ]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    // Submit only tfMPTLock; no capability flag is enabled.
    let tx = STTx::new(TxType::MPTOKEN_ISSUANCE_SET, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), issuer);
        object.set_field_h192(get_field_by_symbol("sfMPTokenIssuanceID"), mpt_id);
        object.set_field_u32(get_field_by_symbol("sfFlags"), protocol::tfMPTLock);
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::MPTOKEN_ISSUANCE_SET, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(mpt_id))
        .expect("read")
        .expect("exists");
    let flags = issuance.get_field_u32(get_field_by_symbol("sfFlags"));
    // Only lsfMPTLocked should be added — no sfSetFlag influence
    assert_eq!(flags, original_flags | protocol::lsfMPTLocked);
}

#[test]
fn nftoken_mint_and_burn_dispatch_split_then_merge_pages_with_page_owner_counts() {
    let account = sample_account(0xA0);
    let ledger = empty_ledger(vec![account_root_with_balance(
        account,
        0,
        0,
        10_000_000_000,
    )]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    for taxon in 0..33 {
        assert_eq!(
            handle_real_dispatch(
                &mut view,
                &nftoken_mint_tx(account, taxon, None),
                TxType::NFTOKEN_MINT,
                Some(10_000_000_000),
            ),
            Ter::TES_SUCCESS
        );
    }

    let account_root = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read")
        .expect("account exists");
    assert_eq!(account_root.get_field_u32(sf("sfMintedNFTokens")), 33);
    assert_eq!(account_root.get_field_u32(sf("sfOwnerCount")), 2);

    let max_page_keylet = protocol::nft_page_max_keylet(raw_account_id(account));
    let max_page = view
        .read(max_page_keylet)
        .expect("max page read")
        .expect("max page exists");
    assert!(max_page.is_field_present(sf("sfPreviousPageMin")));
    let previous_key = max_page.get_field_h256(sf("sfPreviousPageMin"));
    let previous_page = view
        .read(Keylet::new(LedgerEntryType::NFTokenPage, previous_key))
        .expect("previous page read")
        .expect("previous page exists");
    assert_eq!(
        previous_page.get_field_h256(sf("sfNextPageMin")),
        max_page_keylet.key
    );

    let burned_id = max_page
        .get_field_array(sf("sfNFTokens"))
        .get(0)
        .expect("max page token")
        .get_field_h256(sf("sfNFTokenID"));
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &nftoken_burn_tx(account, burned_id),
            TxType::NFTOKEN_BURN,
            None,
        ),
        Ter::TES_SUCCESS
    );

    let account_root = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read")
        .expect("account exists");
    assert_eq!(account_root.get_field_u32(sf("sfOwnerCount")), 1);
    assert_eq!(account_root.get_field_u32(sf("sfBurnedNFTokens")), 1);
    let merged_page = view
        .read(max_page_keylet)
        .expect("merged page read")
        .expect("merged max page exists");
    assert_eq!(merged_page.get_field_array(sf("sfNFTokens")).len(), 32);
    assert!(!merged_page.is_field_present(sf("sfPreviousPageMin")));
    assert!(
        view.read(Keylet::new(LedgerEntryType::NFTokenPage, previous_key))
            .expect("old page read")
            .is_none()
    );
}

#[test]
fn nftoken_mint_reserve_uses_sponsored_account_base() {
    let account = sample_account(0xAC);
    let sponsor = sample_account(0xAD);
    let mut root = account_root_with_balance(account, 0, 0, 50);
    root.set_account_id(sf("sfSponsor"), sponsor);
    let mut ledger = empty_ledger(vec![root]);
    ledger.set_fees(ledger::Fees {
        base: 10,
        reserve: 200,
        increment: 50,
    });
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &nftoken_mint_tx(account, 0, None),
            TxType::NFTOKEN_MINT,
            Some(50),
        ),
        Ter::TES_SUCCESS,
        "pinned accountReserve excludes a sponsored AccountRoot base while charging the new NFT page owner reserve"
    );
    let root = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read")
        .expect("account exists");
    assert_eq!(root.get_field_u32(sf("sfOwnerCount")), 1);
    assert_eq!(ledger::reserve_owner_count(&root, 0), 1);
    assert_eq!(ledger::reserve_account_count(&root, 0), 0);
}

#[test]
fn nftoken_burn_consolidates_three_pages_without_dropping_previous_page_tokens() {
    let account = sample_account(0xA1);
    let token_id = |suffix: u8| {
        let mut bytes = *make_nft_id(0, account).data();
        bytes[31] = suffix;
        Uint256::from_array(bytes)
    };
    let previous_token = token_id(50);
    let burn_token = token_id(150);
    let current_token = token_id(151);
    let next_token = token_id(250);

    let base = protocol::nft_page_min_keylet(raw_account_id(account));
    let previous_keylet = protocol::nft_page_keylet(base, token_id(100));
    let current_keylet = protocol::nft_page_keylet(base, token_id(200));
    let next_keylet = protocol::nft_page_max_keylet(raw_account_id(account));

    let page = |keylet: Keylet,
                token_ids: &[Uint256],
                previous: Option<Uint256>,
                next: Option<Uint256>| {
        let mut entry = STLedgerEntry::new(keylet);
        let mut tokens = STArray::new(sf("sfNFTokens"));
        for token_id in token_ids {
            tokens.push_back(nft_page_token(*token_id));
        }
        entry.set_field_array(sf("sfNFTokens"), tokens);
        if let Some(previous) = previous {
            entry.set_field_h256(sf("sfPreviousPageMin"), previous);
        }
        if let Some(next) = next {
            entry.set_field_h256(sf("sfNextPageMin"), next);
        }
        entry
    };

    let ledger = empty_ledger(vec![
        account_root(account, 3, 0),
        page(
            previous_keylet,
            &[previous_token],
            None,
            Some(current_keylet.key),
        ),
        page(
            current_keylet,
            &[burn_token, current_token],
            Some(previous_keylet.key),
            Some(next_keylet.key),
        ),
        page(next_keylet, &[next_token], Some(current_keylet.key), None),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &nftoken_burn_tx(account, burn_token),
            TxType::NFTOKEN_BURN,
            None,
        ),
        Ter::TES_SUCCESS
    );

    assert!(
        view.read(previous_keylet)
            .expect("previous page read")
            .is_none()
    );
    assert!(
        view.read(current_keylet)
            .expect("current page read")
            .is_none()
    );
    let remaining = view
        .read(next_keylet)
        .expect("next page read")
        .expect("consolidated page");
    let ids: Vec<_> = remaining
        .get_field_array(sf("sfNFTokens"))
        .iter()
        .map(|token| token.get_field_h256(sf("sfNFTokenID")))
        .collect();
    assert_eq!(ids, vec![previous_token, current_token, next_token]);
    assert_eq!(owner_count(&view, account), 1);
}

#[test]
fn nftoken_mint_dispatch_rejects_counter_overflow_without_creating_page() {
    let account = sample_account(0xA2);
    let mut root = account_root_with_balance(account, 0, 0, 10_000_000_000);
    root.set_field_u32(sf("sfFirstNFTokenSequence"), 1);
    root.set_field_u32(sf("sfMintedNFTokens"), u32::MAX);
    let ledger = empty_ledger(vec![root]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &nftoken_mint_tx(account, 0, None),
            TxType::NFTOKEN_MINT,
            Some(10_000_000_000),
        ),
        Ter::TEC_MAX_SEQUENCE_REACHED
    );
    assert!(
        view.read(protocol::nft_page_max_keylet(raw_account_id(account)))
            .expect("page read")
            .is_none()
    );
    let root = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read")
        .expect("account exists");
    assert_eq!(root.get_field_u32(sf("sfMintedNFTokens")), u32::MAX);
    assert_eq!(root.get_field_u32(sf("sfOwnerCount")), 0);
}

#[test]
fn nftoken_mint_amount_creates_sell_offer_and_burn_removes_it() {
    let account = sample_account(0xA3);
    let ledger = empty_ledger(vec![account_root_with_balance(
        account,
        0,
        0,
        10_000_000_000,
    )]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &nftoken_mint_tx(account, 0, Some(test_xrp(1_000))),
            TxType::NFTOKEN_MINT,
            Some(10_000_000_000),
        ),
        Ter::TES_SUCCESS
    );

    let page = view
        .read(protocol::nft_page_max_keylet(raw_account_id(account)))
        .expect("page read")
        .expect("page exists");
    let nftoken_id = page
        .get_field_array(sf("sfNFTokens"))
        .get(0)
        .expect("minted token")
        .get_field_h256(sf("sfNFTokenID"));
    let offer_keylet = protocol::keylet::nft_offer_keylet_for_owner(raw_account_id(account), 1);
    let offer = view
        .read(offer_keylet)
        .expect("offer read")
        .expect("sell offer exists");
    assert!(offer.is_flag(protocol::lsfSellNFToken));
    assert_eq!(offer.get_field_h256(sf("sfNFTokenID")), nftoken_id);
    assert_eq!(owner_count(&view, account), 2);

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &nftoken_burn_tx(account, nftoken_id),
            TxType::NFTOKEN_BURN,
            None,
        ),
        Ter::TES_SUCCESS
    );
    assert!(view.read(offer_keylet).expect("offer read").is_none());
    assert!(
        view.read(protocol::nft_page_max_keylet(raw_account_id(account)))
            .expect("page read")
            .is_none()
    );
    let root = view
        .read(account_keylet(raw_account_id(account)))
        .expect("account read")
        .expect("account exists");
    assert_eq!(root.get_field_u32(sf("sfOwnerCount")), 0);
    assert_eq!(root.get_field_u32(sf("sfMintedNFTokens")), 1);
    assert_eq!(root.get_field_u32(sf("sfBurnedNFTokens")), 1);
}

#[test]
fn nftoken_accept_offer_propagates_underfunded_xrp_payment() {
    let seller = sample_account(0xA4);
    let buyer = sample_account(0xA5);
    let ledger = empty_ledger(vec![
        account_root_with_balance(seller, 0, 0, 10_000_000_000),
        account_root_with_balance(buyer, 0, 0, 100),
    ]);
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &nftoken_mint_tx(seller, 0, Some(test_xrp(1_000))),
            TxType::NFTOKEN_MINT,
            Some(10_000_000_000),
        ),
        Ter::TES_SUCCESS
    );
    let offer = protocol::keylet::nft_offer_keylet_for_owner(raw_account_id(seller), 1).key;

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &nftoken_accept_sell_offer_tx(buyer, offer),
            TxType::NFTOKEN_ACCEPT_OFFER,
            None,
        ),
        Ter::TEC_INSUFFICIENT_FUNDS
    );
}

#[test]
fn nftoken_accept_offer_checks_reserve_when_buyer_needs_new_page() {
    let seller = sample_account(0xA6);
    let buyer = sample_account(0xA7);
    let mut ledger = empty_ledger(vec![
        account_root_with_balance(seller, 0, 0, 10_000_000_000),
        account_root_with_balance(buyer, 0, 0, 1),
    ]);
    ledger.set_fees(Fees {
        base: 10,
        reserve: 200,
        increment: 50,
    });
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &nftoken_mint_tx(seller, 0, Some(test_xrp(0))),
            TxType::NFTOKEN_MINT,
            Some(10_000_000_000),
        ),
        Ter::TES_SUCCESS
    );
    let offer = protocol::keylet::nft_offer_keylet_for_owner(raw_account_id(seller), 1).key;

    assert_eq!(
        handle_real_dispatch(
            &mut view,
            &nftoken_accept_sell_offer_tx(buyer, offer),
            TxType::NFTOKEN_ACCEPT_OFFER,
            None,
        ),
        Ter::TEC_INSUFFICIENT_RESERVE
    );
}

fn make_nft_id(flags: u16, issuer: AccountID) -> Uint256 {
    let mut bytes = [0u8; 32];
    bytes[..2].copy_from_slice(&flags.to_be_bytes());
    bytes[4..24].copy_from_slice(issuer.data());
    Uint256::from_array(bytes)
}

#[test]
fn nftoken_modify_dispatch_updates_uri() {
    let issuer = sample_account(0xA1);
    let token_id = make_nft_id(protocol::nft::FLAG_MUTABLE, issuer);
    // Use the max page keylet — nft_locate_page uses succ() to find pages
    let page_keylet = protocol::nft_page_max_keylet(raw_account_id(issuer));
    let mut token_obj = STObject::new(get_field_by_symbol("sfNFToken"));
    token_obj.set_field_h256(get_field_by_symbol("sfNFTokenID"), token_id);
    token_obj.set_field_vl(get_field_by_symbol("sfURI"), b"old-uri");
    let mut tokens = STArray::new(get_field_by_symbol("sfNFTokens"));
    tokens.push_back(token_obj);
    let mut page = STLedgerEntry::new(page_keylet);
    page.set_field_array(get_field_by_symbol("sfNFTokens"), tokens);

    let mut ledger = empty_ledger(vec![account_root(issuer, 1, 0), page]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("DynamicNFT")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::NFTOKEN_MODIFY, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), issuer);
        object.set_field_h256(get_field_by_symbol("sfNFTokenID"), token_id);
        object.set_field_vl(get_field_by_symbol("sfURI"), b"new-uri");
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::NFTOKEN_MODIFY, None);
    assert_eq!(result, protocol::Ter::TES_SUCCESS);

    let updated_page = view.read(page_keylet).expect("read").expect("exists");
    let tokens = updated_page.get_field_array(get_field_by_symbol("sfNFTokens"));
    let nft = tokens.iter().next().expect("one token");
    assert_eq!(nft.get_field_vl(get_field_by_symbol("sfURI")), b"new-uri");
}

#[test]
fn nftoken_modify_dispatch_rejects_immutable_token() {
    let issuer = sample_account(0xA2);
    // No FLAG_MUTABLE set
    let token_id = make_nft_id(0, issuer);
    let page_keylet = protocol::nft_page_max_keylet(raw_account_id(issuer));
    let page = nft_page_entry(page_keylet, token_id, None, None);

    let mut ledger = empty_ledger(vec![account_root(issuer, 1, 0), page]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("DynamicNFT")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::NFTOKEN_MODIFY, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), issuer);
        object.set_field_h256(get_field_by_symbol("sfNFTokenID"), token_id);
        object.set_field_vl(get_field_by_symbol("sfURI"), b"new-uri");
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::NFTOKEN_MODIFY, None);
    assert_eq!(result, protocol::Ter::TEC_NO_PERMISSION);
}

#[test]
fn nftoken_modify_dispatch_rejects_nftoken_taxon() {
    let issuer = sample_account(0xA4);
    let token_id = make_nft_id(protocol::nft::FLAG_MUTABLE, issuer);
    let page_keylet = protocol::nft_page_max_keylet(raw_account_id(issuer));
    let page = nft_page_entry(page_keylet, token_id, None, None);

    let mut ledger = empty_ledger(vec![account_root(issuer, 1, 0), page]);
    ledger.set_rules(protocol::Rules::new([protocol::feature_id("DynamicNFT")]));
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    // Build the raw decoded form because `STTx::new` applies NFTokenModify's
    // template, which deliberately omits `sfNFTokenTaxon` and therefore cannot
    // represent the malformed wire transaction being tested.
    let mut object = STObject::new(get_field_by_symbol("sfTransaction"));
    object.set_field_u16(
        get_field_by_symbol("sfTransactionType"),
        TxType::NFTOKEN_MODIFY.into(),
    );
    object.set_account_id(get_field_by_symbol("sfAccount"), issuer);
    object.set_field_h256(get_field_by_symbol("sfNFTokenID"), token_id);
    object.set_field_u32(get_field_by_symbol("sfNFTokenTaxon"), 10);
    object.set_field_amount(
        get_field_by_symbol("sfFee"),
        STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
    );
    object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    let tx = STTx::from_stobject(object);
    assert!(tx.is_field_present(get_field_by_symbol("sfNFTokenTaxon")));

    assert_eq!(
        handle_real_dispatch(&mut view, &tx, TxType::NFTOKEN_MODIFY, None),
        protocol::Ter::TEM_MALFORMED
    );
}

#[test]
fn nftoken_modify_dispatch_rejects_without_dynamic_nft_feature() {
    let issuer = sample_account(0xA3);
    let token_id = make_nft_id(protocol::nft::FLAG_MUTABLE, issuer);
    let page_keylet = protocol::keylet::nft_page_keylet(
        protocol::nft_page_min_keylet(raw_account_id(issuer)),
        Uint256::from(token_id),
    );
    let page = nft_page_entry(page_keylet, token_id, None, None);

    let ledger = empty_ledger(vec![account_root(issuer, 1, 0), page]);
    // No DynamicNFT feature enabled
    let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);

    let tx = STTx::new(TxType::NFTOKEN_MODIFY, |object| {
        object.set_account_id(get_field_by_symbol("sfAccount"), issuer);
        object.set_field_h256(get_field_by_symbol("sfNFTokenID"), token_id);
        object.set_field_vl(get_field_by_symbol("sfURI"), b"new-uri");
        object.set_field_amount(
            get_field_by_symbol("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        object.set_field_u32(get_field_by_symbol("sfSequence"), 1);
    });

    let result = handle_real_dispatch(&mut view, &tx, TxType::NFTOKEN_MODIFY, None);
    assert_eq!(result, protocol::Ter::TEM_DISABLED);
}
#[test]
fn amm_clawback_matrix_mpt_exact_thresholds() {
    let issuer = sample_account(0x11);
    let holder = sample_account(0x22);
    let amm_account = sample_account(0x33);

    let usd = Issue::new(currency_from_string("USD"), issuer);
    let mpt1_id = share_id_for(issuer, 1);
    let mpt1 = protocol::MPTIssue::new(mpt1_id);
    let mpt2_id = share_id_for(issuer, 2);
    let mpt2 = protocol::MPTIssue::new(mpt2_id);

    struct Row {
        desc: &'static str,
        asset1: Asset,
        asset2: Asset,
        holder_lp: i64,
        rounding_enabled: bool,
        expected: Ter,
    }

    let cases = [
        // MPT/IOU Vectors
        Row {
            desc: "MPT/IOU success rounding (exact 0.1% threshold)",
            asset1: Asset::MPTIssue(mpt1),
            asset2: Asset::Issue(usd),
            holder_lp: 999_001,
            rounding_enabled: true,
            expected: Ter::TES_SUCCESS,
        },
        Row {
            desc: "MPT/IOU fail rounding (exact 0.1% threshold)",
            asset1: Asset::MPTIssue(mpt1),
            asset2: Asset::Issue(usd),
            holder_lp: 999_000,
            rounding_enabled: true,
            expected: Ter::TEC_AMM_INVALID_TOKENS,
        },
        Row {
            desc: "MPT/IOU success without rounding",
            asset1: Asset::MPTIssue(mpt1),
            asset2: Asset::Issue(usd),
            holder_lp: 999_999,
            rounding_enabled: false,
            expected: Ter::TES_SUCCESS,
        },
        // MPT/MPT Vectors
        Row {
            desc: "MPT/MPT success rounding (exact 0.1% threshold)",
            asset1: Asset::MPTIssue(mpt1),
            asset2: Asset::MPTIssue(mpt2),
            holder_lp: 999_001,
            rounding_enabled: true,
            expected: Ter::TES_SUCCESS,
        },
        Row {
            desc: "MPT/MPT fail rounding (exact 0.1% threshold)",
            asset1: Asset::MPTIssue(mpt1),
            asset2: Asset::MPTIssue(mpt2),
            holder_lp: 999_000,
            rounding_enabled: true,
            expected: Ter::TEC_AMM_INVALID_TOKENS,
        },
        Row {
            desc: "MPT/MPT success without rounding",
            asset1: Asset::MPTIssue(mpt1),
            asset2: Asset::MPTIssue(mpt2),
            holder_lp: 999_999,
            rounding_enabled: false,
            expected: Ter::TES_SUCCESS,
        },
    ];

    for row in cases {
        let lp_currency = protocol::amm_lpt_currency_from_assets(row.asset1, row.asset2);

        let mut entries = vec![
            account_root(issuer, 0, protocol::lsfAllowTrustLineClawback),
            account_root(holder, 0, 0),
            account_root(amm_account, 0, 0),
        ];

        // Create AMM
        let keylet = protocol::keylet::amm(row.asset1, row.asset2);
        let mut amm = STLedgerEntry::from_type_and_key(LedgerEntryType::AMM, keylet.key);
        amm.set_account_id(sf("sfAccount"), amm_account);
        amm.set_field_u16(sf("sfTradingFee"), 17);
        amm.set_field_amount(
            sf("sfLPTokenBalance"),
            STAmount::from_iou_amount(
                sf_generic(),
                IOUAmount::from_parts(1_000_000, 0).expect("LP total"),
                Issue::new(lp_currency, amm_account),
            ),
        );
        amm.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), row.asset1),
        );
        amm.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), row.asset2),
        );
        amm.set_field_array(sf("sfVoteSlots"), STArray::new(sf("sfVoteSlots")));
        amm.set_field_u64(sf("sfOwnerNode"), 0);

        let mut slot = STObject::make_inner_object(sf("sfAuctionSlot"));
        slot.set_account_id(sf("sfAccount"), amm_account);
        slot.set_field_u32(sf("sfExpiration"), 1_000);
        slot.set_field_u16(sf("sfDiscountedFee"), 0);
        amm.set_field_object(sf("sfAuctionSlot"), slot);

        let mut amm_owner_children = vec![*amm.key()];
        let mut holder_owner_children = Vec::new();
        let mut issuer_owner_children = Vec::new();
        entries.push(amm);

        let lp_line = trust_line_entry_iou(
            holder,
            amm_account,
            lp_currency,
            IOUAmount::from_parts(row.holder_lp, 0).expect("LP balance"),
        );
        amm_owner_children.push(*lp_line.key());
        holder_owner_children.push(*lp_line.key());
        entries.push(lp_line);

        // Assets
        for asset in [row.asset1, row.asset2] {
            match asset {
                Asset::Issue(issue) => {
                    let pool_line = trust_line_entry_iou(
                        issuer,
                        amm_account,
                        issue.currency,
                        IOUAmount::from_parts(-1_000_000, 0).expect("IOU pool"),
                    );
                    amm_owner_children.push(*pool_line.key());
                    issuer_owner_children.push(*pool_line.key());
                    entries.push(pool_line);
                    entries.push(trust_line_entry_iou(
                        issuer,
                        holder,
                        issue.currency,
                        IOUAmount::from_parts(0, 0).expect("IOU holder"),
                    ));
                }
                Asset::MPTIssue(mpt_issue) => {
                    let seq = if mpt_issue.mpt_id() == mpt1_id { 1 } else { 2 };
                    entries.push(mpt_issuance_entry(
                        issuer,
                        seq,
                        1_000_000,
                        protocol::lsfMPTCanClawback,
                    ));
                    let amm_token = mptoken_entry(amm_account, mpt_issue.mpt_id(), 1_000_000);
                    amm_owner_children.push(*amm_token.key());
                    entries.push(amm_token);
                    let holder_token = mptoken_entry(holder, mpt_issue.mpt_id(), 0);
                    holder_owner_children.push(*holder_token.key());
                    entries.push(holder_token);
                }
            }
        }

        entries.push(owner_dir_root_with_children(
            amm_account,
            amm_owner_children,
        ));
        if !holder_owner_children.is_empty() {
            entries.push(owner_dir_root_with_children(holder, holder_owner_children));
        }
        if !issuer_owner_children.is_empty() {
            entries.push(owner_dir_root_with_children(issuer, issuer_owner_children));
        }

        let mut features = vec![
            protocol::feature_id("fixAMMv1_3"),
            protocol::feature_id("MPTokensV2"),
        ];
        if row.rounding_enabled {
            features.push(protocol::feature_id("fixAMMClawbackRounding"));
        }

        let mut ledger = empty_ledger(entries);
        ledger.set_rules(protocol::Rules::new(features));

        let tx = STTx::new(TxType::AMM_CLAWBACK, |tx| {
            tx.set_account_id(sf("sfAccount"), issuer);
            tx.set_account_id(sf("sfHolder"), holder);
            tx.set_field_issue(
                sf("sfAsset"),
                STIssue::new_with_asset(sf("sfAsset"), row.asset1),
            );
            tx.set_field_issue(
                sf("sfAsset2"),
                STIssue::new_with_asset(sf("sfAsset2"), row.asset2),
            );
            tx.set_field_amount(
                sf("sfFee"),
                STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
            );
            tx.set_field_u32(sf("sfSequence"), 1);
        });

        let mut view = ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE);
        let result = dispatch_with_pre_fee_balance(&mut view, &tx, TxType::AMM_CLAWBACK);
        assert_eq!(result, row.expected, "failed on: {}", row.desc);
    }
}
