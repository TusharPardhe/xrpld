use std::sync::Arc;

use app::state::invariants::{check_invariants, check_invariants_for_tx};
use basics::{
    base_uint::{Uint160, Uint192, Uint256},
    number::NumberParts as RuntimeNumber,
};
use ledger::{ApplyView, FlowSandbox, Ledger, LedgerHeader, Sandbox};
use protocol::{
    AccountID, ApplyFlags, Asset, Currency, IOUAmount, Issue, LedgerEntryType, MPTAmount, MPTIssue,
    Rules, STAmount, STIssue, STLedgerEntry, STNumber, STObject, STTx, Ter, TxType, XRPAmount,
    feature_id, get_field_by_symbol,
};

fn sf(name: &str) -> &'static protocol::SField {
    get_field_by_symbol(name)
}

fn acct(byte: u8) -> AccountID {
    AccountID::from_array([byte; 20])
}

fn raw_id(account: AccountID) -> Uint160 {
    Uint160::from_slice(account.data()).expect("account width")
}

fn iou_currency(tag: &[u8; 3]) -> Currency {
    let mut data = [0_u8; 20];
    data[12..15].copy_from_slice(tag);
    Currency::from(data)
}

fn test_ledger() -> Ledger {
    let mut ledger = Ledger::new(
        LedgerHeader {
            seq: 32,
            ..LedgerHeader::default()
        },
        false,
    );
    ledger.set_rules(Rules::new([feature_id("fixCleanup3_2_0")]));
    ledger
}

fn mpt_v2_ledger() -> Ledger {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("fixCleanup3_2_0"),
        feature_id("MPTokensV2"),
    ]));
    ledger
}

fn mpt_v2_without_cleanup_ledger() -> Ledger {
    let mut ledger = Ledger::new(
        LedgerHeader {
            seq: 32,
            ..LedgerHeader::default()
        },
        false,
    );
    ledger.set_rules(Rules::new([feature_id("MPTokensV2")]));
    ledger
}

fn lending_ledger() -> Ledger {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("fixCleanup3_2_0"),
        feature_id("LendingProtocol"),
    ]));
    ledger
}

fn lending_cleanup_ledger() -> Ledger {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("fixCleanup3_1_3"),
        feature_id("fixCleanup3_2_0"),
        feature_id("LendingProtocol"),
    ]));
    ledger
}

fn with_flow<R>(f: impl FnOnce(&mut FlowSandbox<Sandbox<Ledger>>) -> R) -> R {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    f(&mut flow)
}

fn amm_invariant_ledger() -> Ledger {
    let mut ledger = test_ledger();
    // ValidAMM::finalize gates its strict AMM checks on fixAMMv1_3.
    // fixCleanup3_2_0 alone must not change that amendment boundary.
    ledger.set_rules(Rules::new([
        feature_id("fixCleanup3_2_0"),
        feature_id("fixAMMv1_3"),
    ]));
    ledger
}

fn with_amm_invariant_flow<R>(f: impl FnOnce(&mut FlowSandbox<Sandbox<Ledger>>) -> R) -> R {
    let base = Arc::new(amm_invariant_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    f(&mut flow)
}

fn with_lending_flow<R>(f: impl FnOnce(&mut FlowSandbox<Sandbox<Ledger>>) -> R) -> R {
    let base = Arc::new(lending_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    f(&mut flow)
}

fn mpt_id(issuer: AccountID, sequence: u32) -> protocol::MPTID {
    protocol::make_mpt_id(sequence, issuer)
}

fn mptoken_entry(
    holder: AccountID,
    issuer: AccountID,
    sequence: u32,
    amount: u64,
) -> STLedgerEntry {
    mptoken_entry_with_flags(holder, issuer, sequence, amount, 0)
}

fn mptoken_entry_with_flags(
    holder: AccountID,
    issuer: AccountID,
    sequence: u32,
    amount: u64,
    flags: u32,
) -> STLedgerEntry {
    let id = mpt_id(issuer, sequence);
    let keylet = protocol::mptoken_keylet_from_mptid(id, raw_id(holder));
    let mut sle = STLedgerEntry::from_type_and_key(LedgerEntryType::MPToken, keylet.key);
    sle.set_account_id(sf("sfAccount"), holder);
    sle.set_field_h192(sf("sfMPTokenIssuanceID"), id);
    sle.set_field_u64(sf("sfMPTAmount"), amount);
    sle.set_field_u32(sf("sfFlags"), flags);
    sle.set_field_u64(sf("sfOwnerNode"), 0);
    sle
}

fn mpt_issuance_entry(
    issuer: AccountID,
    sequence: u32,
    outstanding: u64,
    flags: u32,
) -> STLedgerEntry {
    let id = mpt_id(issuer, sequence);
    let keylet = protocol::mpt_issuance_keylet_from_mptid(id);
    let mut sle = STLedgerEntry::from_type_and_key(LedgerEntryType::MPTokenIssuance, keylet.key);
    sle.set_account_id(sf("sfIssuer"), issuer);
    sle.set_field_u32(sf("sfSequence"), sequence);
    sle.set_field_u64(sf("sfOutstandingAmount"), outstanding);
    sle.set_field_u32(sf("sfFlags"), flags);
    sle.set_field_u64(sf("sfOwnerNode"), 0);
    sle
}

fn account_root(account: AccountID) -> STLedgerEntry {
    let mut sle = STLedgerEntry::from_type_and_key(
        LedgerEntryType::AccountRoot,
        protocol::account_keylet(raw_id(account)).key,
    );
    sle.set_account_id(sf("sfAccount"), account);
    sle.set_field_amount(
        sf("sfBalance"),
        STAmount::from_xrp_amount(XRPAmount::from_drops(0)),
    );
    sle.set_field_u32(sf("sfSequence"), 0);
    sle
}

fn amm_entry(
    key: u64,
    amm_account: AccountID,
    asset: Issue,
    asset2: Issue,
    lp_tokens: i64,
) -> STLedgerEntry {
    let mut sle = STLedgerEntry::from_type_and_key(LedgerEntryType::AMM, Uint256::from_u64(key));
    sle.set_account_id(sf("sfAccount"), amm_account);
    sle.set_field_issue(
        sf("sfAsset"),
        STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(asset)),
    );
    sle.set_field_issue(
        sf("sfAsset2"),
        STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(asset2)),
    );
    sle.set_field_amount(
        sf("sfLPTokenBalance"),
        STAmount::from_iou_amount(
            sf("sfLPTokenBalance"),
            IOUAmount::from_parts(lp_tokens, 0).expect("lp token amount"),
            asset,
        ),
    );
    sle
}

fn amm_entry_with_pool(
    key: u64,
    amm_account: AccountID,
    asset: Issue,
    asset2: Issue,
    amount: i64,
    amount2: i64,
    lp_tokens: i64,
) -> STLedgerEntry {
    let mut sle = amm_entry(key, amm_account, asset, asset2, lp_tokens);
    sle.set_field_amount(
        sf("sfAmount"),
        STAmount::from_iou_amount(
            sf("sfAmount"),
            IOUAmount::from_parts(amount, 0).expect("pool amount"),
            asset,
        ),
    );
    sle.set_field_amount(
        sf("sfAmount2"),
        STAmount::from_iou_amount(
            sf("sfAmount2"),
            IOUAmount::from_parts(amount2, 0).expect("pool amount2"),
            asset2,
        ),
    );
    sle
}

fn vault_pseudo_account_root(account: AccountID, vault_id: Uint256) -> STLedgerEntry {
    let mut sle = account_root(account);
    sle.set_field_h256(sf("sfVaultID"), vault_id);
    sle
}

fn iou_limit(field: &'static protocol::SField, currency: Currency, issuer: AccountID) -> STAmount {
    STAmount::from_iou_amount(
        field,
        IOUAmount::from_parts(0, 0).expect("zero iou"),
        Issue {
            currency,
            account: issuer,
        },
    )
}

fn ripple_state_entry(low_counterparty: AccountID, high_counterparty: AccountID) -> STLedgerEntry {
    let currency = iou_currency(b"USD");
    let keylet = protocol::line(low_counterparty, high_counterparty, currency);
    let mut sle = STLedgerEntry::from_type_and_key(LedgerEntryType::RippleState, keylet.key);
    sle.set_field_amount(
        sf("sfLowLimit"),
        iou_limit(sf("sfLowLimit"), currency, high_counterparty),
    );
    sle.set_field_amount(
        sf("sfHighLimit"),
        iou_limit(sf("sfHighLimit"), currency, low_counterparty),
    );
    sle
}

fn ripple_state_balance_entry(account: AccountID, issuer: AccountID, amount: i64) -> STLedgerEntry {
    let currency = iou_currency(b"USD");
    let keylet = protocol::line(account, issuer, currency);
    let mut sle = STLedgerEntry::from_type_and_key(LedgerEntryType::RippleState, keylet.key);
    sle.set_field_amount(
        sf("sfLowLimit"),
        iou_limit(sf("sfLowLimit"), currency, issuer),
    );
    sle.set_field_amount(
        sf("sfHighLimit"),
        iou_limit(sf("sfHighLimit"), currency, account),
    );
    let signed_amount = if account > issuer { -amount } else { amount };
    sle.set_field_amount(
        sf("sfBalance"),
        STAmount::from_iou_amount(
            sf("sfBalance"),
            IOUAmount::from_parts(signed_amount, 0).expect("iou balance"),
            Issue {
                currency,
                account: issuer,
            },
        ),
    );
    sle
}

fn mpt_issuance_with_reference(
    issuer: AccountID,
    sequence: u32,
    reference_holding: Uint256,
) -> STLedgerEntry {
    let mut sle = mpt_issuance_entry(issuer, sequence, 0, 0);
    sle.set_field_h256(sf("sfReferenceHolding"), reference_holding);
    sle
}

fn associated_number(asset: Asset, value: i64) -> STNumber {
    let mut number = STNumber::from(RuntimeNumber::from_i64(value));
    number.associate_asset(asset);
    number
}

fn vault_entry_with_values(
    key: Uint256,
    owner: AccountID,
    pseudo: AccountID,
    asset: Asset,
    share_mpt_id: MPTIssue,
    total: i64,
    available: i64,
    loss: i64,
) -> STLedgerEntry {
    let mut sle = STLedgerEntry::from_type_and_key(LedgerEntryType::Vault, key);
    sle.set_account_id(sf("sfOwner"), owner);
    sle.set_account_id(sf("sfAccount"), pseudo);
    sle.set_field_issue(sf("sfAsset"), STIssue::new_with_asset(sf("sfAsset"), asset));
    sle.set_field_number(sf("sfAssetsTotal"), associated_number(asset, total));
    sle.set_field_number(sf("sfAssetsAvailable"), associated_number(asset, available));
    sle.set_field_number(sf("sfLossUnrealized"), associated_number(asset, loss));
    sle.set_field_number(sf("sfAssetsMaximum"), associated_number(asset, 0));
    sle.set_field_h192(sf("sfShareMPTID"), share_mpt_id.mpt_id());
    sle
}

fn plain_number(value: i64) -> STNumber {
    STNumber::from(RuntimeNumber::from_i64(value))
}

fn loan_entry(
    key: Uint256,
    broker_id: Uint256,
    borrower: AccountID,
    payment_remaining: u32,
    total_value: i64,
    principal: i64,
    management_fee: i64,
    periodic_payment: i64,
    flags: u32,
) -> STLedgerEntry {
    let mut sle = STLedgerEntry::from_type_and_key(LedgerEntryType::Loan, key);
    sle.set_field_u64(sf("sfOwnerNode"), 0);
    sle.set_field_u64(sf("sfLoanBrokerNode"), 0);
    sle.set_field_h256(sf("sfLoanBrokerID"), broker_id);
    sle.set_field_u32(sf("sfLoanSequence"), 1);
    sle.set_account_id(sf("sfBorrower"), borrower);
    sle.set_field_u32(sf("sfStartDate"), 1);
    sle.set_field_u32(sf("sfPaymentInterval"), 1);
    sle.set_field_u32(sf("sfPaymentRemaining"), payment_remaining);
    sle.set_field_number(sf("sfTotalValueOutstanding"), plain_number(total_value));
    sle.set_field_number(sf("sfPrincipalOutstanding"), plain_number(principal));
    sle.set_field_number(
        sf("sfManagementFeeOutstanding"),
        plain_number(management_fee),
    );
    sle.set_field_number(sf("sfPeriodicPayment"), plain_number(periodic_payment));
    if flags != 0 {
        sle.set_field_u32(sf("sfFlags"), flags);
    }
    sle
}

fn loan_broker_entry(
    key: Uint256,
    owner: AccountID,
    pseudo: AccountID,
    vault_id: Uint256,
    loan_sequence: u32,
    debt_total: i64,
    cover_available: i64,
    owner_count: u32,
) -> STLedgerEntry {
    let mut sle = STLedgerEntry::from_type_and_key(LedgerEntryType::LoanBroker, key);
    sle.set_field_u32(sf("sfSequence"), 1);
    sle.set_field_u64(sf("sfOwnerNode"), 0);
    sle.set_field_u64(sf("sfVaultNode"), 0);
    sle.set_field_h256(sf("sfVaultID"), vault_id);
    sle.set_account_id(sf("sfAccount"), pseudo);
    sle.set_account_id(sf("sfOwner"), owner);
    sle.set_field_u32(sf("sfLoanSequence"), loan_sequence);
    sle.set_field_u32(sf("sfOwnerCount"), owner_count);
    sle.set_field_number(sf("sfDebtTotal"), plain_number(debt_total));
    sle.set_field_number(sf("sfCoverAvailable"), plain_number(cover_available));
    sle
}

fn offer_entry(
    key: Uint256,
    account: AccountID,
    flags: u32,
    domain: Option<Uint256>,
) -> STLedgerEntry {
    let mut sle = STLedgerEntry::from_type_and_key(LedgerEntryType::Offer, key);
    sle.set_account_id(sf("sfAccount"), account);
    sle.set_field_u32(sf("sfSequence"), 1);
    sle.set_field_amount(
        sf("sfTakerPays"),
        STAmount::from_xrp_amount(XRPAmount::from_drops(1)),
    );
    sle.set_field_amount(
        sf("sfTakerGets"),
        STAmount::from_iou_amount(
            sf("sfTakerGets"),
            IOUAmount::from_parts(2_000_000_000_000_000, -15)
                .expect("canonical invariant offer amount"),
            Issue::new(iou_currency(b"USD"), account),
        ),
    );
    if flags != 0 {
        sle.set_field_u32(sf("sfFlags"), flags);
    }
    if let Some(domain) = domain {
        sle.set_field_h256(sf("sfDomainID"), domain);
    }
    sle
}

fn set_additional_books(sle: &mut STLedgerEntry, len: usize) {
    let mut books = protocol::STArray::new(sf("sfAdditionalBooks"));
    for _ in 0..len {
        books.push_back(STObject::make_inner_object(sf("sfBook")));
    }
    sle.set_field_array(sf("sfAdditionalBooks"), books);
}

fn permissioned_domain_entry(domain: Uint256, owner: AccountID) -> STLedgerEntry {
    let mut sle = STLedgerEntry::from_type_and_key(
        LedgerEntryType::PermissionedDomain,
        protocol::permissioned_domain_keylet_from_id(domain).key,
    );
    sle.set_account_id(sf("sfOwner"), owner);
    sle.set_field_array(
        sf("sfAcceptedCredentials"),
        protocol::STArray::new(sf("sfAcceptedCredentials")),
    );
    sle.set_field_u64(sf("sfOwnerNode"), 0);
    sle
}

fn credential_entry(issuer: AccountID, credential_type: &[u8]) -> STObject {
    let mut credential = STObject::make_inner_object(sf("sfCredential"));
    credential.set_account_id(sf("sfIssuer"), issuer);
    credential.set_field_vl(sf("sfCredentialType"), credential_type);
    credential
}

fn credentials_array(items: &[(AccountID, &[u8])]) -> protocol::STArray {
    let mut credentials = protocol::STArray::new(sf("sfAcceptedCredentials"));
    for (issuer, credential_type) in items {
        credentials.push_back(credential_entry(*issuer, credential_type));
    }
    credentials
}

fn permissioned_domain_with_credentials(
    domain: Uint256,
    owner: AccountID,
    credentials: protocol::STArray,
) -> STLedgerEntry {
    let mut sle = permissioned_domain_entry(domain, owner);
    sle.set_field_array(sf("sfAcceptedCredentials"), credentials);
    sle
}

fn offer_create_tx(account: AccountID, domain: Option<Uint256>) -> STTx {
    STTx::new(TxType::OFFER_CREATE, move |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_field_u32(sf("sfSequence"), 1);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_amount(
            sf("sfTakerPays"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(1)),
        );
        tx.set_field_amount(
            sf("sfTakerGets"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(2)),
        );
        if let Some(domain) = domain {
            tx.set_field_h256(sf("sfDomainID"), domain);
        }
    })
}

fn cross_currency_payment_tx(
    account: AccountID,
    destination: AccountID,
    amount_issue: Issue,
    send_max_issue: Issue,
) -> STTx {
    STTx::new(TxType::PAYMENT, move |tx| {
        tx.set_account_id(sf("sfAccount"), account);
        tx.set_account_id(sf("sfDestination"), destination);
        tx.set_field_u32(sf("sfSequence"), 1);
        tx.set_field_amount(
            sf("sfFee"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(10)),
        );
        tx.set_field_amount(
            sf("sfAmount"),
            STAmount::from_iou_amount(
                sf("sfAmount"),
                IOUAmount::from_parts(10, 0).expect("amount"),
                amount_issue,
            ),
        );
        tx.set_field_amount(
            sf("sfSendMax"),
            STAmount::from_iou_amount(
                sf("sfSendMax"),
                IOUAmount::from_parts(11, 0).expect("send max"),
                send_max_issue,
            ),
        );
    })
}

#[test]
fn invariant_rejects_bad_book_directory_exchange_rate() {
    with_flow(|flow| {
        let mut key_bytes = [0_u8; 32];
        key_bytes[24..].copy_from_slice(&5_u64.to_be_bytes());
        let key = Uint256::from_array(key_bytes);
        let mut dir = STLedgerEntry::from_type_and_key(LedgerEntryType::DirectoryNode, key);
        dir.set_field_h256(sf("sfRootIndex"), key);
        dir.set_field_u64(sf("sfExchangeRate"), 7);

        flow.insert(Arc::new(dir)).expect("insert directory");
        assert_eq!(
            check_invariants(
                &flow,
                TxType::OFFER_CREATE,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_recovery_preserves_fee_claim_or_escalates_repeated_failure() {
    // After Transactor::reset has discarded doApply work, a valid fee/sequence
    // context keeps the original tecINVARIANT_FAILED result.
    with_flow(|flow| {
        assert_eq!(
            check_invariants(
                &flow,
                TxType::OFFER_CREATE,
                Ter::TEC_INVARIANT_FAILED,
                XRPAmount::from_drops(10),
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });

    // A second invariant violation in that fee-claim context is a hard tef
    // failure, matching ApplyContext::failInvariantCheck in rippled.
    with_flow(|flow| {
        let mut key_bytes = [0_u8; 32];
        key_bytes[24..].copy_from_slice(&6_u64.to_be_bytes());
        let key = Uint256::from_array(key_bytes);
        let mut dir = STLedgerEntry::from_type_and_key(LedgerEntryType::DirectoryNode, key);
        dir.set_field_h256(sf("sfRootIndex"), key);
        dir.set_field_u64(sf("sfExchangeRate"), 7);
        flow.insert(Arc::new(dir))
            .expect("insert malformed directory");

        assert_eq!(
            check_invariants(
                &flow,
                TxType::OFFER_CREATE,
                Ter::TEC_INVARIANT_FAILED,
                XRPAmount::from_drops(10),
            ),
            Ter::TEF_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_allows_deleted_bad_book_directory_exchange_rate() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut key_bytes = [0_u8; 32];
    key_bytes[24..].copy_from_slice(&5_u64.to_be_bytes());
    let key = Uint256::from_array(key_bytes);
    let mut dir = STLedgerEntry::from_type_and_key(LedgerEntryType::DirectoryNode, key);
    dir.set_field_h256(sf("sfRootIndex"), key);
    dir.set_field_u64(sf("sfExchangeRate"), 7);
    parent
        .insert(Arc::new(dir.clone()))
        .expect("insert directory");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.erase(Arc::new(dir)).expect("erase directory");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::OFFER_CREATE,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TES_SUCCESS
    );
}

#[test]
fn invariant_allows_unchanged_bad_book_directory_root_index() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut key_bytes = [0_u8; 32];
    key_bytes[24..].copy_from_slice(&5_u64.to_be_bytes());
    let key = Uint256::from_array(key_bytes);
    let mut before = STLedgerEntry::from_type_and_key(LedgerEntryType::DirectoryNode, key);
    before.set_field_h256(sf("sfRootIndex"), key);
    before.set_field_u64(sf("sfExchangeRate"), 7);
    parent
        .insert(Arc::new(before.clone()))
        .expect("insert directory");

    let mut after = before.clone();
    after.set_field_v256(
        sf("sfIndexes"),
        protocol::STVector256::from_values(sf("sfIndexes"), vec![Uint256::from_u64(99)]),
    );
    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(after)).expect("update directory");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::OFFER_CREATE,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TES_SUCCESS
    );
}

#[test]
fn invariant_rejects_permissioned_book_root_without_exchange_rate() {
    with_flow(|flow| {
        let key = Uint256::from_u64(6);
        let mut dir = STLedgerEntry::from_type_and_key(LedgerEntryType::DirectoryNode, key);
        dir.set_field_h256(sf("sfRootIndex"), key);
        dir.set_field_h256(sf("sfDomainID"), Uint256::from_u64(99));

        flow.insert(Arc::new(dir))
            .expect("insert permissioned directory");
        assert_eq!(
            check_invariants(
                &flow,
                TxType::OFFER_CREATE,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_mpt_book_root_without_exchange_rate() {
    with_flow(|flow| {
        let key = Uint256::from_u64(7);
        let mut dir = STLedgerEntry::from_type_and_key(LedgerEntryType::DirectoryNode, key);
        dir.set_field_h256(sf("sfRootIndex"), key);
        dir.set_field_h192(sf("sfTakerPaysMPT"), Uint192::from_array([0x44; 24]));

        flow.insert(Arc::new(dir)).expect("insert mpt directory");
        assert_eq!(
            check_invariants(
                flow,
                TxType::OFFER_CREATE,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_malformed_hybrid_offer() {
    with_flow(|flow| {
        let account = acct(0x13);
        let offer = offer_entry(Uint256::from_u64(13), account, protocol::lsfHybrid, None);

        flow.insert(Arc::new(offer)).expect("insert offer");
        assert_eq!(
            check_invariants(
                flow,
                TxType::OFFER_CREATE,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_allows_empty_hybrid_additional_books_before_cleanup_3_1_3() {
    // Later cleanup amendments are not a valid stand-in for the historical
    // pre-fixCleanup3_1_3 ruleset: fixCleanup3_2_0 also enables directory-root
    // integrity checks. Keep this fixture on the exact amendment boundary it
    // claims to exercise, as rippled's amendment tests do.
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([]));
    let base = Arc::new(ledger);
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    let account = acct(0x13);
    let domain = Uint256::from_u64(13);
    let mut offer = offer_entry(
        Uint256::from_u64(14),
        account,
        protocol::lsfHybrid,
        Some(domain),
    );
    set_additional_books(&mut offer, 0);

    flow.insert(Arc::new(offer)).expect("insert offer");
    assert_eq!(
        check_invariants(
            &flow,
            TxType::OFFER_CREATE,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TES_SUCCESS
    );
}

#[test]
fn invariant_rejects_empty_hybrid_additional_books_after_cleanup_3_1_3() {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("fixCleanup3_1_3"),
        feature_id("fixCleanup3_2_0"),
    ]));
    let base = Arc::new(ledger);
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    let account = acct(0x14);
    let domain = Uint256::from_u64(14);
    let mut offer = offer_entry(
        Uint256::from_u64(15),
        account,
        protocol::lsfHybrid,
        Some(domain),
    );
    set_additional_books(&mut offer, 0);

    flow.insert(Arc::new(offer)).expect("insert offer");
    assert_eq!(
        check_invariants(
            &flow,
            TxType::OFFER_CREATE,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_domain_offer_when_domain_entry_is_missing() {
    with_flow(|flow| {
        let account = acct(0x14);
        let domain = Uint256::from_u64(14);
        let offer = offer_entry(Uint256::from_u64(15), account, 0, Some(domain));

        flow.insert(Arc::new(offer)).expect("insert domain offer");
        assert_eq!(
            check_invariants_for_tx(
                flow,
                &offer_create_tx(account, Some(domain)),
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_domain_offercreate_that_affects_regular_offer() {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("fixCleanup3_1_3"),
        feature_id("fixCleanup3_2_0"),
    ]));
    let base = Arc::new(ledger);
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    let account = acct(0x15);
    let domain = Uint256::from_u64(16);

    flow.insert(Arc::new(permissioned_domain_entry(domain, account)))
        .expect("insert domain");
    flow.insert(Arc::new(offer_entry(
        Uint256::from_u64(17),
        account,
        0,
        None,
    )))
    .expect("insert regular offer");

    assert_eq!(
        check_invariants_for_tx(
            &flow,
            &offer_create_tx(account, Some(domain)),
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_allows_domain_offercreate_that_deletes_regular_offer_after_cleanup_3_2_0() {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("PermissionedDEX"),
        feature_id("fixCleanup3_1_3"),
        feature_id("fixCleanup3_2_0"),
    ]));
    let base = Arc::new(ledger);
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let account = acct(0x16);
    let domain = Uint256::from_u64(17);
    let offer = offer_entry(Uint256::from_u64(18), account, 0, None);

    parent
        .insert(Arc::new(permissioned_domain_entry(domain, account)))
        .expect("insert domain");
    parent
        .insert(Arc::new(offer.clone()))
        .expect("insert regular offer");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.erase(Arc::new(offer)).expect("erase regular offer");

    assert_eq!(
        check_invariants_for_tx(
            &flow,
            &offer_create_tx(account, Some(domain)),
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TES_SUCCESS
    );
}

#[test]
fn invariant_rejects_domain_offercreate_that_deletes_regular_offer_before_cleanup_3_2_0() {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("PermissionedDEX"),
        feature_id("fixCleanup3_1_3"),
    ]));
    let base = Arc::new(ledger);
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let account = acct(0x18);
    let domain = Uint256::from_u64(19);
    let offer = offer_entry(Uint256::from_u64(20), account, 0, None);

    parent
        .insert(Arc::new(permissioned_domain_entry(domain, account)))
        .expect("insert domain");
    parent
        .insert(Arc::new(offer.clone()))
        .expect("insert regular offer");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.erase(Arc::new(offer)).expect("erase regular offer");

    assert_eq!(
        check_invariants_for_tx(
            &flow,
            &offer_create_tx(account, Some(domain)),
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_permissioned_domain_set_with_empty_credentials() {
    with_flow(|flow| {
        let owner = acct(0x16);
        let domain = Uint256::from_u64(18);

        flow.insert(Arc::new(permissioned_domain_entry(domain, owner)))
            .expect("insert domain");

        assert_eq!(
            check_invariants(
                flow,
                TxType::PERMISSIONED_DOMAIN_SET,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_permissioned_domain_set_with_unsorted_credentials() {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("fixCleanup3_1_3"),
        feature_id("fixCleanup3_2_0"),
    ]));
    let base = Arc::new(ledger);
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    let owner = acct(0x17);
    let domain = Uint256::from_u64(19);
    let credentials = credentials_array(&[(acct(0x18), b"a"), (acct(0x17), b"a")]);

    flow.insert(Arc::new(permissioned_domain_with_credentials(
        domain,
        owner,
        credentials,
    )))
    .expect("insert domain");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PERMISSIONED_DOMAIN_SET,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_permissioned_domain_set_with_duplicate_credentials() {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("fixCleanup3_1_3"),
        feature_id("fixCleanup3_2_0"),
    ]));
    let base = Arc::new(ledger);
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    let owner = acct(0x19);
    let domain = Uint256::from_u64(20);
    let credentials = credentials_array(&[(acct(0x1A), b"a"), (acct(0x1A), b"a")]);

    flow.insert(Arc::new(permissioned_domain_with_credentials(
        domain,
        owner,
        credentials,
    )))
    .expect("insert domain");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PERMISSIONED_DOMAIN_SET,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_permissioned_domain_change_by_unauthorized_transaction() {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("fixCleanup3_1_3"),
        feature_id("fixCleanup3_2_0"),
    ]));
    let base = Arc::new(ledger);
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    let owner = acct(0x1B);
    let domain = Uint256::from_u64(21);
    let credentials = credentials_array(&[(acct(0x1C), b"a")]);

    flow.insert(Arc::new(permissioned_domain_with_credentials(
        domain,
        owner,
        credentials,
    )))
    .expect("insert domain");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PAYMENT,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_permissioned_domain_change_on_failed_transaction() {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("fixCleanup3_1_3"),
        feature_id("fixCleanup3_2_0"),
    ]));
    let base = Arc::new(ledger);
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    let owner = acct(0x1D);
    let domain = Uint256::from_u64(22);
    let credentials = credentials_array(&[(acct(0x1E), b"a")]);

    flow.insert(Arc::new(permissioned_domain_with_credentials(
        domain,
        owner,
        credentials,
    )))
    .expect("insert domain");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PERMISSIONED_DOMAIN_SET,
            Ter::TEC_CLAIM,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_failed_clawback_that_changes_trustline() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x51);
    let holder = acct(0x52);
    let before = ripple_state_balance_entry(holder, issuer, 10);
    parent
        .insert(Arc::new(before))
        .expect("insert parent trustline");
    let mut flow = FlowSandbox::new(&mut parent);
    let after = ripple_state_balance_entry(holder, issuer, 9);
    flow.update(Arc::new(after)).expect("update trustline");
    let currency = iou_currency(b"USD");
    let tx = STTx::new(TxType::CLAWBACK, |object| {
        object.set_account_id(sf("sfAccount"), issuer);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_iou_amount(
                sf("sfAmount"),
                IOUAmount::from_parts(1, 0).expect("clawback amount"),
                Issue {
                    currency,
                    account: holder,
                },
            ),
        );
    });

    assert_eq!(
        check_invariants_for_tx(
            &flow,
            &tx,
            Ter::TEC_NO_PERMISSION,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_directory_child_without_root() {
    with_flow(|flow| {
        let root = Uint256::from_u64(7);
        let child = Uint256::from_u64(8);
        let mut dir = STLedgerEntry::from_type_and_key(LedgerEntryType::DirectoryNode, child);
        dir.set_field_h256(sf("sfRootIndex"), root);

        flow.insert(Arc::new(dir)).expect("insert directory child");
        assert_eq!(
            check_invariants(
                flow,
                TxType::OFFER_CREATE,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_xrp_trustline_limit() {
    with_flow(|flow| {
        let low = acct(0x0A);
        let high = acct(0x0B);
        let mut line = ripple_state_entry(low, high);
        line.set_field_amount(
            sf("sfLowLimit"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(0)),
        );

        flow.insert(Arc::new(line)).expect("insert xrp trustline");

        assert_eq!(
            check_invariants(
                flow,
                TxType::TRUST_SET,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_deep_freeze_without_freeze_on_trustline() {
    with_flow(|flow| {
        let low = acct(0x0C);
        let high = acct(0x0D);
        let mut line = ripple_state_entry(low, high);
        line.set_field_u32(sf("sfFlags"), protocol::lsfLowDeepFreeze);

        flow.insert(Arc::new(line))
            .expect("insert bad deep-freeze trustline");

        assert_eq!(
            check_invariants(
                flow,
                TxType::TRUST_SET,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_mpt_holder_delta_without_outstanding_delta() {
    let base = Arc::new(mpt_v2_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    {
        let holder = acct(0x11);
        let issuer = acct(0x22);
        let before = mptoken_entry(holder, issuer, 1, 100);
        parent
            .insert(Arc::new(before))
            .expect("insert before token");

        let mut flow = FlowSandbox::new(&mut parent);
        let after = mptoken_entry(holder, issuer, 1, 90);
        flow.update(Arc::new(after)).expect("update after token");
        assert_eq!(
            check_invariants(
                &flow,
                TxType::PAYMENT,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    }
}

#[test]
fn invariant_allows_mpt_holder_transfer_without_can_transfer_before_mptokens_v2() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x21);
    let sender = acct(0x22);
    let receiver = acct(0x23);
    parent
        .insert(Arc::new(mpt_issuance_entry(issuer, 1, 100, 0)))
        .expect("insert issuance");
    parent
        .insert(Arc::new(mptoken_entry(sender, issuer, 1, 100)))
        .expect("insert sender token");
    parent
        .insert(Arc::new(mptoken_entry(receiver, issuer, 1, 0)))
        .expect("insert receiver token");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(mptoken_entry(sender, issuer, 1, 90)))
        .expect("update sender token");
    flow.update(Arc::new(mptoken_entry(receiver, issuer, 1, 10)))
        .expect("update receiver token");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PAYMENT,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TES_SUCCESS
    );
}

#[test]
fn invariant_rejects_mpt_holder_transfer_without_can_transfer_under_mptokens_v2() {
    let mut ledger = Ledger::new(
        LedgerHeader {
            seq: 32,
            ..LedgerHeader::default()
        },
        false,
    );
    ledger.set_rules(Rules::new([feature_id("MPTokensV2")]));
    let base = Arc::new(ledger);
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x20);
    let sender = acct(0x21);
    let receiver = acct(0x22);
    parent
        .insert(Arc::new(mpt_issuance_entry(issuer, 1, 100, 0)))
        .expect("insert issuance");
    parent
        .insert(Arc::new(mptoken_entry(sender, issuer, 1, 100)))
        .expect("insert sender token");
    parent
        .insert(Arc::new(mptoken_entry(receiver, issuer, 1, 0)))
        .expect("insert receiver token");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(mptoken_entry(sender, issuer, 1, 90)))
        .expect("update sender token");
    flow.update(Arc::new(mptoken_entry(receiver, issuer, 1, 10)))
        .expect("update receiver token");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PAYMENT,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_allows_recovery_path_mpt_transfer_without_can_transfer() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x24);
    let sender = acct(0x25);
    let receiver = acct(0x26);
    let owner = acct(0x27);
    let vault_id = Uint256::from_u64(260);
    let asset = Asset::Issue(Issue {
        currency: iou_currency(b"USD"),
        account: acct(0x28),
    });
    let vault = vault_entry_with_values(
        vault_id,
        owner,
        issuer,
        asset,
        MPTIssue::new(mpt_id(issuer, 1)),
        0,
        0,
        0,
    );
    parent
        .insert(Arc::new(mpt_issuance_entry(issuer, 1, 100, 0)))
        .expect("insert issuance");
    parent
        .insert(Arc::new(vault.clone()))
        .expect("insert vault");
    parent
        .insert(Arc::new(mptoken_entry(sender, issuer, 1, 100)))
        .expect("insert sender token");
    parent
        .insert(Arc::new(mptoken_entry(receiver, issuer, 1, 0)))
        .expect("insert receiver token");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(vault)).expect("update vault");
    flow.update(Arc::new(mptoken_entry(sender, issuer, 1, 90)))
        .expect("update sender token");
    flow.update(Arc::new(mptoken_entry(receiver, issuer, 1, 10)))
        .expect("update receiver token");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::LOAN_PAY,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TES_SUCCESS
    );
}

#[test]
fn invariant_rejects_dex_mpt_holder_transfer_without_can_trade() {
    let base = Arc::new(mpt_v2_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x27);
    let sender = acct(0x28);
    let receiver = acct(0x29);
    parent
        .insert(Arc::new(mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer,
        )))
        .expect("insert issuance");
    parent
        .insert(Arc::new(mptoken_entry(sender, issuer, 1, 100)))
        .expect("insert sender token");
    parent
        .insert(Arc::new(mptoken_entry(receiver, issuer, 1, 0)))
        .expect("insert receiver token");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(mptoken_entry(sender, issuer, 1, 90)))
        .expect("update sender token");
    flow.update(Arc::new(mptoken_entry(receiver, issuer, 1, 10)))
        .expect("update receiver token");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::OFFER_CREATE,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_cross_currency_payment_mpt_transfer_without_can_trade() {
    let base = Arc::new(mpt_v2_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x2A);
    let sender = acct(0x2B);
    let receiver = acct(0x2C);
    parent
        .insert(Arc::new(mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer,
        )))
        .expect("insert issuance");
    parent
        .insert(Arc::new(mptoken_entry(sender, issuer, 1, 100)))
        .expect("insert sender token");
    parent
        .insert(Arc::new(mptoken_entry(receiver, issuer, 1, 0)))
        .expect("insert receiver token");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(mptoken_entry(sender, issuer, 1, 90)))
        .expect("update sender token");
    flow.update(Arc::new(mptoken_entry(receiver, issuer, 1, 10)))
        .expect("update receiver token");

    let amount_issue = Issue {
        currency: iou_currency(b"USD"),
        account: issuer,
    };
    let send_max_issue = Issue {
        currency: iou_currency(b"EUR"),
        account: issuer,
    };
    let tx = cross_currency_payment_tx(sender, receiver, amount_issue, send_max_issue);

    assert_eq!(
        check_invariants_for_tx(&flow, &tx, Ter::TES_SUCCESS, XRPAmount::from_drops(10)),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_mpt_holder_transfer_when_issuance_locked() {
    let base = Arc::new(mpt_v2_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x3A);
    let sender = acct(0x3B);
    let receiver = acct(0x3C);
    parent
        .insert(Arc::new(mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTLocked,
        )))
        .expect("insert issuance");
    parent
        .insert(Arc::new(mptoken_entry(sender, issuer, 1, 100)))
        .expect("insert sender token");
    parent
        .insert(Arc::new(mptoken_entry(receiver, issuer, 1, 0)))
        .expect("insert receiver token");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(mptoken_entry(sender, issuer, 1, 90)))
        .expect("update sender token");
    flow.update(Arc::new(mptoken_entry(receiver, issuer, 1, 10)))
        .expect("update receiver token");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PAYMENT,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_mpt_holder_transfer_to_unauthorized_holder() {
    let base = Arc::new(mpt_v2_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x3D);
    let sender = acct(0x3E);
    let receiver = acct(0x3F);
    parent
        .insert(Arc::new(mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTRequireAuth,
        )))
        .expect("insert issuance");
    parent
        .insert(Arc::new(mptoken_entry_with_flags(
            sender,
            issuer,
            1,
            100,
            protocol::lsfMPTAuthorized,
        )))
        .expect("insert sender token");
    parent
        .insert(Arc::new(mptoken_entry(receiver, issuer, 1, 0)))
        .expect("insert receiver token");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(mptoken_entry_with_flags(
        sender,
        issuer,
        1,
        90,
        protocol::lsfMPTAuthorized,
    )))
    .expect("update sender token");
    flow.update(Arc::new(mptoken_entry(receiver, issuer, 1, 10)))
        .expect("update receiver token");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PAYMENT,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_allows_mpt_transfer_to_vault_pseudo_without_explicit_authorization() {
    let mut ledger = test_ledger();
    ledger.set_rules(Rules::new([
        feature_id("fixCleanup3_2_0"),
        feature_id("SingleAssetVault"),
    ]));
    let base = Arc::new(ledger);
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x4A);
    let sender = acct(0x4B);
    let pseudo = acct(0x4C);
    let vault_id = Uint256::from_u64(7040);

    parent
        .insert(Arc::new(vault_pseudo_account_root(pseudo, vault_id)))
        .expect("insert vault pseudo root");
    parent
        .insert(Arc::new(mpt_issuance_entry(
            issuer,
            1,
            100,
            protocol::lsfMPTCanTransfer | protocol::lsfMPTRequireAuth,
        )))
        .expect("insert issuance");
    parent
        .insert(Arc::new(mptoken_entry_with_flags(
            sender,
            issuer,
            1,
            100,
            protocol::lsfMPTAuthorized,
        )))
        .expect("insert sender token");
    parent
        .insert(Arc::new(mptoken_entry(pseudo, issuer, 1, 0)))
        .expect("insert pseudo token");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(mptoken_entry_with_flags(
        sender,
        issuer,
        1,
        90,
        protocol::lsfMPTAuthorized,
    )))
    .expect("update sender token");
    flow.update(Arc::new(mptoken_entry(pseudo, issuer, 1, 10)))
        .expect("update pseudo token");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PAYMENT,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TES_SUCCESS
    );
}

#[test]
fn invariant_rejects_unprivileged_mpt_issuance_creation() {
    with_flow(|flow| {
        let issuer = acct(0x18);
        flow.insert(Arc::new(mpt_issuance_entry(issuer, 1, 0, 0)))
            .expect("insert issuance");

        assert_eq!(
            check_invariants(
                flow,
                TxType::PAYMENT,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_allows_single_mpt_issuance_create_privilege() {
    with_flow(|flow| {
        let issuer = acct(0x19);
        flow.insert(Arc::new(mpt_issuance_entry(issuer, 1, 0, 0)))
            .expect("insert issuance");

        assert_eq!(
            check_invariants(
                flow,
                TxType::MPTOKEN_ISSUANCE_CREATE,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TES_SUCCESS
        );
    });
}

#[test]
fn invariant_rejects_unprivileged_mptoken_creation() {
    with_flow(|flow| {
        let issuer = acct(0x1A);
        let holder = acct(0x1B);
        flow.insert(Arc::new(mptoken_entry(holder, issuer, 1, 0)))
            .expect("insert token");

        assert_eq!(
            check_invariants(
                flow,
                TxType::TRUST_SET,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_allows_checkcash_single_mptoken_creation() {
    with_flow(|flow| {
        let issuer = acct(0x1C);
        let holder = acct(0x1D);
        flow.insert(Arc::new(mptoken_entry(holder, issuer, 1, 0)))
            .expect("insert token");

        assert_eq!(
            check_invariants(
                flow,
                TxType::CHECK_CASH,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TES_SUCCESS
        );
    });
}

#[test]
fn invariant_rejects_amm_clawback_two_mptoken_creations_with_mptokens_v2() {
    let base = Arc::new(mpt_v2_without_cleanup_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    let issuer = acct(0x1E);
    let holder_a = acct(0x1F);
    let holder_b = acct(0x20);

    flow.insert(Arc::new(mptoken_entry(holder_a, issuer, 1, 0)))
        .expect("insert first token");
    flow.insert(Arc::new(mptoken_entry(holder_b, issuer, 1, 0)))
        .expect("insert second token");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::AMM_CLAWBACK,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_allows_amm_clawback_one_mptoken_creation_with_mptokens_v2() {
    let base = Arc::new(mpt_v2_without_cleanup_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    let issuer = acct(0x1E);
    let holder = acct(0x1F);

    flow.insert(Arc::new(mptoken_entry(holder, issuer, 1, 0)))
        .expect("insert token");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::AMM_CLAWBACK,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TES_SUCCESS
    );
}

#[test]
fn invariant_rejects_reference_holding_on_non_vault_create_issuance() {
    with_flow(|flow| {
        let issuer = acct(0x2A);
        flow.insert(Arc::new(mpt_issuance_with_reference(
            issuer,
            1,
            Uint256::from_u64(99),
        )))
        .expect("insert issuance");

        assert_eq!(
            check_invariants(
                flow,
                TxType::PAYMENT,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_allows_reference_holding_on_vault_create_issuance() {
    with_flow(|flow| {
        let issuer = acct(0x2B);
        let owner = acct(0x2C);
        let asset = Asset::Issue(Issue {
            currency: iou_currency(b"USD"),
            account: acct(0x2D),
        });
        let vault_id = Uint256::from_u64(99);
        flow.insert(Arc::new(vault_pseudo_account_root(issuer, vault_id)))
            .expect("insert pseudo root");
        flow.insert(Arc::new(vault_entry_with_values(
            vault_id,
            owner,
            issuer,
            asset,
            MPTIssue::new(mpt_id(issuer, 1)),
            0,
            0,
            0,
        )))
        .expect("insert vault");
        flow.insert(Arc::new(mpt_issuance_with_reference(issuer, 1, vault_id)))
            .expect("insert issuance");

        assert_eq!(
            check_invariants(
                flow,
                TxType::VAULT_CREATE,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TES_SUCCESS
        );
    });
}

#[test]
fn invariant_rejects_reference_holding_mutation() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x2C);
    parent
        .insert(Arc::new(mpt_issuance_with_reference(
            issuer,
            1,
            Uint256::from_u64(1),
        )))
        .expect("insert issuance");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(mpt_issuance_with_reference(
        issuer,
        1,
        Uint256::from_u64(2),
    )))
    .expect("update issuance");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::VAULT_SET,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_vault_pseudo_mpt_holding_deleted_by_non_vault_delete() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x2D);
    let pseudo = acct(0x2E);
    let vault_id = Uint256::from_u64(700);
    let token = mptoken_entry(pseudo, issuer, 1, 0);
    parent
        .insert(Arc::new(vault_pseudo_account_root(pseudo, vault_id)))
        .expect("insert pseudo root");
    parent
        .insert(Arc::new(token.clone()))
        .expect("insert mptoken");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.erase(Arc::new(token)).expect("erase mptoken");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PAYMENT,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_allows_vault_pseudo_mpt_holding_deleted_by_vault_delete() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x2F);
    let pseudo = acct(0x30);
    let vault_id = Uint256::from_u64(701);
    let asset = Asset::Issue(Issue {
        currency: iou_currency(b"USD"),
        account: acct(0x31),
    });
    let vault = vault_entry_with_values(
        vault_id,
        acct(0x32),
        pseudo,
        asset,
        MPTIssue::new(mpt_id(issuer, 1)),
        0,
        0,
        0,
    );
    let issuance = mpt_issuance_entry(issuer, 1, 0, 0);
    let token = mptoken_entry(pseudo, issuer, 1, 0);
    let pseudo_root = vault_pseudo_account_root(pseudo, vault_id);
    parent
        .insert(Arc::new(pseudo_root.clone()))
        .expect("insert pseudo root");
    parent
        .insert(Arc::new(vault.clone()))
        .expect("insert vault");
    parent
        .insert(Arc::new(issuance.clone()))
        .expect("insert issuance");
    parent
        .insert(Arc::new(token.clone()))
        .expect("insert mptoken");

    let mut flow = FlowSandbox::new(&mut parent);
    // A successful rippled VaultDelete has MustDeleteAcct privilege and must
    // delete exactly the vault pseudo AccountRoot along with the vault and its
    // share issuance. Omitting this made the fixture itself invariant-invalid.
    flow.erase(Arc::new(pseudo_root))
        .expect("erase pseudo root");
    flow.erase(Arc::new(vault)).expect("erase vault");
    flow.erase(Arc::new(issuance)).expect("erase issuance");
    flow.erase(Arc::new(token)).expect("erase mptoken");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::VAULT_DELETE,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TES_SUCCESS
    );
}

#[test]
fn invariant_rejects_vault_pseudo_ripple_state_deleted_by_non_vault_delete() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let pseudo = acct(0x31);
    let peer = acct(0x32);
    let vault_id = Uint256::from_u64(702);
    let line = ripple_state_entry(peer, pseudo);
    parent
        .insert(Arc::new(vault_pseudo_account_root(pseudo, vault_id)))
        .expect("insert pseudo root");
    parent
        .insert(Arc::new(line.clone()))
        .expect("insert ripple state");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.erase(Arc::new(line)).expect("erase ripple state");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::TRUST_SET,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_vault_available_above_total() {
    with_flow(|flow| {
        let owner = acct(0x33);
        let issuer = acct(0x44);
        let issue = Issue {
            currency: iou_currency(b"USD"),
            account: issuer,
        };
        let asset = Asset::Issue(issue);
        let mut vault =
            STLedgerEntry::from_type_and_key(LedgerEntryType::Vault, Uint256::from_u64(9));
        vault.set_account_id(sf("sfOwner"), owner);
        vault.set_account_id(sf("sfAccount"), acct(0x55));
        vault.set_field_issue(sf("sfAsset"), STIssue::new_with_asset(sf("sfAsset"), asset));
        vault.set_field_number(sf("sfAssetsTotal"), associated_number(asset, 10));
        vault.set_field_number(sf("sfAssetsAvailable"), associated_number(asset, 11));
        vault.set_field_number(sf("sfLossUnrealized"), associated_number(asset, 0));
        vault.set_field_h192(sf("sfShareMPTID"), mpt_id(acct(0x55), 1));

        flow.insert(Arc::new(vault)).expect("insert vault");
        assert_eq!(
            check_invariants(
                flow,
                TxType::VAULT_DEPOSIT,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_vault_unrealized_loss_above_unavailable_assets() {
    with_flow(|flow| {
        let owner = acct(0x34);
        let issuer = acct(0x45);
        let issue = Issue {
            currency: iou_currency(b"USD"),
            account: issuer,
        };
        let asset = Asset::Issue(issue);
        let mut vault =
            STLedgerEntry::from_type_and_key(LedgerEntryType::Vault, Uint256::from_u64(16));
        vault.set_account_id(sf("sfOwner"), owner);
        vault.set_account_id(sf("sfAccount"), acct(0x56));
        vault.set_field_issue(sf("sfAsset"), STIssue::new_with_asset(sf("sfAsset"), asset));
        vault.set_field_number(sf("sfAssetsTotal"), associated_number(asset, 10));
        vault.set_field_number(sf("sfAssetsAvailable"), associated_number(asset, 8));
        vault.set_field_number(sf("sfLossUnrealized"), associated_number(asset, 3));
        vault.set_field_h192(sf("sfShareMPTID"), mpt_id(acct(0x56), 1));

        flow.insert(Arc::new(vault)).expect("insert vault");
        assert_eq!(
            check_invariants(
                flow,
                TxType::VAULT_SET,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_vault_total_above_positive_assets_maximum() {
    with_flow(|flow| {
        let owner = acct(0x35);
        let issuer = acct(0x46);
        let issue = Issue {
            currency: iou_currency(b"USD"),
            account: issuer,
        };
        let asset = Asset::Issue(issue);
        let mut vault =
            STLedgerEntry::from_type_and_key(LedgerEntryType::Vault, Uint256::from_u64(17));
        vault.set_account_id(sf("sfOwner"), owner);
        vault.set_account_id(sf("sfAccount"), acct(0x57));
        vault.set_field_issue(sf("sfAsset"), STIssue::new_with_asset(sf("sfAsset"), asset));
        vault.set_field_number(sf("sfAssetsTotal"), associated_number(asset, 11));
        vault.set_field_number(sf("sfAssetsAvailable"), associated_number(asset, 11));
        vault.set_field_number(sf("sfLossUnrealized"), associated_number(asset, 0));
        vault.set_field_number(sf("sfAssetsMaximum"), associated_number(asset, 10));
        vault.set_field_h192(sf("sfShareMPTID"), mpt_id(acct(0x57), 1));

        flow.insert(Arc::new(vault)).expect("insert vault");
        assert_eq!(
            check_invariants(
                flow,
                TxType::VAULT_SET,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_vault_update_by_non_vault_transaction() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let owner = acct(0x71);
    let pseudo = acct(0x72);
    let issuer = acct(0x73);
    let asset = Asset::Issue(Issue {
        currency: iou_currency(b"USD"),
        account: issuer,
    });
    let share_mpt_id = MPTIssue::new(mpt_id(pseudo, 1));
    let key = Uint256::from_u64(710);
    parent
        .insert(Arc::new(vault_entry_with_values(
            key,
            owner,
            pseudo,
            asset,
            share_mpt_id,
            10,
            10,
            0,
        )))
        .expect("insert before vault");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(vault_entry_with_values(
        key,
        owner,
        pseudo,
        asset,
        share_mpt_id,
        11,
        11,
        0,
    )))
    .expect("update vault");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PAYMENT,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_vault_set_without_share_issuance() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let owner = acct(0x74);
    let pseudo = acct(0x75);
    let issuer = acct(0x76);
    let asset = Asset::Issue(Issue {
        currency: iou_currency(b"USD"),
        account: issuer,
    });
    let share_mpt_id = MPTIssue::new(mpt_id(pseudo, 1));
    let key = Uint256::from_u64(711);
    parent
        .insert(Arc::new(vault_entry_with_values(
            key,
            owner,
            pseudo,
            asset,
            share_mpt_id,
            10,
            10,
            0,
        )))
        .expect("insert before vault");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(vault_entry_with_values(
        key,
        owner,
        pseudo,
        asset,
        share_mpt_id,
        10,
        10,
        0,
    )))
    .expect("update vault");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::VAULT_SET,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_vault_set_share_outstanding_change() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let owner = acct(0x80);
    let pseudo = acct(0x81);
    let asset_issuer = acct(0x82);
    let holder = acct(0x83);
    let asset = Asset::Issue(Issue {
        currency: iou_currency(b"USD"),
        account: asset_issuer,
    });
    let share_mpt_id = MPTIssue::new(mpt_id(pseudo, 1));
    let key = Uint256::from_u64(714);
    parent
        .insert(Arc::new(vault_entry_with_values(
            key,
            owner,
            pseudo,
            asset,
            share_mpt_id,
            10,
            10,
            0,
        )))
        .expect("insert before vault");
    parent
        .insert(Arc::new(mpt_issuance_entry(pseudo, 1, 10, 0)))
        .expect("insert share issuance");
    parent
        .insert(Arc::new(mptoken_entry(holder, pseudo, 1, 10)))
        .expect("insert holder shares");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(vault_entry_with_values(
        key,
        owner,
        pseudo,
        asset,
        share_mpt_id,
        10,
        10,
        0,
    )))
    .expect("update vault");
    flow.update(Arc::new(mpt_issuance_entry(pseudo, 1, 11, 0)))
        .expect("update share issuance");
    flow.update(Arc::new(mptoken_entry(holder, pseudo, 1, 11)))
        .expect("update holder shares");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::VAULT_SET,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_vault_deposit_without_depositor_share_increase() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let owner = acct(0x84);
    let pseudo = acct(0x85);
    let asset_issuer = acct(0x86);
    let depositor = acct(0x87);
    let other = acct(0x88);
    let issue = Issue {
        currency: iou_currency(b"USD"),
        account: asset_issuer,
    };
    let asset = Asset::Issue(issue);
    let share_mpt_id = MPTIssue::new(mpt_id(pseudo, 1));
    let key = Uint256::from_u64(715);
    parent
        .insert(Arc::new(vault_entry_with_values(
            key,
            owner,
            pseudo,
            asset,
            share_mpt_id,
            10,
            10,
            0,
        )))
        .expect("insert before vault");
    parent
        .insert(Arc::new(mpt_issuance_entry(pseudo, 1, 10, 0)))
        .expect("insert share issuance");
    parent
        .insert(Arc::new(mptoken_entry(depositor, pseudo, 1, 10)))
        .expect("insert depositor shares");
    parent
        .insert(Arc::new(mptoken_entry(other, pseudo, 1, 0)))
        .expect("insert other shares");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(vault_entry_with_values(
        key,
        owner,
        pseudo,
        asset,
        share_mpt_id,
        11,
        11,
        0,
    )))
    .expect("update vault");
    flow.update(Arc::new(mpt_issuance_entry(pseudo, 1, 11, 0)))
        .expect("update share issuance");
    flow.update(Arc::new(mptoken_entry(other, pseudo, 1, 1)))
        .expect("update other shares");

    let tx = STTx::new(TxType::VAULT_DEPOSIT, move |object| {
        object.set_account_id(sf("sfAccount"), depositor);
        object.set_field_h256(sf("sfVaultID"), key);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_iou_amount(
                sf("sfAmount"),
                IOUAmount::from_parts(1, 0).expect("amount"),
                issue,
            ),
        );
    });

    assert_eq!(
        check_invariants_for_tx(&flow, &tx, Ter::TES_SUCCESS, XRPAmount::from_drops(10)),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_vault_deposit_without_matching_depositor_asset_decrease() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let owner = acct(0x85);
    let pseudo = acct(0x86);
    let asset_issuer = acct(0x87);
    let depositor = acct(0x88);
    let issue = Issue {
        currency: iou_currency(b"USD"),
        account: asset_issuer,
    };
    let asset = Asset::Issue(issue);
    let share_mpt_id = MPTIssue::new(mpt_id(pseudo, 1));
    let key = Uint256::from_u64(1715);
    parent
        .insert(Arc::new(vault_entry_with_values(
            key,
            owner,
            pseudo,
            asset,
            share_mpt_id,
            10,
            10,
            0,
        )))
        .expect("insert before vault");
    parent
        .insert(Arc::new(mpt_issuance_entry(pseudo, 1, 10, 0)))
        .expect("insert share issuance");
    parent
        .insert(Arc::new(mptoken_entry(depositor, pseudo, 1, 10)))
        .expect("insert depositor shares");
    parent
        .insert(Arc::new(ripple_state_balance_entry(
            depositor,
            asset_issuer,
            10,
        )))
        .expect("insert depositor trustline");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(vault_entry_with_values(
        key,
        owner,
        pseudo,
        asset,
        share_mpt_id,
        11,
        11,
        0,
    )))
    .expect("update vault");
    flow.update(Arc::new(mpt_issuance_entry(pseudo, 1, 11, 0)))
        .expect("update share issuance");
    flow.update(Arc::new(mptoken_entry(depositor, pseudo, 1, 11)))
        .expect("update depositor shares");

    let tx = STTx::new(TxType::VAULT_DEPOSIT, move |object| {
        object.set_account_id(sf("sfAccount"), depositor);
        object.set_field_h256(sf("sfVaultID"), key);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_iou_amount(
                sf("sfAmount"),
                IOUAmount::from_parts(1, 0).expect("amount"),
                issue,
            ),
        );
    });

    assert_eq!(
        check_invariants_for_tx(&flow, &tx, Ter::TES_SUCCESS, XRPAmount::from_drops(10)),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_vault_deposit_without_matching_pseudo_asset_increase() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let owner = acct(0xA0);
    let pseudo = acct(0xA1);
    let asset_issuer = acct(0xA2);
    let depositor = acct(0xA3);
    let issue = Issue {
        currency: iou_currency(b"USD"),
        account: asset_issuer,
    };
    let asset = Asset::Issue(issue);
    let share_mpt_id = MPTIssue::new(mpt_id(pseudo, 1));
    let key = Uint256::from_u64(3715);
    parent
        .insert(Arc::new(vault_entry_with_values(
            key,
            owner,
            pseudo,
            asset,
            share_mpt_id,
            10,
            10,
            0,
        )))
        .expect("insert before vault");
    parent
        .insert(Arc::new(mpt_issuance_entry(pseudo, 1, 10, 0)))
        .expect("insert share issuance");
    parent
        .insert(Arc::new(mptoken_entry(depositor, pseudo, 1, 10)))
        .expect("insert depositor shares");
    parent
        .insert(Arc::new(ripple_state_balance_entry(
            pseudo,
            asset_issuer,
            10,
        )))
        .expect("insert pseudo trustline");
    parent
        .insert(Arc::new(ripple_state_balance_entry(
            depositor,
            asset_issuer,
            10,
        )))
        .expect("insert depositor trustline");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(vault_entry_with_values(
        key,
        owner,
        pseudo,
        asset,
        share_mpt_id,
        11,
        11,
        0,
    )))
    .expect("update vault");
    flow.update(Arc::new(mpt_issuance_entry(pseudo, 1, 11, 0)))
        .expect("update share issuance");
    flow.update(Arc::new(mptoken_entry(depositor, pseudo, 1, 11)))
        .expect("update depositor shares");
    flow.update(Arc::new(ripple_state_balance_entry(
        depositor,
        asset_issuer,
        9,
    )))
    .expect("update depositor trustline");

    let tx = STTx::new(TxType::VAULT_DEPOSIT, move |object| {
        object.set_account_id(sf("sfAccount"), depositor);
        object.set_field_h256(sf("sfVaultID"), key);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_iou_amount(
                sf("sfAmount"),
                IOUAmount::from_parts(1, 0).expect("amount"),
                issue,
            ),
        );
    });

    assert_eq!(
        check_invariants_for_tx(&flow, &tx, Ter::TES_SUCCESS, XRPAmount::from_drops(10)),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_vault_withdraw_without_account_share_decrease() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let owner = acct(0x89);
    let pseudo = acct(0x8A);
    let asset_issuer = acct(0x8B);
    let account = acct(0x8C);
    let other = acct(0x8D);
    let issue = Issue {
        currency: iou_currency(b"USD"),
        account: asset_issuer,
    };
    let asset = Asset::Issue(issue);
    let share_mpt_id = MPTIssue::new(mpt_id(pseudo, 1));
    let key = Uint256::from_u64(716);
    parent
        .insert(Arc::new(vault_entry_with_values(
            key,
            owner,
            pseudo,
            asset,
            share_mpt_id,
            10,
            10,
            0,
        )))
        .expect("insert before vault");
    parent
        .insert(Arc::new(mpt_issuance_entry(pseudo, 1, 10, 0)))
        .expect("insert share issuance");
    parent
        .insert(Arc::new(mptoken_entry(account, pseudo, 1, 10)))
        .expect("insert account shares");
    parent
        .insert(Arc::new(mptoken_entry(other, pseudo, 1, 1)))
        .expect("insert other shares");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(vault_entry_with_values(
        key,
        owner,
        pseudo,
        asset,
        share_mpt_id,
        9,
        9,
        0,
    )))
    .expect("update vault");
    flow.update(Arc::new(mpt_issuance_entry(pseudo, 1, 9, 0)))
        .expect("update share issuance");
    flow.update(Arc::new(mptoken_entry(other, pseudo, 1, 0)))
        .expect("update other shares");

    let tx = STTx::new(TxType::VAULT_WITHDRAW, move |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_field_h256(sf("sfVaultID"), key);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_iou_amount(
                sf("sfAmount"),
                IOUAmount::from_parts(1, 0).expect("amount"),
                issue,
            ),
        );
    });

    assert_eq!(
        check_invariants_for_tx(&flow, &tx, Ter::TES_SUCCESS, XRPAmount::from_drops(10)),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_vault_withdraw_without_matching_destination_asset_increase() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let owner = acct(0xA4);
    let pseudo = acct(0xA5);
    let asset_issuer = acct(0xA6);
    let account = acct(0xA7);
    let destination = acct(0xA8);
    let issue = Issue {
        currency: iou_currency(b"USD"),
        account: asset_issuer,
    };
    let asset = Asset::Issue(issue);
    let share_mpt_id = MPTIssue::new(mpt_id(pseudo, 1));
    let key = Uint256::from_u64(3716);
    parent
        .insert(Arc::new(vault_entry_with_values(
            key,
            owner,
            pseudo,
            asset,
            share_mpt_id,
            10,
            10,
            0,
        )))
        .expect("insert before vault");
    parent
        .insert(Arc::new(mpt_issuance_entry(pseudo, 1, 10, 0)))
        .expect("insert share issuance");
    parent
        .insert(Arc::new(mptoken_entry(account, pseudo, 1, 10)))
        .expect("insert account shares");
    parent
        .insert(Arc::new(ripple_state_balance_entry(
            pseudo,
            asset_issuer,
            10,
        )))
        .expect("insert pseudo trustline");
    parent
        .insert(Arc::new(ripple_state_balance_entry(
            destination,
            asset_issuer,
            0,
        )))
        .expect("insert destination trustline");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(vault_entry_with_values(
        key,
        owner,
        pseudo,
        asset,
        share_mpt_id,
        9,
        9,
        0,
    )))
    .expect("update vault");
    flow.update(Arc::new(mpt_issuance_entry(pseudo, 1, 9, 0)))
        .expect("update share issuance");
    flow.update(Arc::new(mptoken_entry(account, pseudo, 1, 9)))
        .expect("update account shares");
    flow.update(Arc::new(ripple_state_balance_entry(
        pseudo,
        asset_issuer,
        9,
    )))
    .expect("update pseudo trustline");

    let tx = STTx::new(TxType::VAULT_WITHDRAW, move |object| {
        object.set_account_id(sf("sfAccount"), account);
        object.set_account_id(sf("sfDestination"), destination);
        object.set_field_h256(sf("sfVaultID"), key);
        object.set_field_amount(
            sf("sfAmount"),
            STAmount::from_iou_amount(
                sf("sfAmount"),
                IOUAmount::from_parts(1, 0).expect("amount"),
                issue,
            ),
        );
    });

    assert_eq!(
        check_invariants_for_tx(&flow, &tx, Ter::TES_SUCCESS, XRPAmount::from_drops(10)),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_vault_clawback_without_holder_share_decrease() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let owner = acct(0x8E);
    let pseudo = acct(0x8F);
    let asset_issuer = acct(0x90);
    let holder = acct(0x91);
    let other = acct(0x92);
    let issue = Issue {
        currency: iou_currency(b"USD"),
        account: asset_issuer,
    };
    let asset = Asset::Issue(issue);
    let share_mpt_id = MPTIssue::new(mpt_id(pseudo, 1));
    let key = Uint256::from_u64(717);
    parent
        .insert(Arc::new(vault_entry_with_values(
            key,
            owner,
            pseudo,
            asset,
            share_mpt_id,
            10,
            10,
            0,
        )))
        .expect("insert before vault");
    parent
        .insert(Arc::new(mpt_issuance_entry(pseudo, 1, 10, 0)))
        .expect("insert share issuance");
    parent
        .insert(Arc::new(mptoken_entry(holder, pseudo, 1, 10)))
        .expect("insert holder shares");
    parent
        .insert(Arc::new(mptoken_entry(other, pseudo, 1, 1)))
        .expect("insert other shares");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(vault_entry_with_values(
        key,
        owner,
        pseudo,
        asset,
        share_mpt_id,
        9,
        9,
        0,
    )))
    .expect("update vault");
    flow.update(Arc::new(mpt_issuance_entry(pseudo, 1, 9, 0)))
        .expect("update share issuance");
    flow.update(Arc::new(mptoken_entry(other, pseudo, 1, 0)))
        .expect("update other shares");

    let tx = STTx::new(TxType::VAULT_CLAWBACK, move |object| {
        object.set_account_id(sf("sfAccount"), asset_issuer);
        object.set_account_id(sf("sfHolder"), holder);
        object.set_field_h256(sf("sfVaultID"), key);
    });

    assert_eq!(
        check_invariants_for_tx(&flow, &tx, Ter::TES_SUCCESS, XRPAmount::from_drops(10)),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_vault_create_without_pseudo_account_backlink() {
    with_flow(|flow| {
        let owner = acct(0x77);
        let pseudo = acct(0x78);
        let issuer = acct(0x79);
        let asset = Asset::Issue(Issue {
            currency: iou_currency(b"USD"),
            account: issuer,
        });
        let share_mpt_id = MPTIssue::new(mpt_id(pseudo, 1));
        let key = Uint256::from_u64(712);

        flow.insert(Arc::new(vault_entry_with_values(
            key,
            owner,
            pseudo,
            asset,
            share_mpt_id,
            0,
            0,
            0,
        )))
        .expect("insert vault");
        flow.insert(Arc::new(mpt_issuance_entry(pseudo, 1, 0, 0)))
            .expect("insert share issuance");

        assert_eq!(
            check_invariants(
                flow,
                TxType::VAULT_CREATE,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_vault_delete_with_unrelated_share_deletion() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let owner = acct(0x7A);
    let pseudo = acct(0x7B);
    let issuer = acct(0x7C);
    let asset = Asset::Issue(Issue {
        currency: iou_currency(b"USD"),
        account: issuer,
    });
    let share_mpt_id = MPTIssue::new(mpt_id(pseudo, 1));
    let key = Uint256::from_u64(713);
    let vault = vault_entry_with_values(key, owner, pseudo, asset, share_mpt_id, 0, 0, 0);
    let unrelated = mpt_issuance_entry(pseudo, 2, 0, 0);
    parent
        .insert(Arc::new(vault.clone()))
        .expect("insert before vault");
    parent
        .insert(Arc::new(unrelated.clone()))
        .expect("insert unrelated issuance");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.erase(Arc::new(vault)).expect("erase vault");
    flow.erase(Arc::new(unrelated))
        .expect("erase unrelated issuance");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::VAULT_DELETE,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_loan_zero_payments_with_outstanding_value() {
    with_lending_flow(|flow| {
        let loan = loan_entry(
            Uint256::from_u64(18),
            Uint256::from_u64(19),
            acct(0x58),
            0,
            1,
            1,
            0,
            1,
            0,
        );

        flow.insert(Arc::new(loan)).expect("insert loan");
        assert_eq!(
            check_invariants(
                flow,
                TxType::LOAN_PAY,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_fully_paid_loan_with_payments_remaining() {
    with_lending_flow(|flow| {
        let loan = loan_entry(
            Uint256::from_u64(20),
            Uint256::from_u64(21),
            acct(0x59),
            1,
            0,
            0,
            0,
            1,
            0,
        );

        flow.insert(Arc::new(loan)).expect("insert loan");
        assert_eq!(
            check_invariants(
                flow,
                TxType::LOAN_PAY,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_loan_overpayment_flag_change() {
    let base = Arc::new(lending_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let key = Uint256::from_u64(22);
    let broker = Uint256::from_u64(23);
    let borrower = acct(0x5A);
    parent
        .insert(Arc::new(loan_entry(
            key,
            broker,
            borrower,
            1,
            1,
            1,
            0,
            1,
            protocol::lsfLoanOverpayment,
        )))
        .expect("insert before loan");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(loan_entry(
        key, broker, borrower, 1, 1, 1, 0, 1, 0,
    )))
    .expect("update loan");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::LOAN_PAY,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_loan_with_non_positive_periodic_payment() {
    with_lending_flow(|flow| {
        let loan = loan_entry(
            Uint256::from_u64(24),
            Uint256::from_u64(25),
            acct(0x5B),
            1,
            1,
            1,
            0,
            0,
            0,
        );

        flow.insert(Arc::new(loan)).expect("insert loan");
        assert_eq!(
            check_invariants(
                flow,
                TxType::LOAN_SET,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_loan_broker_with_missing_vault() {
    with_lending_flow(|flow| {
        let broker = loan_broker_entry(
            Uint256::from_u64(26),
            acct(0x5C),
            acct(0x5D),
            Uint256::from_u64(27),
            1,
            0,
            0,
            0,
        );

        flow.insert(Arc::new(broker)).expect("insert broker");
        assert_eq!(
            check_invariants(
                flow,
                TxType::LOAN_BROKER_SET,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_loan_broker_sequence_decrease() {
    let base = Arc::new(lending_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let vault_id = Uint256::from_u64(28);
    let broker_id = Uint256::from_u64(29);
    let owner = acct(0x5E);
    let pseudo = acct(0x5F);
    let issuer = acct(0x60);
    let issue = Issue {
        currency: iou_currency(b"USD"),
        account: issuer,
    };
    let asset = Asset::Issue(issue);
    let mut vault = STLedgerEntry::from_type_and_key(LedgerEntryType::Vault, vault_id);
    vault.set_account_id(sf("sfOwner"), owner);
    vault.set_account_id(sf("sfAccount"), acct(0x61));
    vault.set_field_issue(sf("sfAsset"), STIssue::new_with_asset(sf("sfAsset"), asset));
    vault.set_field_number(sf("sfAssetsTotal"), associated_number(asset, 0));
    vault.set_field_number(sf("sfAssetsAvailable"), associated_number(asset, 0));
    vault.set_field_number(sf("sfLossUnrealized"), associated_number(asset, 0));
    vault.set_field_h192(sf("sfShareMPTID"), mpt_id(acct(0x61), 1));
    parent.insert(Arc::new(vault)).expect("insert vault");
    parent
        .insert(Arc::new(loan_broker_entry(
            broker_id, owner, pseudo, vault_id, 2, 0, 0, 0,
        )))
        .expect("insert before broker");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(loan_broker_entry(
        broker_id, owner, pseudo, vault_id, 1, 0, 0, 0,
    )))
    .expect("update broker");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::LOAN_BROKER_SET,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_zero_owner_count_loan_broker_with_multi_index_directory() {
    let base = Arc::new(lending_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let vault_id = Uint256::from_u64(30);
    let broker_id = Uint256::from_u64(31);
    let owner = acct(0x62);
    let pseudo = acct(0x63);
    let issuer = acct(0x64);
    let issue = Issue {
        currency: iou_currency(b"USD"),
        account: issuer,
    };
    let asset = Asset::Issue(issue);
    let mut vault = STLedgerEntry::from_type_and_key(LedgerEntryType::Vault, vault_id);
    vault.set_account_id(sf("sfOwner"), owner);
    vault.set_account_id(sf("sfAccount"), acct(0x65));
    vault.set_field_issue(sf("sfAsset"), STIssue::new_with_asset(sf("sfAsset"), asset));
    vault.set_field_number(sf("sfAssetsTotal"), associated_number(asset, 0));
    vault.set_field_number(sf("sfAssetsAvailable"), associated_number(asset, 0));
    vault.set_field_number(sf("sfLossUnrealized"), associated_number(asset, 0));
    vault.set_field_h192(sf("sfShareMPTID"), mpt_id(acct(0x65), 1));
    parent.insert(Arc::new(vault)).expect("insert vault");

    let owner_dir = protocol::owner_dir_keylet(raw_id(pseudo));
    let mut dir = STLedgerEntry::from_type_and_key(LedgerEntryType::DirectoryNode, owner_dir.key);
    dir.set_field_h256(sf("sfRootIndex"), owner_dir.key);
    dir.set_field_v256(
        sf("sfIndexes"),
        protocol::STVector256::from_values(
            sf("sfIndexes"),
            vec![Uint256::from_u64(32), Uint256::from_u64(33)],
        ),
    );
    parent.insert(Arc::new(dir)).expect("insert owner dir");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.insert(Arc::new(loan_broker_entry(
        broker_id, owner, pseudo, vault_id, 1, 0, 0, 0,
    )))
    .expect("insert broker");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::LOAN_BROKER_SET,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_loan_broker_cover_below_pseudo_balance() {
    let base = Arc::new(lending_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let vault_id = Uint256::from_u64(34);
    let broker_id = Uint256::from_u64(35);
    let owner = acct(0x66);
    let pseudo = acct(0x67);
    let issuer = acct(0x70);
    let issue = Issue {
        currency: iou_currency(b"USD"),
        account: issuer,
    };
    let asset = Asset::Issue(issue);
    let mut vault = STLedgerEntry::from_type_and_key(LedgerEntryType::Vault, vault_id);
    vault.set_account_id(sf("sfOwner"), owner);
    vault.set_account_id(sf("sfAccount"), acct(0x68));
    vault.set_field_issue(sf("sfAsset"), STIssue::new_with_asset(sf("sfAsset"), asset));
    vault.set_field_number(sf("sfAssetsTotal"), associated_number(asset, 0));
    vault.set_field_number(sf("sfAssetsAvailable"), associated_number(asset, 0));
    vault.set_field_number(sf("sfLossUnrealized"), associated_number(asset, 0));
    vault.set_field_h192(sf("sfShareMPTID"), mpt_id(acct(0x68), 1));
    parent.insert(Arc::new(vault)).expect("insert vault");
    parent
        .insert(Arc::new(ripple_state_balance_entry(pseudo, issuer, 5)))
        .expect("insert pseudo trustline");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.insert(Arc::new(loan_broker_entry(
        broker_id, owner, pseudo, vault_id, 1, 0, 4, 1,
    )))
    .expect("insert broker");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::LOAN_BROKER_COVER_WITHDRAW,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_loan_broker_cover_above_pseudo_balance_after_cleanup_3_1_3() {
    let base = Arc::new(lending_cleanup_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let vault_id = Uint256::from_u64(36);
    let broker_id = Uint256::from_u64(37);
    let owner = acct(0x69);
    let pseudo = acct(0x6A);
    let issuer = acct(0x71);
    let issue = Issue {
        currency: iou_currency(b"USD"),
        account: issuer,
    };
    let asset = Asset::Issue(issue);
    let mut vault = STLedgerEntry::from_type_and_key(LedgerEntryType::Vault, vault_id);
    vault.set_account_id(sf("sfOwner"), owner);
    vault.set_account_id(sf("sfAccount"), acct(0x6B));
    vault.set_field_issue(sf("sfAsset"), STIssue::new_with_asset(sf("sfAsset"), asset));
    vault.set_field_number(sf("sfAssetsTotal"), associated_number(asset, 0));
    vault.set_field_number(sf("sfAssetsAvailable"), associated_number(asset, 0));
    vault.set_field_number(sf("sfLossUnrealized"), associated_number(asset, 0));
    vault.set_field_h192(sf("sfShareMPTID"), mpt_id(acct(0x6B), 1));
    parent.insert(Arc::new(vault)).expect("insert vault");
    parent
        .insert(Arc::new(ripple_state_balance_entry(pseudo, issuer, 5)))
        .expect("insert pseudo trustline");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.insert(Arc::new(loan_broker_entry(
        broker_id, owner, pseudo, vault_id, 1, 0, 6, 1,
    )))
    .expect("insert broker");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::LOAN_BROKER_COVER_DEPOSIT,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_amm_zero_lp_tokens() {
    with_amm_invariant_flow(|flow| {
        let issuer = acct(0x66);
        let issue1 = Issue {
            currency: iou_currency(b"AAA"),
            account: issuer,
        };
        let issue2 = Issue {
            currency: iou_currency(b"BBB"),
            account: issuer,
        };
        let mut amm = STLedgerEntry::from_type_and_key(LedgerEntryType::AMM, Uint256::from_u64(10));
        amm.set_account_id(sf("sfAccount"), acct(0x77));
        amm.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(issue1)),
        );
        amm.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(issue2)),
        );
        amm.set_field_amount(
            sf("sfLPTokenBalance"),
            STAmount::from_iou_amount(sf("sfLPTokenBalance"), IOUAmount::new(), issue1),
        );

        flow.insert(Arc::new(amm)).expect("insert amm");
        assert_eq!(
            check_invariants(
                flow,
                TxType::AMM_CREATE,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_amm_create_lp_tokens_above_pool_product() {
    with_amm_invariant_flow(|flow| {
        let issue1 = Issue {
            currency: iou_currency(b"AAA"),
            account: acct(0x81),
        };
        let issue2 = Issue {
            currency: iou_currency(b"BBB"),
            account: acct(0x82),
        };
        let amm = amm_entry_with_pool(20, acct(0x83), issue1, issue2, 3, 3, 20);

        flow.insert(Arc::new(amm)).expect("insert amm");
        assert_eq!(
            check_invariants(
                flow,
                TxType::AMM_CREATE,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_amm_deposit_lp_tokens_above_pool_product() {
    with_amm_invariant_flow(|flow| {
        let issue1 = Issue {
            currency: iou_currency(b"AAA"),
            account: acct(0x84),
        };
        let issue2 = Issue {
            currency: iou_currency(b"BBB"),
            account: acct(0x85),
        };
        let amm = amm_entry_with_pool(21, acct(0x86), issue1, issue2, 3, 3, 20);

        flow.insert(Arc::new(amm)).expect("insert amm");
        assert_eq!(
            check_invariants(
                flow,
                TxType::AMM_DEPOSIT,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_recursive_invalid_mpt_amount_inside_amm_auction_slot() {
    with_flow(|flow| {
        let issuer = acct(0x88);
        let issue = MPTIssue::new(mpt_id(issuer, 1));
        let asset = Issue {
            currency: iou_currency(b"AAA"),
            account: issuer,
        };
        let asset2 = Issue {
            currency: iou_currency(b"BBB"),
            account: issuer,
        };
        let mut slot = STObject::make_inner_object(sf("sfAuctionSlot"));
        slot.set_account_id(sf("sfAccount"), acct(0x99));
        slot.set_field_u32(sf("sfExpiration"), 100);
        slot.set_field_amount(
            sf("sfPrice"),
            STAmount::from_mpt_amount(sf("sfPrice"), MPTAmount::from_value(-1), issue),
        );

        let mut amm = STLedgerEntry::from_type_and_key(LedgerEntryType::AMM, Uint256::from_u64(11));
        amm.set_account_id(sf("sfAccount"), acct(0x77));
        amm.set_field_issue(
            sf("sfAsset"),
            STIssue::new_with_asset(sf("sfAsset"), Asset::Issue(asset)),
        );
        amm.set_field_issue(
            sf("sfAsset2"),
            STIssue::new_with_asset(sf("sfAsset2"), Asset::Issue(asset2)),
        );
        amm.set_field_amount(
            sf("sfLPTokenBalance"),
            STAmount::from_iou_amount(
                sf("sfLPTokenBalance"),
                IOUAmount::from_parts(1, 0).expect("iou"),
                asset,
            ),
        );
        amm.set_field_object(sf("sfAuctionSlot"), slot);

        flow.insert(Arc::new(amm)).expect("insert amm");
        assert_eq!(
            check_invariants(
                flow,
                TxType::AMM_BID,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_allows_recursive_invalid_mpt_amount_before_fix_cleanup_3_2_0() {
    let base = Arc::new(mpt_v2_without_cleanup_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let mut flow = FlowSandbox::new(&mut parent);
    let account = acct(0x89);
    let destination = acct(0x8A);
    let issue = MPTIssue::new(mpt_id(account, 1));
    let mut check = STLedgerEntry::new(protocol::check_keylet(raw_id(account), 1));
    check.set_account_id(sf("sfAccount"), account);
    check.set_account_id(sf("sfDestination"), destination);
    check.set_field_amount(
        sf("sfSendMax"),
        STAmount::from_mpt_amount(sf("sfSendMax"), MPTAmount::from_value(-1), issue),
    );

    flow.insert(Arc::new(check)).expect("insert check");
    assert_eq!(
        check_invariants(
            &flow,
            TxType::ACCOUNT_SET,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TES_SUCCESS
    );
}

#[test]
fn invariant_rejects_invalid_mpt_amount_in_ledger_entry_after_fix_cleanup_3_2_0() {
    with_flow(|flow| {
        let account = acct(0x8B);
        let destination = acct(0x8C);
        let issue = MPTIssue::new(mpt_id(account, 1));
        let mut check = STLedgerEntry::new(protocol::check_keylet(raw_id(account), 1));
        check.set_account_id(sf("sfAccount"), account);
        check.set_account_id(sf("sfDestination"), destination);
        check.set_field_amount(
            sf("sfSendMax"),
            STAmount::from_mpt_amount(sf("sfSendMax"), MPTAmount::from_value(-1), issue),
        );

        flow.insert(Arc::new(check)).expect("insert check");
        assert_eq!(
            check_invariants(
                flow,
                TxType::ACCOUNT_SET,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_amm_bid_mpt_amm_pool_change() {
    with_flow(|flow| {
        let issuer = acct(0x8A);
        let amm_account = acct(0x8B);
        let token = mptoken_entry_with_flags(amm_account, issuer, 1, 50, protocol::lsfMPTAMM);

        flow.insert(Arc::new(token)).expect("insert amm mpt token");
        assert_eq!(
            check_invariants(
                flow,
                TxType::AMM_BID,
                Ter::TES_SUCCESS,
                XRPAmount::from_drops(10)
            ),
            Ter::TEC_INVARIANT_FAILED
        );
    });
}

#[test]
fn invariant_rejects_amm_vote_lp_token_balance_change() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x8C);
    let amm_account = acct(0x8D);
    let asset = Issue {
        currency: iou_currency(b"AAA"),
        account: issuer,
    };
    let asset2 = Issue {
        currency: iou_currency(b"BBB"),
        account: issuer,
    };
    parent
        .insert(Arc::new(amm_entry(12, amm_account, asset, asset2, 10)))
        .expect("insert before amm");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(amm_entry(12, amm_account, asset, asset2, 11)))
        .expect("update after amm");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::AMM_VOTE,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_amm_bid_lp_token_balance_increase() {
    let base = Arc::new(test_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x8E);
    let amm_account = acct(0x8F);
    let asset = Issue {
        currency: iou_currency(b"AAA"),
        account: issuer,
    };
    let asset2 = Issue {
        currency: iou_currency(b"BBB"),
        account: issuer,
    };
    parent
        .insert(Arc::new(amm_entry(13, amm_account, asset, asset2, 10)))
        .expect("insert before amm");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(amm_entry(13, amm_account, asset, asset2, 11)))
        .expect("update after amm");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::AMM_BID,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_amm_delete_that_leaves_amm_entry() {
    let base = Arc::new(amm_invariant_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x90);
    let amm_account = acct(0x91);
    let asset = Issue {
        currency: iou_currency(b"AAA"),
        account: issuer,
    };
    let asset2 = Issue {
        currency: iou_currency(b"BBB"),
        account: issuer,
    };
    parent
        .insert(Arc::new(amm_entry(14, amm_account, asset, asset2, 10)))
        .expect("insert before amm");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(amm_entry(14, amm_account, asset, asset2, 10)))
        .expect("update after amm");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::AMM_DELETE,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}

#[test]
fn invariant_rejects_payment_that_modifies_amm_entry() {
    let base = Arc::new(amm_invariant_ledger());
    let mut parent = Sandbox::new(base, ApplyFlags::default());
    let issuer = acct(0x92);
    let amm_account = acct(0x93);
    let asset = Issue {
        currency: iou_currency(b"AAA"),
        account: issuer,
    };
    let asset2 = Issue {
        currency: iou_currency(b"BBB"),
        account: issuer,
    };
    parent
        .insert(Arc::new(amm_entry(15, amm_account, asset, asset2, 10)))
        .expect("insert before amm");

    let mut flow = FlowSandbox::new(&mut parent);
    flow.update(Arc::new(amm_entry(15, amm_account, asset, asset2, 9)))
        .expect("update after amm");

    assert_eq!(
        check_invariants(
            &flow,
            TxType::PAYMENT,
            Ter::TES_SUCCESS,
            XRPAmount::from_drops(10)
        ),
        Ter::TEC_INVARIANT_FAILED
    );
}
