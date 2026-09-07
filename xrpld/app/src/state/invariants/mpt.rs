use super::common::*;
use ledger::{ApplyView, FlowSandbox, ReadView};
use protocol::{AccountID, LedgerEntryType, MPTID, STLedgerEntry, Ter};
use std::collections::BTreeMap;

#[derive(Default)]
pub(super) struct MptAccounting {
    outstanding_before: i128,
    outstanding_after: i128,
    amount_delta: i128,
    overflow: bool,
}

#[derive(Default)]
pub(super) struct MptTransferAmount {
    before: Option<u64>,
    after: Option<u64>,
    authorized_before: bool,
    authorized_after: bool,
    locked_before: bool,
    locked_after: bool,
}

#[derive(Default)]
pub(super) struct MptIssuanceLifecycle {
    reference_holding_set_on_create: bool,
    reference_holding_mutated: bool,
    vault_holding_deleted: bool,
    issuances_created: u32,
    issuances_deleted: u32,
    tokens_created: u32,
    tokens_deleted: u32,
    token_created_by_issuer: bool,
}

#[derive(Default)]
pub(super) struct ConfidentialMptChange {
    mpt_amount_delta: i128,
    coa_delta: i128,
    outstanding_delta: i128,
    issuance: Option<STLedgerEntry>,
    deleted_with_encrypted: bool,
    bad_consistency: bool,
    bad_coa: bool,
    changes_confidential_fields: bool,
    bad_version: bool,
}

fn capped_delta(value: u64) -> i128 {
    i128::from(value.min(max_mpt_token_amount()))
}

fn optional_u32_value(sle: &STLedgerEntry, field: &'static protocol::SField) -> Option<u32> {
    sle.is_field_present(field)
        .then(|| sle.get_field_u32(field))
}

fn optional_vl_value(sle: &STLedgerEntry, field: &'static protocol::SField) -> Option<Vec<u8>> {
    sle.is_field_present(field).then(|| sle.get_field_vl(field))
}

pub(super) fn record_confidential_mpt(
    changes: &mut BTreeMap<MPTID, ConfidentialMptChange>,
    is_delete: bool,
    before: Option<&STLedgerEntry>,
    after: &STLedgerEntry,
) {
    let id = |sle: &STLedgerEntry| match sle.get_type() {
        LedgerEntryType::MPToken => sle.get_field_h192(sf("sfMPTokenIssuanceID")),
        LedgerEntryType::MPTokenIssuance => mpt_id_from_issuance(sle),
        _ => MPTID::default(),
    };
    if let Some(before) = before.filter(|sle| sle.get_type() == LedgerEntryType::MPToken) {
        let change = changes.entry(id(before)).or_default();
        change.mpt_amount_delta -= capped_delta(before.get_field_u64(sf("sfMPTAmount")));
        if is_delete {
            change.deleted_with_encrypted = before.get_field_u64(sf("sfMPTAmount")) > 0
                || [
                    "sfConfidentialBalanceSpending",
                    "sfConfidentialBalanceInbox",
                    "sfIssuerEncryptedBalance",
                    "sfAuditorEncryptedBalance",
                ]
                .iter()
                .any(|field| before.is_field_present(sf(field)));
        }
    }
    if after.get_type() == LedgerEntryType::MPToken {
        let change = changes.entry(id(after)).or_default();
        change.mpt_amount_delta += capped_delta(after.get_field_u64(sf("sfMPTAmount")));
        let issuer = after.is_field_present(sf("sfIssuerEncryptedBalance"));
        let inbox = after.is_field_present(sf("sfConfidentialBalanceInbox"));
        let spending = after.is_field_present(sf("sfConfidentialBalanceSpending"));
        let auditor = after.is_field_present(sf("sfAuditorEncryptedBalance"));
        change.bad_consistency |= inbox != spending || inbox != issuer || (auditor && !issuer);
        for field in [
            "sfConfidentialBalanceInbox",
            "sfConfidentialBalanceSpending",
            "sfIssuerEncryptedBalance",
            "sfAuditorEncryptedBalance",
        ] {
            let field = sf(field);
            if after.is_field_present(field)
                && before.is_none_or(|before| {
                    before.get_type() != LedgerEntryType::MPToken
                        || optional_vl_value(before, field) != optional_vl_value(after, field)
                })
            {
                change.changes_confidential_fields = true;
            }
        }
    }
    if let Some(before) = before.filter(|sle| sle.get_type() == LedgerEntryType::MPTokenIssuance) {
        let change = changes.entry(id(before)).or_default();
        if before.is_field_present(sf("sfConfidentialOutstandingAmount")) {
            change.coa_delta -=
                capped_delta(before.get_field_u64(sf("sfConfidentialOutstandingAmount")));
        }
        change.outstanding_delta -= capped_delta(before.get_field_u64(sf("sfOutstandingAmount")));
    }
    if after.get_type() == LedgerEntryType::MPTokenIssuance {
        let change = changes.entry(id(after)).or_default();
        let coa = optional_u64(after, sf("sfConfidentialOutstandingAmount"));
        if after.is_field_present(sf("sfConfidentialOutstandingAmount")) {
            change.coa_delta += capped_delta(coa);
        }
        let outstanding = after.get_field_u64(sf("sfOutstandingAmount"));
        change.outstanding_delta += capped_delta(outstanding);
        change.issuance = Some(after.clone());
        change.bad_coa |= coa > outstanding;
    }
    if let Some(before) = before.filter(|sle| sle.get_type() == LedgerEntryType::MPToken)
        && after.get_type() == LedgerEntryType::MPToken
    {
        let spending_before = optional_vl_value(before, sf("sfConfidentialBalanceSpending"));
        let spending_after = optional_vl_value(after, sf("sfConfidentialBalanceSpending"));
        if spending_before.is_some() && spending_before != spending_after {
            changes.entry(id(after)).or_default().bad_version |=
                optional_u32_value(before, sf("sfConfidentialBalanceVersion"))
                    == optional_u32_value(after, sf("sfConfidentialBalanceVersion"));
        }
    }
}

pub(super) fn validates_confidential_mpt<V: ApplyView + ?Sized>(
    view: &FlowSandbox<V>,
    txn_type: protocol::TxType,
    result: Ter,
    changes: &BTreeMap<MPTID, ConfidentialMptChange>,
) -> bool {
    if !protocol::is_tes_success(result) {
        return true;
    }
    let confidential_tx = matches!(txn_type.to_u16(), 85..=89);
    changes.iter().all(|(id, change)| {
        let issuance = if let Some(issuance) = change.issuance.clone() {
            Some(issuance)
        } else {
            match view.read(protocol::mpt_issuance_keylet_from_mptid(*id)) {
                Ok(value) => value.map(|sle| (*sle).clone()),
                // A SHAMap/storage failure is not evidence that the issuance
                // was deleted. Fail the invariant closed instead of silently
                // skipping all confidential-balance checks.
                Err(_) => return false,
            }
        };
        let Some(issuance) = issuance else {
            return true;
        };
        if change.deleted_with_encrypted
            && optional_u64(&issuance, sf("sfConfidentialOutstandingAmount")) > 0
        {
            return false;
        }
        if change.bad_consistency || change.bad_coa || change.bad_version {
            return false;
        }
        if change.changes_confidential_fields
            && !issuance.is_flag(protocol::lsfMPTCanHoldConfidentialBalance)
        {
            return false;
        }
        if change.coa_delta != 0 {
            change.mpt_amount_delta + change.coa_delta == change.outstanding_delta
        } else if confidential_tx {
            change.mpt_amount_delta == 0 && change.outstanding_delta == 0
        } else {
            true
        }
    })
}

pub(super) fn max_mpt_token_amount() -> u64 {
    protocol::MAX_MP_TOKEN_AMOUNT as u64
}

pub(super) fn mpt_id_from_issuance(sle: &STLedgerEntry) -> MPTID {
    protocol::make_mpt_id(
        sle.get_field_u32(sf("sfSequence")),
        sle.get_account_id(sf("sfIssuer")),
    )
}

pub(super) fn mpt_max_amount(sle: &STLedgerEntry) -> u64 {
    if sle.is_field_present(sf("sfMaximumAmount")) {
        sle.get_field_u64(sf("sfMaximumAmount"))
    } else {
        max_mpt_token_amount()
    }
}

pub(super) fn record_mpt_accounting(
    data: &mut BTreeMap<MPTID, MptAccounting>,
    sle: &STLedgerEntry,
    before: bool,
) {
    match sle.get_type() {
        LedgerEntryType::MPTokenIssuance => {
            let outstanding = optional_u64(sle, sf("sfOutstandingAmount"));
            let id = mpt_id_from_issuance(sle);
            let entry = data.entry(id).or_default();
            if outstanding > mpt_max_amount(sle) {
                entry.overflow = true;
            }
            if before {
                entry.outstanding_before = i128::from(outstanding);
            } else {
                entry.outstanding_after = i128::from(outstanding);
            }
        }
        LedgerEntryType::MPToken => {
            let mpt_amount = optional_u64(sle, sf("sfMPTAmount"));
            let locked_amount = optional_u64(sle, sf("sfLockedAmount"));
            let id = sle.get_field_h192(sf("sfMPTokenIssuanceID"));
            let entry = data.entry(id).or_default();
            let max_amount = max_mpt_token_amount();
            if mpt_amount > max_amount
                || locked_amount > max_amount
                || locked_amount > max_amount.saturating_sub(mpt_amount)
            {
                entry.overflow = true;
                return;
            }
            let holder_total = i128::from(mpt_amount) + i128::from(locked_amount);
            if before {
                entry.amount_delta -= holder_total;
            } else {
                entry.amount_delta += holder_total;
            }
        }
        _ => {}
    }
}

pub(super) fn validates_mpt_accounting(
    data: &BTreeMap<MPTID, MptAccounting>,
    enforce: bool,
) -> bool {
    if !enforce {
        return true;
    }

    data.values().all(|entry| {
        !entry.overflow && entry.outstanding_after == entry.outstanding_before + entry.amount_delta
    })
}

/// Mirrors rippled's `ValidMPTBalanceChanges::finalize`: confidential MPT
/// transactions move value between the public amount and encrypted balances.
/// Their accounting is owned by `ValidConfidentialMPToken`, so applying the
/// ordinary `sfMPTAmount`/`sfOutstandingAmount` equation as well would reject
/// valid convert, convert-back, and clawback transactions.
pub(super) fn validates_mpt_accounting_for_transaction(
    data: &BTreeMap<MPTID, MptAccounting>,
    enforce: bool,
    txn_type: protocol::TxType,
) -> bool {
    if matches!(txn_type.to_u16(), 85..=89) {
        return true;
    }
    validates_mpt_accounting(data, enforce)
}

pub(super) fn record_mpt_transfer(
    transfers: &mut BTreeMap<MPTID, BTreeMap<AccountID, MptTransferAmount>>,
    sle: &STLedgerEntry,
    before: bool,
) {
    if sle.get_type() != LedgerEntryType::MPToken {
        return;
    }

    let id = sle.get_field_h192(sf("sfMPTokenIssuanceID"));
    let account = sle.get_account_id(sf("sfAccount"));
    let amount = optional_u64(sle, sf("sfMPTAmount"));
    let entry = transfers.entry(id).or_default().entry(account).or_default();
    if before {
        entry.before = Some(amount);
        entry.authorized_before = sle.is_flag(protocol::lsfMPTAuthorized);
        entry.locked_before = sle.is_flag(protocol::lsfMPTLocked);
    } else {
        entry.after = Some(amount);
        entry.authorized_after = sle.is_flag(protocol::lsfMPTAuthorized);
        entry.locked_after = sle.is_flag(protocol::lsfMPTLocked);
    }
}

pub(super) fn mpt_transfer_waives_can_transfer(
    txn_type: protocol::TxType,
    fix_cleanup_3_2_0: bool,
) -> bool {
    txn_type == protocol::TxType::AMM_WITHDRAW
        || (fix_cleanup_3_2_0
            && matches!(
                txn_type,
                protocol::TxType::VAULT_WITHDRAW
                    | protocol::TxType::LOAN_BROKER_COVER_WITHDRAW
                    | protocol::TxType::LOAN_PAY
            ))
}

pub(super) fn mpt_transfer_is_dex(
    txn_type: protocol::TxType,
    cross_currency_payment: bool,
) -> bool {
    if txn_type == protocol::TxType::PAYMENT {
        return cross_currency_payment;
    }

    matches!(
        txn_type,
        protocol::TxType::AMM_CREATE
            | protocol::TxType::AMM_DEPOSIT
            | protocol::TxType::OFFER_CREATE
    )
}

pub(super) fn validates_mpt_transfers<V: ApplyView + ?Sized>(
    sandbox: &FlowSandbox<V>,
    txn_type: protocol::TxType,
    cross_currency_payment: bool,
    fix_cleanup_3_2_0: bool,
    mptokens_v2_enabled: bool,
    transfers: &BTreeMap<MPTID, BTreeMap<AccountID, MptTransferAmount>>,
) -> Result<bool, ledger::ViewError> {
    if txn_type == protocol::TxType::AMM_CLAWBACK {
        return Ok(true);
    }

    for (mpt_id, holders) in transfers {
        let Some(issuance) = sandbox.read(protocol::mpt_issuance_keylet_from_mptid(*mpt_id))?
        else {
            continue;
        };

        let can_transfer = issuance.is_flag(protocol::lsfMPTCanTransfer)
            || mpt_transfer_waives_can_transfer(txn_type, fix_cleanup_3_2_0);
        let can_trade = issuance.is_flag(protocol::lsfMPTCanTrade);
        let req_auth = issuance.is_flag(protocol::lsfMPTRequireAuth);
        let issue = protocol::MPTIssue::new(*mpt_id);

        let mut senders = 0_u16;
        let mut receivers = 0_u16;
        let mut invalid_transfer = issuance.is_flag(protocol::lsfMPTLocked);
        for (account, value) in holders {
            let Some(after) = value.after else {
                continue;
            };
            let before = value.before.unwrap_or(0);
            if before == after {
                continue;
            }
            if after > before {
                receivers = receivers.saturating_add(1);
            } else {
                senders = senders.saturating_add(1);
            }
            let frozen = ledger::mptoken_helpers::is_frozen_mpt(sandbox, account, &issue)?;
            let authorized = if req_auth {
                protocol::is_tes_success(ledger::mptoken_helpers::require_auth_mpt(
                    sandbox, &issue, account,
                )?)
            } else {
                true
            };
            if frozen || value.locked_before || value.locked_after || !authorized {
                invalid_transfer = true;
            }
        }

        if senders > 0
            && receivers > 0
            && (invalid_transfer
                || !can_transfer
                || (mpt_transfer_is_dex(txn_type, cross_currency_payment) && !can_trade))
        {
            return Ok(!mptokens_v2_enabled);
        }
    }

    Ok(true)
}

pub(super) fn same_optional_h256(
    before: &STLedgerEntry,
    after: &STLedgerEntry,
    field: &'static protocol::SField,
) -> bool {
    let before_present = before.is_field_present(field);
    let after_present = after.is_field_present(field);
    before_present == after_present
        && (!before_present || before.get_field_h256(field) == after.get_field_h256(field))
}

pub(super) fn record_mpt_issuance_lifecycle<V: ApplyView + ?Sized>(
    sandbox: &FlowSandbox<V>,
    txn_type: protocol::TxType,
    lifecycle: &mut MptIssuanceLifecycle,
    is_delete: bool,
    before: Option<&STLedgerEntry>,
    after: Option<&STLedgerEntry>,
    deleted: &STLedgerEntry,
) -> Result<(), ledger::ViewError> {
    if let Some(after) = after
        && after.get_type() == LedgerEntryType::MPTokenIssuance
    {
        if before.is_none() {
            lifecycle.issuances_created = lifecycle.issuances_created.saturating_add(1);
            lifecycle.reference_holding_set_on_create |= after
                .is_field_present(sf("sfReferenceHolding"))
                && txn_type != protocol::TxType::VAULT_CREATE;
        } else if let Some(before) = before {
            lifecycle.reference_holding_mutated |=
                !same_optional_h256(before, after, sf("sfReferenceHolding"));
        }
    }

    if is_delete && deleted.get_type() == LedgerEntryType::MPTokenIssuance {
        lifecycle.issuances_deleted = lifecycle.issuances_deleted.saturating_add(1);
    }

    if let Some(after) = after
        && after.get_type() == LedgerEntryType::MPToken
        && before.is_none()
    {
        lifecycle.tokens_created = lifecycle.tokens_created.saturating_add(1);
        let id = after.get_field_h192(sf("sfMPTokenIssuanceID"));
        lifecycle.token_created_by_issuer |=
            protocol::MPTIssue::new(id).issuer() == after.get_account_id(sf("sfAccount"));
    }

    if is_delete && deleted.get_type() == LedgerEntryType::MPToken {
        lifecycle.tokens_deleted = lifecycle.tokens_deleted.saturating_add(1);
    }

    if !is_delete || txn_type == protocol::TxType::VAULT_DELETE {
        return Ok(());
    }

    lifecycle.vault_holding_deleted |= match deleted.get_type() {
        LedgerEntryType::MPToken => {
            let holder = deleted.get_account_id(sf("sfAccount"));
            is_vault_pseudo_account(sandbox, holder)?
        }
        LedgerEntryType::RippleState => {
            let low_counterparty = deleted.get_field_amount(sf("sfLowLimit")).issue().account;
            let high_counterparty = deleted.get_field_amount(sf("sfHighLimit")).issue().account;
            is_vault_pseudo_account(sandbox, low_counterparty)?
                || is_vault_pseudo_account(sandbox, high_counterparty)?
        }
        _ => false,
    };
    Ok(())
}

pub(super) fn is_vault_pseudo_account<V: ApplyView + ?Sized>(
    sandbox: &FlowSandbox<V>,
    account: AccountID,
) -> Result<bool, ledger::ViewError> {
    Ok(sandbox
        .read(protocol::account_keylet(raw_account_id(account)))?
        .is_some_and(|sle| sle.is_field_present(sf("sfVaultID"))))
}

pub(super) fn validates_mpt_issuance_lifecycle(lifecycle: &MptIssuanceLifecycle) -> bool {
    !lifecycle.reference_holding_set_on_create
        && !lifecycle.reference_holding_mutated
        && !lifecycle.vault_holding_deleted
}

pub(super) fn has_create_mpt_issuance_privilege(txn_type: protocol::TxType) -> bool {
    matches!(
        txn_type,
        protocol::TxType::MPTOKEN_ISSUANCE_CREATE | protocol::TxType::VAULT_CREATE
    )
}

pub(super) fn has_destroy_mpt_issuance_privilege(txn_type: protocol::TxType) -> bool {
    matches!(
        txn_type,
        protocol::TxType::MPTOKEN_ISSUANCE_DESTROY | protocol::TxType::VAULT_DELETE
    )
}

pub(super) fn has_must_authorize_mpt_privilege(txn_type: protocol::TxType) -> bool {
    txn_type == protocol::TxType::MPTOKEN_AUTHORIZE
}

pub(super) fn has_may_authorize_mpt_privilege(txn_type: protocol::TxType) -> bool {
    matches!(
        txn_type,
        protocol::TxType::AMM_CLAWBACK
            | protocol::TxType::AMM_WITHDRAW
            | protocol::TxType::VAULT_DEPOSIT
            | protocol::TxType::VAULT_WITHDRAW
            | protocol::TxType::LOAN_BROKER_SET
            | protocol::TxType::LOAN_BROKER_DELETE
            | protocol::TxType::LOAN_BROKER_COVER_WITHDRAW
            | protocol::TxType::LOAN_SET
            | protocol::TxType::LOAN_PAY
    )
}

pub(super) fn has_may_create_mpt_privilege(txn_type: protocol::TxType) -> bool {
    matches!(
        txn_type,
        protocol::TxType::PAYMENT
            | protocol::TxType::OFFER_CREATE
            | protocol::TxType::CHECK_CASH
            | protocol::TxType::AMM_CREATE
    )
}

pub(super) fn has_may_delete_mpt_privilege(txn_type: protocol::TxType) -> bool {
    matches!(
        txn_type,
        protocol::TxType::AMM_DELETE
            | protocol::TxType::VAULT_WITHDRAW
            | protocol::TxType::VAULT_CLAWBACK
    )
}

pub(super) fn validates_mpt_lifecycle_counts(
    txn_type: protocol::TxType,
    result: Ter,
    tx_has_holder: bool,
    single_asset_vault_enabled: bool,
    lending_protocol_enabled: bool,
    mptokens_v2_enabled: bool,
    lifecycle: &MptIssuanceLifecycle,
) -> bool {
    let applies =
        protocol::is_tes_success(result) || (mptokens_v2_enabled && result == Ter::TEC_INCOMPLETE);
    if !applies {
        return true;
    }

    if lifecycle.token_created_by_issuer && (single_asset_vault_enabled || lending_protocol_enabled)
    {
        return false;
    }

    if has_create_mpt_issuance_privilege(txn_type) {
        return lifecycle.issuances_created == 1 && lifecycle.issuances_deleted == 0;
    }

    if has_destroy_mpt_issuance_privilege(txn_type) {
        return lifecycle.issuances_created == 0 && lifecycle.issuances_deleted == 1;
    }

    let enforce_escrow_finish = txn_type == protocol::TxType::ESCROW_FINISH
        && (single_asset_vault_enabled || lending_protocol_enabled);
    if has_must_authorize_mpt_privilege(txn_type)
        || has_may_authorize_mpt_privilege(txn_type)
        || enforce_escrow_finish
    {
        if lifecycle.issuances_created > 0 || lifecycle.issuances_deleted > 0 {
            return false;
        }

        if mptokens_v2_enabled
            && has_may_authorize_mpt_privilege(txn_type)
            && matches!(
                txn_type,
                protocol::TxType::AMM_WITHDRAW | protocol::TxType::AMM_CLAWBACK
            )
        {
            if tx_has_holder
                && txn_type == protocol::TxType::AMM_WITHDRAW
                && lifecycle.tokens_created > 0
            {
                return false;
            }
            return lifecycle.tokens_created <= 1 && lifecycle.tokens_deleted <= 2;
        }

        if lending_protocol_enabled && lifecycle.tokens_created + lifecycle.tokens_deleted > 1 {
            return false;
        }

        if tx_has_holder && (lifecycle.tokens_created > 0 || lifecycle.tokens_deleted > 0) {
            return false;
        }

        if !tx_has_holder
            && has_must_authorize_mpt_privilege(txn_type)
            && lifecycle.tokens_created + lifecycle.tokens_deleted != 1
        {
            return false;
        }

        return true;
    }

    if has_may_create_mpt_privilege(txn_type) {
        if lifecycle.issuances_created > 0
            || lifecycle.issuances_deleted > 0
            || lifecycle.tokens_deleted > 0
            || tx_has_holder
        {
            return false;
        }
        if (txn_type == protocol::TxType::AMM_CREATE && lifecycle.tokens_created > 2)
            || (txn_type == protocol::TxType::CHECK_CASH && lifecycle.tokens_created > 1)
        {
            return false;
        }
        return true;
    }

    // EscrowFinish may create the destination holder's MPToken while
    // releasing an MPT escrow. rippled permits that lifecycle change here,
    // after the amendment-gated authorization checks above, rather than
    // assigning EscrowFinish the broader MayAuthorizeMpt privilege.
    if txn_type == protocol::TxType::ESCROW_FINISH {
        return true;
    }

    if has_may_delete_mpt_privilege(txn_type)
        && lifecycle.tokens_created == 0
        && lifecycle.issuances_created == 0
        && lifecycle.issuances_deleted == 0
        && ((txn_type == protocol::TxType::AMM_DELETE && lifecycle.tokens_deleted <= 2)
            || lifecycle.tokens_deleted == 1)
    {
        return true;
    }

    lifecycle.issuances_created == 0
        && lifecycle.issuances_deleted == 0
        && lifecycle.tokens_created == 0
        && lifecycle.tokens_deleted == 0
}
