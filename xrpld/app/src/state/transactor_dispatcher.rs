//! Transactor dispatcher — routes `TxType` to real view-backed engines.

use crate::state::transactor_apply_bridge::*;
use crate::state::transactor_escrow_bridge::*;
use basics::math::base_uint::{Uint160, Uint256};
use basics::number::{NumberParts as RuntimeNumber, RoundingMode};
use protocol::{
    AUCTION_SLOT_DISCOUNTED_FEE_FRACTION, AccountID, Asset, IOUAmount, Keylet, LedgerEntryType,
    MPTAmount, STAmount, STArray, STIssue, STLedgerEntry, STObject, STTx, STVector256, Ter, TxType,
    VOTE_MAX_SLOTS, VOTE_WEIGHT_SCALE_FACTOR, XRPAmount, get_field_by_symbol, is_tes_success,
    lsfDisableMaster, owner_dir_keylet, signers_keylet,
};
use std::sync::Arc;
use tx::*;

fn sf(name: &str) -> &'static protocol::SField {
    get_field_by_symbol(name)
}

fn decoded_amendments_entry(sle: &STLedgerEntry) -> protocol::DecodedAmendmentsEntry {
    let amendments = sle
        .is_field_present(sf("sfAmendments"))
        .then(|| sle.get_field_v256(sf("sfAmendments")).value().to_vec())
        .unwrap_or_default();
    let majorities = if sle.is_field_present(sf("sfMajorities")) {
        sle.get_field_array(sf("sfMajorities"))
            .iter()
            .map(|entry| protocol::DecodedMajorityEntry {
                amendment: entry.get_field_h256(sf("sfAmendment")),
                close_time: entry.get_field_u32(sf("sfCloseTime")),
            })
            .collect()
    } else {
        Vec::new()
    };
    protocol::DecodedAmendmentsEntry {
        amendments,
        majorities,
        previous_txn_id: sle
            .is_field_present(sf("sfPreviousTxnID"))
            .then(|| sle.get_field_h256(sf("sfPreviousTxnID"))),
        previous_txn_lgr_seq: sle
            .is_field_present(sf("sfPreviousTxnLgrSeq"))
            .then(|| sle.get_field_u32(sf("sfPreviousTxnLgrSeq"))),
    }
}

fn apply_decoded_amendments_entry(obj: &mut STObject, decoded: &protocol::DecodedAmendmentsEntry) {
    if decoded.amendments.is_empty() {
        obj.make_field_absent(sf("sfAmendments"));
    } else {
        obj.set_field_v256(
            sf("sfAmendments"),
            STVector256::from_values(sf("sfAmendments"), decoded.amendments.clone()),
        );
    }
    if decoded.majorities.is_empty() {
        obj.make_field_absent(sf("sfMajorities"));
    } else {
        let mut majorities = STArray::new(sf("sfMajorities"));
        for majority in &decoded.majorities {
            let mut entry = STObject::make_inner_object(sf("sfMajority"));
            entry.set_field_h256(sf("sfAmendment"), majority.amendment);
            entry.set_field_u32(sf("sfCloseTime"), majority.close_time);
            majorities.push_back(entry);
        }
        obj.set_field_array(sf("sfMajorities"), majorities);
    }
}

fn decoded_negative_unl_entry(sle: &STLedgerEntry) -> protocol::DecodedNegativeUnlEntry {
    let disabled_validators = if sle.is_field_present(sf("sfDisabledValidators")) {
        sle.get_field_array(sf("sfDisabledValidators"))
            .iter()
            .map(|entry| protocol::DecodedDisabledValidator {
                public_key: entry.get_field_vl(sf("sfPublicKey")),
                first_ledger_sequence: entry.get_field_u32(sf("sfFirstLedgerSequence")),
            })
            .collect()
    } else {
        Vec::new()
    };
    protocol::DecodedNegativeUnlEntry {
        disabled_validators,
        validator_to_disable: sle
            .is_field_present(sf("sfValidatorToDisable"))
            .then(|| sle.get_field_vl(sf("sfValidatorToDisable"))),
        validator_to_re_enable: sle
            .is_field_present(sf("sfValidatorToReEnable"))
            .then(|| sle.get_field_vl(sf("sfValidatorToReEnable"))),
        previous_txn_id: sle
            .is_field_present(sf("sfPreviousTxnID"))
            .then(|| sle.get_field_h256(sf("sfPreviousTxnID"))),
        previous_txn_lgr_seq: sle
            .is_field_present(sf("sfPreviousTxnLgrSeq"))
            .then(|| sle.get_field_u32(sf("sfPreviousTxnLgrSeq"))),
    }
}

fn apply_decoded_negative_unl_entry(
    obj: &mut STObject,
    decoded: &protocol::DecodedNegativeUnlEntry,
) {
    if decoded.disabled_validators.is_empty() {
        obj.make_field_absent(sf("sfDisabledValidators"));
    } else {
        let mut disabled = STArray::new(sf("sfDisabledValidators"));
        for validator in &decoded.disabled_validators {
            let mut entry = STObject::make_inner_object(sf("sfDisabledValidator"));
            entry.set_field_vl(sf("sfPublicKey"), &validator.public_key);
            entry.set_field_u32(sf("sfFirstLedgerSequence"), validator.first_ledger_sequence);
            disabled.push_back(entry);
        }
        obj.set_field_array(sf("sfDisabledValidators"), disabled);
    }
    match &decoded.validator_to_disable {
        Some(validator) => obj.set_field_vl(sf("sfValidatorToDisable"), validator),
        None => obj.make_field_absent(sf("sfValidatorToDisable")),
    }
    match &decoded.validator_to_re_enable {
        Some(validator) => obj.set_field_vl(sf("sfValidatorToReEnable"), validator),
        None => obj.make_field_absent(sf("sfValidatorToReEnable")),
    }
}

fn describe_owner_dir(account: AccountID) -> impl Fn(&mut STObject) {
    move |directory| directory.set_account_id(sf("sfOwner"), account)
}

#[allow(dead_code)] // reserve for M7 sweep
fn oracle_pair_key(entry: &STObject) -> (protocol::Currency, protocol::Currency) {
    (
        entry.get_field_currency(sf("sfBaseAsset")).currency(),
        entry.get_field_currency(sf("sfQuoteAsset")).currency(),
    )
}

#[allow(dead_code)] // reserve for M7 sweep
fn populated_oracle_price_data(entry: &STObject) -> STObject {
    let mut price_data = STObject::make_inner_object(sf("sfPriceData"));
    price_data.set_field_currency(
        sf("sfBaseAsset"),
        entry.get_field_currency(sf("sfBaseAsset")),
    );
    price_data.set_field_currency(
        sf("sfQuoteAsset"),
        entry.get_field_currency(sf("sfQuoteAsset")),
    );
    if entry.is_field_present(sf("sfAssetPrice")) {
        price_data.set_field_u64(sf("sfAssetPrice"), entry.get_field_u64(sf("sfAssetPrice")));
    }
    if entry.is_field_present(sf("sfScale")) {
        price_data.set_field_u8(sf("sfScale"), entry.get_field_u8(sf("sfScale")));
    }
    price_data
}

#[allow(dead_code)] // reserve for M7 sweep
fn oracle_price_data_series(
    pairs: std::collections::BTreeMap<(protocol::Currency, protocol::Currency), STObject>,
) -> STArray {
    let mut series = STArray::new(sf("sfPriceDataSeries"));
    series.reserve(pairs.len());
    for price_data in pairs.into_values() {
        series.push_back(price_data);
    }
    series
}

fn oracle_owner_count(pair_count: usize) -> i32 {
    if pair_count > 5 { 2 } else { 1 }
}

fn tx_amm_asset(tx: &STTx, field: &'static protocol::SField) -> Asset {
    if let Some(value) = tx.peek_at_pfield(field) {
        if let Some(issue) = value.as_any().downcast_ref::<STIssue>() {
            return issue.asset();
        }
        if let Some(amount) = value.as_any().downcast_ref::<STAmount>() {
            return amount.asset();
        }
    }
    tx.get_field_issue(field).asset()
}

fn optional_tx_amount(tx: &STTx, field: &'static protocol::SField) -> Option<STAmount> {
    tx.is_field_present(field)
        .then(|| tx.get_field_amount(field))
}

fn check_amm_mptokens_v2_gate<V: ledger::ApplyView>(view: &V, assets: &[Asset]) -> Ter {
    if view.rules().enabled(&protocol::feature_id("MPTokensV2")) {
        return Ter::TES_SUCCESS;
    }

    if assets
        .iter()
        .any(|asset| matches!(asset, Asset::MPTIssue(_)))
    {
        return Ter::TEM_DISABLED;
    }

    Ter::TES_SUCCESS
}

fn account_holds_amm_asset<V: ledger::ApplyView>(
    view: &V,
    account: &AccountID,
    asset: Asset,
    field: &'static protocol::SField,
) -> Result<STAmount, Ter> {
    match asset {
        Asset::Issue(issue) if issue.native() => Ok(
            match view.read(protocol::account_keylet(Uint160::from_void(account.data()))) {
                Ok(Some(sle)) => sle.get_field_amount(sf("sfBalance")),
                Ok(None) => STAmount::from_xrp_amount(XRPAmount::new()),
                Err(_) => return Err(Ter::TEF_BAD_LEDGER),
            },
        ),
        Asset::Issue(issue) => {
            if issue.account == *account {
                return Ok(STAmount::from_iou_amount(field, IOUAmount::new(), issue));
            }
            let mut amount =
                match view.read(protocol::line(*account, issue.account, issue.currency)) {
                    Ok(Some(sle)) => sle.get_field_amount(sf("sfBalance")),
                    Ok(None) => STAmount::from_iou_amount(field, IOUAmount::new(), issue),
                    Err(_) => return Err(Ter::TEF_BAD_LEDGER),
                };
            if *account > issue.account {
                amount.negate();
            }
            amount.set_issuer(issue.account);
            Ok(amount)
        }
        Asset::MPTIssue(issue) => {
            let value = match view.read(protocol::mptoken_keylet_from_mptid(
                issue.mpt_id(),
                Uint160::from_void(account.data()),
            )) {
                Ok(Some(sle)) => {
                    if sle.is_field_present(sf("sfMPTAmount")) {
                        sle.get_field_u64(sf("sfMPTAmount"))
                    } else {
                        0
                    }
                }
                Ok(None) => 0,
                Err(_) => return Err(Ter::TEF_BAD_LEDGER),
            };
            let value = i64::try_from(value).map_err(|_| Ter::TEF_BAD_LEDGER)?;
            Ok(STAmount::from_mpt_amount(
                field,
                MPTAmount::from_value(value),
                issue,
            ))
        }
    }
}

macro_rules! amm_holds_or_return {
    ($view:expr, $account:expr, $asset:expr, $field:expr) => {
        match account_holds_amm_asset($view, $account, $asset, $field) {
            Ok(amount) => amount,
            Err(ter) => return ter,
        }
    };
}

fn amm_deposit_asset<V: ledger::ApplyView>(
    view: &mut V,
    from: &AccountID,
    amm_account: &AccountID,
    amount: &STAmount,
) -> Ter {
    match amount.asset() {
        Asset::Issue(issue) if issue.native() => {
            ledger::ripple_state_helpers::account_send(view, from, amm_account, amount)
        }
        Asset::Issue(_) => amm_transfer_iou_no_fee(view, from, amm_account, amount),
        Asset::MPTIssue(_) => amm_transfer_mpt_no_fee(view, from, amm_account, amount),
    }
}

fn amm_transfer_iou_no_fee<V: ledger::ApplyView>(
    view: &mut V,
    from: &AccountID,
    to: &AccountID,
    amount: &STAmount,
) -> Ter {
    let issue = amount.issue();
    if *from == issue.account || *to == issue.account || issue.account.is_zero() {
        return ledger::ripple_state_helpers::direct_send_no_fee_iou_pub(view, from, to, amount);
    }

    let result =
        ledger::ripple_state_helpers::direct_send_no_fee_iou_pub(view, &issue.account, to, amount);
    if result != Ter::TES_SUCCESS {
        return result;
    }
    ledger::ripple_state_helpers::direct_send_no_fee_iou_pub(view, from, &issue.account, amount)
}

fn amm_transfer_mpt_no_fee<V: ledger::ApplyView>(
    view: &mut V,
    from: &AccountID,
    to: &AccountID,
    amount: &STAmount,
) -> Ter {
    let Asset::MPTIssue(issue) = amount.asset() else {
        return Ter::TEC_INTERNAL;
    };
    let value = amount.mpt().value();
    if value <= 0 || from == to {
        return Ter::TES_SUCCESS;
    }
    let Ok(units) = u64::try_from(value) else {
        return Ter::TEC_INTERNAL;
    };
    let debit_keylet =
        protocol::mptoken_keylet_from_mptid(issue.mpt_id(), Uint160::from_void(from.data()));
    let credit_keylet =
        protocol::mptoken_keylet_from_mptid(issue.mpt_id(), Uint160::from_void(to.data()));
    let debit_token = match view.peek(debit_keylet) {
        Ok(Some(sle)) => sle,
        Ok(None) => return Ter::TEC_AMM_BALANCE,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    let credit_token = match view.peek(credit_keylet) {
        Ok(Some(sle)) => sle,
        Ok(None) => return Ter::TEC_NO_AUTH,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    let debit_balance = debit_token.get_field_u64(sf("sfMPTAmount"));
    let Some(next_debit) = debit_balance.checked_sub(units) else {
        return Ter::TEC_AMM_BALANCE;
    };
    let credit_balance = credit_token.get_field_u64(sf("sfMPTAmount"));
    let Some(next_credit) = credit_balance.checked_add(units) else {
        return Ter::TEC_INTERNAL;
    };

    let mut debit_obj = debit_token.clone_as_object();
    debit_obj.set_field_u64(sf("sfMPTAmount"), next_debit);
    if view
        .update(Arc::new(STLedgerEntry::from_stobject(
            debit_obj,
            *debit_token.key(),
        )))
        .is_err()
    {
        return Ter::TEF_BAD_LEDGER;
    }

    let mut credit_obj = credit_token.clone_as_object();
    credit_obj.set_field_u64(sf("sfMPTAmount"), next_credit);
    if view
        .update(Arc::new(STLedgerEntry::from_stobject(
            credit_obj,
            *credit_token.key(),
        )))
        .is_err()
    {
        return Ter::TEF_BAD_LEDGER;
    }

    Ter::TES_SUCCESS
}

fn amm_withdraw_asset<V: ledger::ApplyView>(
    view: &mut V,
    amm_account: &AccountID,
    account: &AccountID,
    amount: &STAmount,
) -> Ter {
    match amount.asset() {
        Asset::Issue(issue) if issue.native() => {
            ledger::ripple_state_helpers::account_send(view, amm_account, account, amount)
        }
        Asset::Issue(_) => amm_transfer_iou_no_fee(view, amm_account, account, amount),
        Asset::MPTIssue(_) => amm_transfer_mpt_no_fee(view, amm_account, account, amount),
    }
}

/// Pinned `AMMWithdraw::withdraw` `fixAMMv1_2` parity. Before sending a
/// non-XRP pool asset, reserve capacity is checked if the withdrawing account
/// does not yet have the corresponding holding. IOU accountSend creates the
/// trust line; MPT accountSend requires us to create the MPToken first.
fn amm_prepare_withdraw_holding<V: ledger::ApplyView>(
    view: &mut V,
    sttx: &STTx,
    account: &AccountID,
    asset: Asset,
    prior_balance: XRPAmount,
    clawback_issuer: Option<AccountID>,
) -> Ter {
    if !view.rules().enabled(&protocol::feature_id("fixAMMv1_2")) {
        return Ter::TES_SUCCESS;
    }

    let missing = match asset {
        Asset::Issue(issue) => {
            if issue.native() || issue.issuer() == *account {
                return Ter::TES_SUCCESS;
            }
            match view.read(protocol::line(*account, issue.issuer(), issue.currency)) {
                Ok(line) => line.is_none(),
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
        }
        Asset::MPTIssue(issue) => {
            if issue.issuer() == *account {
                return Ter::TES_SUCCESS;
            }
            match view.read(protocol::mptoken_keylet_from_mptid(
                issue.mpt_id(),
                Uint160::from_void(account.data()),
            )) {
                Ok(token) => token.is_none(),
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
        }
    };
    if !missing {
        return Ter::TES_SUCCESS;
    }

    let account_sle = match view.peek(protocol::account_keylet(Uint160::from_void(account.data())))
    {
        Ok(Some(sle)) => sle,
        Ok(None) => return Ter::TEC_INTERNAL,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    let owner_count = ledger::reserve_owner_count(&account_sle, 0);
    let reserve = if owner_count < 2 {
        0_i64
    } else {
        let reserve = ledger::effective_account_reserve(view.fees(), &account_sle, 1, 0);
        let Ok(reserve) = i64::try_from(reserve) else {
            return Ter::TEF_BAD_LEDGER;
        };
        reserve
    };
    let current_balance = account_sle.get_field_amount(sf("sfBalance")).xrp();
    let adjusted_balance = match asset {
        Asset::Issue(_) => std::cmp::max(prior_balance, current_balance),
        Asset::MPTIssue(_) => prior_balance,
    };
    if adjusted_balance.drops() < reserve {
        return Ter::TEC_INSUFFICIENT_RESERVE;
    }

    if let Asset::MPTIssue(issue) = asset {
        let auth = match ledger::mptoken_helpers::require_auth_mpt_with_type(
            view,
            &issue,
            account,
            ledger::mptoken_helpers::MPTAuthType::Weak,
        ) {
            Ok(ter) => ter,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        let authorize_recreated = if auth == Ter::TES_SUCCESS {
            false
        } else if auth == Ter::TEC_NO_AUTH && clawback_issuer.is_some() {
            clawback_issuer == Some(issue.issuer())
        } else {
            return auth;
        };
        let created = ledger::add_empty_holding_with_tx(view, sttx, account, prior_balance, &asset);
        if created != Ter::TES_SUCCESS {
            return created;
        }
        if authorize_recreated {
            let keylet = protocol::mptoken_keylet_from_mptid(
                issue.mpt_id(),
                Uint160::from_void(account.data()),
            );
            let token = match view.peek(keylet) {
                Ok(Some(token)) => token,
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let mut obj = token.clone_as_object();
            obj.set_field_u32(
                sf("sfFlags"),
                token.get_field_u32(sf("sfFlags")) | protocol::lsfMPTAuthorized,
            );
            if view
                .update(Arc::new(STLedgerEntry::from_stobject(obj, *token.key())))
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
        }
    }
    Ter::TES_SUCCESS
}

fn amount_from_number(
    asset: Asset,
    value: RuntimeNumber,
    rounding: RoundingMode,
) -> Option<STAmount> {
    protocol::to_amount_from_number(asset, value, rounding).ok()
}

fn amm_clawback_proportional_amount(
    balance: &STAmount,
    frac: RuntimeNumber,
    rounding: RoundingMode,
) -> Option<STAmount> {
    amount_from_number(
        balance.asset(),
        ledger::amm_helpers::stamount_as_number(balance) * frac,
        rounding,
    )
}

fn amm_clawback_lp_tokens(
    lp_total: &STAmount,
    frac: RuntimeNumber,
    rounding: RoundingMode,
) -> Option<STAmount> {
    amount_from_number(
        lp_total.asset(),
        ledger::amm_helpers::stamount_as_number(lp_total) * frac,
        rounding,
    )
}

fn amm_clawback_math(
    amount: Option<&STAmount>,
    pool1: &STAmount,
    pool2: &STAmount,
    lp_total: &STAmount,
    holder_lp: &STAmount,
    rules: protocol::Rules,
) -> Result<tx::AMMWithdrawApplyMathResult, Ter> {
    let full_withdraw = |holder_lp: &STAmount| -> Result<tx::AMMWithdrawApplyMathResult, Ter> {
        if holder_lp.signum() == 0 {
            return Err(Ter::TEC_AMM_BALANCE);
        }
        let frac = ledger::amm_helpers::stamount_as_number(holder_lp)
            / ledger::amm_helpers::stamount_as_number(lp_total);
        let amount1 = amm_clawback_proportional_amount(pool1, frac, RoundingMode::Downward)
            .ok_or(Ter::TEC_INTERNAL)?;
        let amount2 = amm_clawback_proportional_amount(pool2, frac, RoundingMode::Downward)
            .ok_or(Ter::TEC_INTERNAL)?;
        if amount1.signum() == 0 || amount2.signum() == 0 {
            return Err(Ter::TEC_AMM_FAILED);
        }
        Ok(tx::AMMWithdrawApplyMathResult {
            amount1: Some(amount1),
            amount2: Some(amount2),
            lp_tokens: holder_lp.clone(),
            new_lp_token_balance: lp_total.clone() - holder_lp.clone(),
        })
    };

    let Some(amount) = amount else {
        return full_withdraw(holder_lp);
    };

    let frac = ledger::amm_helpers::stamount_as_number(amount)
        / ledger::amm_helpers::stamount_as_number(pool1);
    let lp_tokens = amm_clawback_lp_tokens(lp_total, frac, RoundingMode::TowardsZero)
        .ok_or(Ter::TEC_INTERNAL)?;
    if lp_tokens > *holder_lp {
        return full_withdraw(holder_lp);
    }

    let (amount1, amount2, lp_tokens) =
        if rules.enabled(&protocol::feature_id("fixAMMClawbackRounding")) {
            let tokens = ledger::amm_helpers::get_rounded_lp_tokens(
                &rules,
                lp_total,
                frac,
                ledger::amm_helpers::IsDeposit::No,
            );
            if tokens.signum() == 0 {
                return Err(Ter::TEC_AMM_INVALID_TOKENS);
            }
            let adjusted_frac =
                ledger::amm_helpers::adjust_frac_by_tokens(&rules, lp_total, &tokens, frac);
            let amount1 = ledger::amm_helpers::get_rounded_asset(
                &rules,
                pool1,
                adjusted_frac,
                ledger::amm_helpers::IsDeposit::No,
            );
            let amount2 = ledger::amm_helpers::get_rounded_asset(
                &rules,
                pool2,
                adjusted_frac,
                ledger::amm_helpers::IsDeposit::No,
            );
            if rules.enabled(&protocol::feature_id("fixCleanup3_4_0"))
                && (amount1.signum() == 0 || amount2.signum() == 0)
            {
                return Err(Ter::TEC_AMM_FAILED);
            }
            (amount1, amount2, tokens)
        } else {
            let amount2 = amm_clawback_proportional_amount(pool2, frac, RoundingMode::TowardsZero)
                .ok_or(Ter::TEC_INTERNAL)?;
            (amount.clone(), amount2, lp_tokens)
        };

    if lp_tokens.signum() <= 0 || lp_tokens > *holder_lp || amount1 > *pool1 || amount2 > *pool2 {
        return Err(Ter::TEC_AMM_INVALID_TOKENS);
    }

    Ok(tx::AMMWithdrawApplyMathResult {
        amount1: Some(amount1),
        amount2: Some(amount2),
        lp_tokens: lp_tokens.clone(),
        new_lp_token_balance: lp_total.clone() - lp_tokens,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AMMClawbackBalanceRead {
    PreAdjustHolder,
    Pool,
    PostAdjustHolder,
}

fn amm_clawback_balance_read_plan(
    fix_amm_clawback_rounding: bool,
) -> &'static [AMMClawbackBalanceRead] {
    const LEGACY: &[AMMClawbackBalanceRead] = &[
        AMMClawbackBalanceRead::Pool,
        AMMClawbackBalanceRead::PostAdjustHolder,
    ];
    const FIXED: &[AMMClawbackBalanceRead] = &[
        AMMClawbackBalanceRead::PreAdjustHolder,
        AMMClawbackBalanceRead::Pool,
        AMMClawbackBalanceRead::PostAdjustHolder,
    ];
    if fix_amm_clawback_rounding {
        FIXED
    } else {
        LEGACY
    }
}

fn amm_math_panic_ter(rules: &protocol::Rules) -> Ter {
    if rules.enabled(&protocol::feature_id("fixCleanup3_4_0")) {
        Ter::TEC_AMM_FAILED
    } else {
        Ter::TEF_EXCEPTION
    }
}

fn direct_send_mpt_no_fee<V: ledger::ApplyView>(
    view: &mut V,
    from: &AccountID,
    to: &AccountID,
    amount: &STAmount,
) -> Ter {
    if amount.signum() <= 0 || from == to {
        return Ter::TES_SUCCESS;
    }
    let Asset::MPTIssue(issue) = amount.asset() else {
        return Ter::TEC_INTERNAL;
    };
    let value = amount.mpt().value();
    let Ok(units) = u64::try_from(value) else {
        return Ter::TEC_INTERNAL;
    };
    let issuer = issue.issuer();
    let issuance_keylet = protocol::mpt_issuance_keylet_from_mptid(issue.mpt_id());
    let issuance = match view.peek(issuance_keylet) {
        Ok(Some(sle)) => sle,
        Ok(None) => return Ter::TEC_OBJECT_NOT_FOUND,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    let outstanding = issuance.get_field_u64(sf("sfOutstandingAmount"));

    if *from == issuer {
        let Some(next) = outstanding.checked_add(units) else {
            return Ter::TEC_INTERNAL;
        };
        let mut obj = issuance.clone_as_object();
        obj.set_field_u64(sf("sfOutstandingAmount"), next);
        if view
            .update(Arc::new(STLedgerEntry::from_stobject(obj, *issuance.key())))
            .is_err()
        {
            return Ter::TEF_BAD_LEDGER;
        }
    } else {
        let debit_keylet =
            protocol::mptoken_keylet_from_mptid(issue.mpt_id(), Uint160::from_void(from.data()));
        let token = match view.peek(debit_keylet) {
            Ok(Some(sle)) => sle,
            Ok(None) => return Ter::TEC_NO_AUTH,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        let balance = token.get_field_u64(sf("sfMPTAmount"));
        let Some(next) = balance.checked_sub(units) else {
            return Ter::TEC_INSUFFICIENT_FUNDS;
        };
        let mut obj = token.clone_as_object();
        obj.set_field_u64(sf("sfMPTAmount"), next);
        if view
            .update(Arc::new(STLedgerEntry::from_stobject(obj, *token.key())))
            .is_err()
        {
            return Ter::TEF_BAD_LEDGER;
        }
    }

    if *to == issuer {
        let issuance = match view.peek(issuance_keylet) {
            Ok(Some(sle)) => sle,
            Ok(None) => return Ter::TEC_OBJECT_NOT_FOUND,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        let outstanding = issuance.get_field_u64(sf("sfOutstandingAmount"));
        let Some(next) = outstanding.checked_sub(units) else {
            return Ter::TEC_INTERNAL;
        };
        let mut obj = issuance.clone_as_object();
        obj.set_field_u64(sf("sfOutstandingAmount"), next);
        if view
            .update(Arc::new(STLedgerEntry::from_stobject(obj, *issuance.key())))
            .is_err()
        {
            return Ter::TEF_BAD_LEDGER;
        }
    } else {
        let credit_keylet =
            protocol::mptoken_keylet_from_mptid(issue.mpt_id(), Uint160::from_void(to.data()));
        let token = match view.peek(credit_keylet) {
            Ok(Some(sle)) => sle,
            Ok(None) => return Ter::TEC_NO_AUTH,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        let balance = token.get_field_u64(sf("sfMPTAmount"));
        let Some(next) = balance.checked_add(units) else {
            return Ter::TEC_INTERNAL;
        };
        let mut obj = token.clone_as_object();
        obj.set_field_u64(sf("sfMPTAmount"), next);
        if view
            .update(Arc::new(STLedgerEntry::from_stobject(obj, *token.key())))
            .is_err()
        {
            return Ter::TEF_BAD_LEDGER;
        }
    }

    Ter::TES_SUCCESS
}

fn delegate_reserve_balance_from_lookup(
    account: Result<Option<Arc<STLedgerEntry>>, ledger::ViewError>,
) -> Result<i64, Ter> {
    match account {
        Ok(Some(sle)) => Ok(sle.get_field_amount(sf("sfBalance")).xrp().drops()),
        Ok(None) => Err(Ter::TEF_INTERNAL),
        Err(_) => Err(Ter::TEF_BAD_LEDGER),
    }
}

fn finish_delegate_apply(result: Ter, failure: Option<Ter>) -> Ter {
    failure.unwrap_or(result)
}

fn amm_clawback_send_amount<V: ledger::ApplyView>(
    view: &mut V,
    holder: &AccountID,
    issuer: &AccountID,
    amount: &STAmount,
) -> Ter {
    match amount.asset() {
        Asset::Issue(issue) if issue.native() => Ter::TEM_MALFORMED,
        Asset::Issue(_) => amm_transfer_iou_no_fee(view, holder, issuer, amount),
        Asset::MPTIssue(_) => direct_send_mpt_no_fee(view, holder, issuer, amount),
    }
}

fn amm_clawback_asset_allowed<V: ledger::ApplyView>(
    view: &mut V,
    issuer: &AccountID,
    issuer_sle: &STLedgerEntry,
    asset: Asset,
) -> Result<bool, Ter> {
    Ok(match asset {
        Asset::Issue(issue) => {
            !issue.native()
                && issue.account == *issuer
                && issuer_sle.is_flag(protocol::lsfAllowTrustLineClawback)
                && !issuer_sle.is_flag(protocol::lsfNoFreeze)
        }
        Asset::MPTIssue(issue) => view
            .peek(protocol::mpt_issuance_keylet_from_mptid(issue.mpt_id()))
            .map_err(|_| Ter::TEF_BAD_LEDGER)?
            .is_some_and(|sle| {
                sle.is_flag(protocol::lsfMPTCanClawback)
                    && sle.get_account_id(sf("sfIssuer")) == *issuer
            }),
    })
}

fn legacy_amm_clawback_direct_dispatch<V: ledger::ApplyView>(view: &mut V, sttx: &STTx) -> Ter {
    let issuer = sttx.get_account_id(sf("sfAccount"));
    let holder = sttx.get_account_id(sf("sfHolder"));
    let amount = sttx.get_field_amount(sf("sfAmount"));
    let Asset::Issue(issue) = amount.asset() else {
        return Ter::TES_SUCCESS;
    };
    if issue.native() {
        return Ter::TES_SUCCESS;
    }

    let line_keylet = protocol::line(issuer, holder, issue.currency);
    let line = match view.peek(line_keylet) {
        Ok(Some(line)) => line,
        Ok(None) => return Ter::TES_SUCCESS,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    let b_high = holder > issuer;
    let current_balance = line.get_field_amount(sf("sfBalance"));
    let holder_balance = if b_high {
        let mut balance = current_balance.clone();
        balance.negate();
        balance
    } else {
        current_balance.clone()
    };
    let mut normalized_amount = amount;
    normalized_amount.set_issue(protocol::Issue {
        account: issuer,
        currency: issue.currency,
    });
    let clawback_actual = if normalized_amount > holder_balance {
        holder_balance
    } else {
        normalized_amount
    };
    let new_balance = if b_high {
        current_balance + clawback_actual
    } else {
        current_balance - clawback_actual
    };

    let mut obj = line.clone_as_object();
    obj.set_field_amount(sf("sfBalance"), new_balance);
    if view
        .update(Arc::new(STLedgerEntry::from_stobject(obj, *line.key())))
        .is_err()
    {
        return Ter::TEF_INTERNAL;
    }

    Ter::TES_SUCCESS
}

fn escrow_mpt_unlock_amounts<V: ledger::ApplyView>(
    view: &V,
    amount: &STAmount,
    locked_rate: u32,
    sender: &AccountID,
    receiver: &AccountID,
) -> Result<(STAmount, STAmount), Ter> {
    let Asset::MPTIssue(issue) = amount.asset() else {
        return Ok((amount.clone(), amount.clone()));
    };
    let issuer = issue.issuer();
    let mut rate = protocol::Rate::new(locked_rate);
    let current_rate = ledger::mptoken_helpers::transfer_rate_mpt(view, issue.mpt_id())
        .map_err(|_| Ter::TEF_BAD_LEDGER)?;
    if current_rate < rate {
        rate = current_rate;
    }

    if sender != &issuer && receiver != &issuer && rate != protocol::PARITY_RATE {
        let net_amount = if view
            .rules()
            .enabled(&protocol::feature_id("fixCleanup3_4_0"))
        {
            protocol::mpt_amount::mul_ratio(
                amount.mpt(),
                protocol::PARITY_RATE.value,
                rate.value,
                false,
            )
            .map(|net| STAmount::from_mpt_amount(sf("sfAmount"), net, issue))
            .map_err(|_| Ter::TEC_INTERNAL)?
        } else {
            // Preserve rippled's legacy two-subtraction path exactly. For an
            // integral MPT this is observably different from returning the
            // rounded quotient directly: divideRound rounds the fee basis up,
            // then STAmount subtraction charges only the resulting integral
            // fee. fixCleanup3_4_0 deliberately replaces this with the direct
            // round-down mulRatio path above.
            let transfer_fee = amount.clone() - protocol::divide_round(amount, rate, true);
            amount.clone() - transfer_fee
        };
        return Ok((net_amount, amount.clone()));
    }
    Ok((amount.clone(), amount.clone()))
}

fn escrow_iou_unlock_amount<V: ledger::ApplyView>(
    view: &mut V,
    amount: &STAmount,
    locked_rate: u32,
    sender: &AccountID,
    receiver: &AccountID,
) -> Result<STAmount, Ter> {
    let Asset::Issue(issue) = amount.asset() else {
        return Ok(amount.clone());
    };
    let issuer = issue.issuer();
    let mut rate = protocol::Rate::new(locked_rate);
    let current_rate = protocol::Rate::new(
        ledger::ripple_state_helpers::try_transfer_rate(view, &issuer)
            .map_err(|_| Ter::TEF_BAD_LEDGER)?,
    );
    if current_rate < rate {
        rate = current_rate;
    }

    if sender != &issuer && receiver != &issuer && rate != protocol::PARITY_RATE {
        return Ok(protocol::divide_round(amount, rate, true));
    }
    Ok(amount.clone())
}

fn unlock_escrow_iou<V: ledger::ApplyView>(
    view: &mut V,
    amount: &STAmount,
    locked_rate: u32,
    sender: &AccountID,
    receiver: &AccountID,
    submitter: &AccountID,
    pre_fee_balance_drops: Option<i64>,
    reserve_sponsor: Option<&Arc<STLedgerEntry>>,
) -> Ter {
    let Asset::Issue(issue) = amount.asset() else {
        return Ter::TEF_INTERNAL;
    };
    let issuer = issue.issuer();
    if sender == &issuer {
        return Ter::TEC_INTERNAL;
    }
    if receiver == &issuer {
        return Ter::TES_SUCCESS;
    }

    let line_keylet = protocol::line(*receiver, issuer, issue.currency);
    let line_exists = match view.exists(line_keylet) {
        Ok(exists) => exists,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    let receiver_created_line = !line_exists && receiver == submitter;
    if receiver_created_line {
        let destination_keylet = protocol::account_keylet(Uint160::from_void(receiver.data()));
        let destination_sle = match view.peek(destination_keylet) {
            Ok(Some(sle)) => sle,
            Ok(None) => return Ter::TEC_INTERNAL,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        match check_cash_has_object_reserve(
            view,
            &destination_sle,
            pre_fee_balance_drops,
            reserve_sponsor,
        ) {
            Ok(true) => {}
            Ok(false) => return Ter::TEC_NO_LINE_INSUF_RESERVE,
            Err(ter) => return ter,
        }
        let limit = STAmount::new_with_asset(
            sf("sfLimitAmount"),
            Asset::Issue(protocol::Issue::new(issue.currency, *receiver)),
            0,
            0,
            false,
        );
        let created = crate::state::trust_set::trust_create(
            view,
            *receiver > issuer,
            receiver,
            &issuer,
            line_keylet.key,
            &destination_sle,
            false,
            !destination_sle.is_flag(protocol::lsfDefaultRipple),
            false,
            false,
            &limit,
            0,
            0,
            reserve_sponsor,
        );
        if created != Ter::TES_SUCCESS {
            return created;
        }
    } else if !line_exists {
        return Ter::TEC_NO_LINE;
    }

    let final_amount = match escrow_iou_unlock_amount(view, amount, locked_rate, sender, receiver) {
        Ok(amount) => amount,
        Err(ter) => return ter,
    };
    if !receiver_created_line {
        let line = match view.peek(line_keylet) {
            Ok(Some(sle)) => sle,
            Ok(None) => return Ter::TEC_INTERNAL,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        let receiver_is_low = issuer > *receiver;
        let line_limit = line.get_field_amount(if receiver_is_low {
            sf("sfLowLimit")
        } else {
            sf("sfHighLimit")
        });
        let mut line_balance = line.get_field_amount(sf("sfBalance"));
        if !receiver_is_low {
            line_balance.negate();
        }
        line_balance += final_amount.clone();
        if line_limit < line_balance {
            return Ter::TEC_LIMIT_EXCEEDED;
        }
    }

    ledger::ripple_state_helpers::direct_send_no_fee_iou_pub(view, &issuer, receiver, &final_amount)
}

fn check_mpt_check_create_allowed<V: ledger::ApplyView>(
    view: &V,
    source: &AccountID,
    destination: &AccountID,
    amount: &STAmount,
) -> Ter {
    let Asset::MPTIssue(issue) = amount.asset() else {
        return Ter::TES_SUCCESS;
    };
    let issuer = issue.issuer();

    if source != &issuer {
        let frozen =
            frozen_mpt_result(ledger::mptoken_helpers::is_frozen_mpt(view, source, &issue));
        if frozen != Ter::TES_SUCCESS {
            return frozen;
        }
    }
    if destination != &issuer {
        let frozen = frozen_mpt_result(ledger::mptoken_helpers::is_frozen_mpt(
            view,
            destination,
            &issue,
        ));
        if frozen != Ter::TES_SUCCESS {
            return frozen;
        }
    }

    ledger::mptoken_helpers::can_transfer_mpt(view, &issue, source, destination)
        .unwrap_or(Ter::TEF_BAD_LEDGER)
}

fn frozen_mpt_result(result: Result<bool, ledger::ViewError>) -> Ter {
    match result {
        Ok(true) => Ter::TEC_LOCKED,
        Ok(false) => Ter::TES_SUCCESS,
        Err(_) => Ter::TEF_BAD_LEDGER,
    }
}

fn nft_accept_delete_result(result: Result<bool, ledger::ViewError>) -> Ter {
    match result {
        Ok(true) => Ter::TES_SUCCESS,
        // NFTokenAcceptOffer::doApply treats a structurally undeletable offer
        // as its defensive tecINTERNAL branch.
        Ok(false) => Ter::TEC_INTERNAL,
        // C++ ApplyView operations are not fallible at this boundary. Rust's
        // explicit backing-store failure must not be collapsed into a tec.
        Err(_) => Ter::TEF_BAD_LEDGER,
    }
}

fn signer_list_exists_from_lookup(result: Result<bool, ledger::ViewError>) -> Result<bool, Ter> {
    result.map_err(|_| Ter::TEF_BAD_LEDGER)
}

fn required_source_account_from_lookup(
    result: Result<Option<Arc<STLedgerEntry>>, ledger::ViewError>,
) -> Result<(), Ter> {
    match result {
        Ok(Some(_)) => Ok(()),
        Ok(None) => Err(Ter::TEF_INTERNAL),
        Err(_) => Err(Ter::TEF_BAD_LEDGER),
    }
}

fn check_mpt_check_cash_allowed<V: ledger::ApplyView>(
    view: &mut V,
    source: &AccountID,
    destination: &AccountID,
    amount: &STAmount,
) -> Ter {
    let Asset::MPTIssue(issue) = amount.asset() else {
        return Ter::TES_SUCCESS;
    };
    let issuer = issue.issuer();
    match view.peek(protocol::account_keylet(Uint160::from_void(issuer.data()))) {
        Ok(Some(_)) => {}
        Ok(None) => return Ter::TEC_NO_ISSUER,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    }
    let auth = ledger::mptoken_helpers::require_auth_mpt(view, &issue, destination)
        .unwrap_or(Ter::TEF_BAD_LEDGER);
    if auth != Ter::TES_SUCCESS {
        return auth;
    }
    if destination != &issuer {
        let frozen = frozen_mpt_result(ledger::mptoken_helpers::is_frozen_mpt(
            view,
            destination,
            &issue,
        ));
        if frozen != Ter::TES_SUCCESS {
            return frozen;
        }
    }
    let transfer = ledger::mptoken_helpers::can_transfer_mpt(view, &issue, source, destination)
        .unwrap_or(Ter::TEF_BAD_LEDGER);
    if transfer != Ter::TES_SUCCESS {
        return transfer;
    }
    Ter::TES_SUCCESS
}

fn check_cash_reserve_sponsor<V: ledger::ApplyView>(
    view: &mut V,
    sttx: &STTx,
) -> Result<Option<Arc<STLedgerEntry>>, Ter> {
    if !sttx.is_field_present(sf("sfSponsor"))
        || !sttx.is_field_present(sf("sfSponsorFlags"))
        || !ledger::is_reserve_sponsored(sttx.get_field_u32(sf("sfSponsorFlags")))
    {
        return Ok(None);
    }
    let sponsor = sttx.get_account_id(sf("sfSponsor"));
    view.peek(protocol::account_keylet(Uint160::from_void(sponsor.data())))
        .map_err(|_| Ter::TEF_BAD_LEDGER)?
        .ok_or(Ter::TEC_INTERNAL)
        .map(Some)
}

fn check_cash_has_object_reserve<V: ledger::ApplyView>(
    view: &V,
    destination_sle: &STLedgerEntry,
    destination_pre_fee_balance: Option<i64>,
    sponsor_sle: Option<&Arc<STLedgerEntry>>,
) -> Result<bool, Ter> {
    let reserve_sle = sponsor_sle.map_or(destination_sle, |sle| sle.as_ref());
    let balance = sponsor_sle.map_or_else(
        || {
            destination_pre_fee_balance.unwrap_or_else(|| {
                destination_sle
                    .get_field_amount(sf("sfBalance"))
                    .xrp()
                    .drops()
            })
        },
        |sle| sle.get_field_amount(sf("sfBalance")).xrp().drops(),
    );
    let reserve = i64::try_from(ledger::effective_account_reserve(
        view.fees(),
        reserve_sle,
        1,
        0,
    ))
    .map_err(|_| Ter::TEF_BAD_LEDGER)?;
    if balance < reserve {
        return Ok(false);
    }

    if let Some(sponsor_sle) = sponsor_sle {
        let sponsor = sponsor_sle.get_account_id(sf("sfAccount"));
        let destination = destination_sle.get_account_id(sf("sfAccount"));
        if let Some(sponsorship) = view
            .read(protocol::sponsorship_keylet(
                Uint160::from_void(sponsor.data()),
                Uint160::from_void(destination.data()),
            ))
            .map_err(|_| Ter::TEF_BAD_LEDGER)?
            && sponsorship.get_field_u32(sf("sfRemainingOwnerCount")) < 1
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn check_mpt_amm_asset_allowed<V: ledger::ApplyView>(
    view: &V,
    account: &AccountID,
    asset: Asset,
    require_holding: bool,
) -> Ter {
    let Asset::MPTIssue(issue) = asset else {
        return Ter::TES_SUCCESS;
    };
    let issuer = issue.issuer();

    if require_holding && account != &issuer {
        match view.read(protocol::mptoken_keylet_from_mptid(
            issue.mpt_id(),
            Uint160::from_void(account.data()),
        )) {
            Ok(Some(_)) => {}
            Ok(None) => return Ter::TEC_NO_AUTH,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        }
    }

    let auth = ledger::mptoken_helpers::require_auth_mpt(view, &issue, account)
        .unwrap_or(Ter::TEF_BAD_LEDGER);
    if auth != Ter::TES_SUCCESS {
        return auth;
    }

    let frozen = frozen_mpt_result(ledger::mptoken_helpers::is_frozen_mpt(
        view, account, &issue,
    ));
    if frozen != Ter::TES_SUCCESS {
        return frozen;
    }

    ledger::mptoken_helpers::can_mpt_trade_and_transfer(view, &asset, account, account)
        .unwrap_or(Ter::TEF_BAD_LEDGER)
}

fn check_mpt_amm_withdraw_asset_allowed<V: ledger::ApplyView>(
    view: &V,
    account: &AccountID,
    asset: Asset,
) -> Ter {
    let Asset::MPTIssue(issue) = asset else {
        return Ter::TES_SUCCESS;
    };

    // #7040: AMMWithdraw is a recovery path. It must not require CanTransfer
    // or CanTrade, but it still rejects globally/individually locked MPTs.
    let frozen = frozen_mpt_result(ledger::mptoken_helpers::is_frozen_mpt(
        view, account, &issue,
    ));
    if frozen != Ter::TES_SUCCESS {
        return frozen;
    }

    let auth = ledger::mptoken_helpers::require_auth_mpt(view, &issue, account)
        .unwrap_or(Ter::TEF_BAD_LEDGER);
    if auth != Ter::TES_SUCCESS {
        return auth;
    }

    Ter::TES_SUCCESS
}

fn check_mpt_amm_pool_asset_unlocked<V: ledger::ApplyView>(
    view: &V,
    amm_account: &AccountID,
    asset: Asset,
) -> Ter {
    let Asset::MPTIssue(issue) = asset else {
        return Ter::TES_SUCCESS;
    };

    let frozen = frozen_mpt_result(ledger::mptoken_helpers::is_frozen_mpt(
        view,
        amm_account,
        &issue,
    ));
    if frozen != Ter::TES_SUCCESS {
        return frozen;
    }

    Ter::TES_SUCCESS
}

fn nft_page_mask() -> Uint256 {
    protocol::nft_page_mask()
}

fn nft_owner_min(owner: &AccountID) -> Keylet {
    protocol::nft_page_min_keylet(Uint160::from_void(owner.data()))
}

fn nft_owner_max(owner: &AccountID) -> Keylet {
    protocol::nft_page_max_keylet(Uint160::from_void(owner.data()))
}

fn nft_page_for_token_keylet(owner: &AccountID, token_id: Uint256) -> Keylet {
    protocol::nft_page_keylet(nft_owner_min(owner), token_id)
}

fn nft_compare_tokens(left: Uint256, right: Uint256) -> std::cmp::Ordering {
    let mask = nft_page_mask();
    let left_low = left & mask;
    let right_low = right & mask;
    left_low.cmp(&right_low).then_with(|| left.cmp(&right))
}

fn starray_from_tokens(tokens: Vec<STObject>) -> STArray {
    let mut array = STArray::new(sf("sfNFTokens"));
    array.reserve(tokens.len());
    for token in tokens {
        array.push_back(token);
    }
    array
}

fn number_from_i64(value: i64) -> RuntimeNumber {
    RuntimeNumber::from_i64(value)
}

fn amm_lp_holds_in_view<V: ledger::ApplyView>(
    view: &mut V,
    amm_sle: &STLedgerEntry,
    lp_account: AccountID,
) -> Result<Option<STAmount>, ledger::ViewError> {
    let lp_tokens = amm_sle.get_field_amount(sf("sfLPTokenBalance"));
    let Asset::Issue(lp_issue) = lp_tokens.asset() else {
        return Ok(None);
    };
    let amm_account = amm_sle.get_account_id(sf("sfAccount"));
    let keylet = protocol::line(lp_account, amm_account, lp_issue.currency);
    let Some(sle) = view.peek(keylet)? else {
        return Ok(None);
    };
    let mut amount = sle.get_field_amount(sf("sfBalance"));
    if lp_account > amm_account {
        amount.negate();
    }
    amount.set_issuer(amm_account);
    Ok(Some(amount))
}

fn nft_locate_page<V: ledger::ApplyView>(
    view: &mut V,
    owner: &AccountID,
    token_id: Uint256,
) -> Result<Option<Arc<STLedgerEntry>>, ledger::ViewError> {
    let first = nft_page_for_token_keylet(owner, token_id);
    let last = nft_owner_max(owner);
    let candidate = view
        .succ(first.key, Some(last.key.next()))?
        .unwrap_or(last.key);
    view.peek(Keylet::new(LedgerEntryType::NFTokenPage, candidate))
}

fn nft_find_token_and_page<V: ledger::ApplyView>(
    view: &mut V,
    owner: &AccountID,
    token_id: Uint256,
) -> Result<Option<(STObject, Arc<STLedgerEntry>)>, ledger::ViewError> {
    let Some(page) = nft_locate_page(view, owner, token_id)? else {
        return Ok(None);
    };

    for token in page.get_field_array(sf("sfNFTokens")).iter() {
        if token.get_field_h256(sf("sfNFTokenID")) == token_id {
            return Ok(Some((token.clone(), page)));
        }
    }

    Ok(None)
}

fn nft_page_link<V: ledger::ApplyView>(
    view: &mut V,
    page: &Arc<STLedgerEntry>,
    field: &'static protocol::SField,
) -> Result<Option<Arc<STLedgerEntry>>, ledger::ViewError> {
    if !page.is_field_present(field) {
        return Ok(None);
    }

    let key = page.get_field_h256(field);
    view.peek(Keylet::new(LedgerEntryType::NFTokenPage, key))
}

fn nft_merge_pages<V: ledger::ApplyView>(
    view: &mut V,
    first: Arc<STLedgerEntry>,
    second: Arc<STLedgerEntry>,
) -> Result<bool, ledger::ViewError> {
    if first.key() >= second.key() {
        return Err(ledger::ViewError::Conversion(
            "NFToken pages passed to merge out of order".to_owned(),
        ));
    }
    if !first.is_field_present(sf("sfNextPageMin"))
        || first.get_field_h256(sf("sfNextPageMin")) != *second.key()
        || !second.is_field_present(sf("sfPreviousPageMin"))
        || second.get_field_h256(sf("sfPreviousPageMin")) != *first.key()
    {
        return Err(ledger::ViewError::Conversion(
            "NFToken page merge encountered broken links".to_owned(),
        ));
    }

    let first_tokens: Vec<_> = first
        .get_field_array(sf("sfNFTokens"))
        .iter()
        .cloned()
        .collect();
    let second_tokens: Vec<_> = second
        .get_field_array(sf("sfNFTokens"))
        .iter()
        .cloned()
        .collect();
    if first_tokens.len() + second_tokens.len() > protocol::DIR_MAX_TOKENS_PER_PAGE {
        return Ok(false);
    }

    let mut merged = first_tokens;
    merged.extend(second_tokens);
    merged.sort_by(|left, right| {
        nft_compare_tokens(
            left.get_field_h256(sf("sfNFTokenID")),
            right.get_field_h256(sf("sfNFTokenID")),
        )
    });

    let mut second_obj = second.clone_as_object();
    second_obj.set_field_array(sf("sfNFTokens"), starray_from_tokens(merged));
    if second_obj.is_field_present(sf("sfPreviousPageMin")) {
        second_obj.make_field_absent(sf("sfPreviousPageMin"));
    }

    if first.is_field_present(sf("sfPreviousPageMin")) {
        let previous_key = first.get_field_h256(sf("sfPreviousPageMin"));
        if let Some(previous) =
            view.peek(Keylet::new(LedgerEntryType::NFTokenPage, previous_key))?
        {
            let mut previous_obj = previous.clone_as_object();
            previous_obj.set_field_h256(sf("sfNextPageMin"), *second.key());
            view.update(Arc::new(STLedgerEntry::from_stobject(
                previous_obj,
                *previous.key(),
            )))?;
            second_obj.set_field_h256(sf("sfPreviousPageMin"), previous_key);
        } else {
            return Err(ledger::ViewError::Conversion(
                "NFToken page merge could not load previous page".to_owned(),
            ));
        }
    }

    view.update(Arc::new(STLedgerEntry::from_stobject(
        second_obj,
        *second.key(),
    )))?;
    view.erase(first)?;

    Ok(true)
}

fn nft_remove_token_from_page<V: ledger::ApplyView>(
    view: &mut V,
    owner: &AccountID,
    token_id: Uint256,
    current: Arc<STLedgerEntry>,
) -> Ter {
    let tokens = current.get_field_array(sf("sfNFTokens"));
    let mut kept = Vec::new();
    let mut removed = false;
    for token in tokens.iter() {
        if token.get_field_h256(sf("sfNFTokenID")) == token_id {
            removed = true;
        } else {
            kept.push(token.clone());
        }
    }

    if !removed {
        return Ter::TEC_NO_ENTRY;
    }

    let previous = match nft_page_link(view, &current, sf("sfPreviousPageMin")) {
        Ok(page) => page,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    let next = match nft_page_link(view, &current, sf("sfNextPageMin")) {
        Ok(page) => page,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    if !kept.is_empty() {
        let mut obj = current.clone_as_object();
        obj.set_field_array(sf("sfNFTokens"), starray_from_tokens(kept));
        let mut updated_current = Arc::new(STLedgerEntry::from_stobject(obj, *current.key()));
        if view.update(updated_current.clone()).is_err() {
            return Ter::TEF_BAD_LEDGER;
        }

        let mut owner_count_delta = 0;
        if let Some(prev) = previous.clone() {
            match nft_merge_pages(view, prev, updated_current.clone()) {
                Ok(true) => {
                    owner_count_delta -= 1;
                    // `mergePages(prev, curr)` updates `curr` with both
                    // pages' tokens. Reload it before attempting the second
                    // merge; otherwise the stale pre-merge SLE would omit
                    // every token moved from `prev` when consolidating three
                    // pages into one.
                    updated_current = match view.peek(Keylet::new(
                        LedgerEntryType::NFTokenPage,
                        *updated_current.key(),
                    )) {
                        Ok(Some(page)) => page,
                        Ok(None) => return Ter::TEF_BAD_LEDGER,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    };
                }
                Ok(false) => {}
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
        }
        if let Some(next_page) = next {
            match nft_merge_pages(view, updated_current, next_page) {
                Ok(true) => owner_count_delta -= 1,
                Ok(false) => {}
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
        }
        if owner_count_delta != 0 {
            let account =
                match view.peek(protocol::account_keylet(Uint160::from_void(owner.data()))) {
                    Ok(Some(account)) => account,
                    Ok(None) | Err(_) => return Ter::TEF_BAD_LEDGER,
                };
            if ledger::adjust_owner_count(view, &account, owner_count_delta).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
        }
        return Ter::TES_SUCCESS;
    }

    if let Some(prev) = previous.clone() {
        if view
            .rules()
            .enabled(&protocol::feature_id("fixNFTokenPageLinks"))
            && (*current.key() & nft_page_mask()) == nft_page_mask()
        {
            let mut current_obj = current.clone_as_object();
            current_obj.set_field_array(sf("sfNFTokens"), prev.get_field_array(sf("sfNFTokens")));
            if prev.is_field_present(sf("sfPreviousPageMin")) {
                let prev_link = prev.get_field_h256(sf("sfPreviousPageMin"));
                current_obj.set_field_h256(sf("sfPreviousPageMin"), prev_link);
                match view.peek(Keylet::new(LedgerEntryType::NFTokenPage, prev_link)) {
                    Ok(Some(new_prev)) => {
                        let mut new_prev_obj = new_prev.clone_as_object();
                        new_prev_obj.set_field_h256(sf("sfNextPageMin"), *current.key());
                        if view
                            .update(Arc::new(STLedgerEntry::from_stobject(
                                new_prev_obj,
                                *new_prev.key(),
                            )))
                            .is_err()
                        {
                            return Ter::TEF_BAD_LEDGER;
                        }
                    }
                    Ok(None) => return Ter::TEF_BAD_LEDGER,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                }
            } else if current_obj.is_field_present(sf("sfPreviousPageMin")) {
                current_obj.make_field_absent(sf("sfPreviousPageMin"));
            }

            let account =
                match view.peek(protocol::account_keylet(Uint160::from_void(owner.data()))) {
                    Ok(Some(account)) => account,
                    Ok(None) | Err(_) => return Ter::TEF_BAD_LEDGER,
                };
            if ledger::adjust_owner_count(view, &account, -1).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            if view
                .update(Arc::new(STLedgerEntry::from_stobject(
                    current_obj,
                    *current.key(),
                )))
                .is_err()
                || view.erase(prev).is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            return Ter::TES_SUCCESS;
        }

        let mut prev_obj = prev.clone_as_object();
        if let Some(next_page) = next.clone() {
            prev_obj.set_field_h256(sf("sfNextPageMin"), *next_page.key());
        } else if prev_obj.is_field_present(sf("sfNextPageMin")) {
            prev_obj.make_field_absent(sf("sfNextPageMin"));
        }
        if view
            .update(Arc::new(STLedgerEntry::from_stobject(
                prev_obj,
                *prev.key(),
            )))
            .is_err()
        {
            return Ter::TEF_BAD_LEDGER;
        }
    }

    if let Some(next_page) = next.clone() {
        let mut next_obj = next_page.clone_as_object();
        if let Some(prev) = previous.clone() {
            next_obj.set_field_h256(sf("sfPreviousPageMin"), *prev.key());
        } else if next_obj.is_field_present(sf("sfPreviousPageMin")) {
            next_obj.make_field_absent(sf("sfPreviousPageMin"));
        }
        if view
            .update(Arc::new(STLedgerEntry::from_stobject(
                next_obj,
                *next_page.key(),
            )))
            .is_err()
        {
            return Ter::TEF_BAD_LEDGER;
        }
    }

    if view.erase(current).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }

    let mut owner_count_delta = -1;
    if let (Some(prev), Some(next_page)) = (previous, next) {
        match nft_merge_pages(view, prev, next_page) {
            Ok(true) => owner_count_delta -= 1,
            Ok(false) => {}
            Err(_) => return Ter::TEF_BAD_LEDGER,
        }
    }

    let account = match view.peek(protocol::account_keylet(Uint160::from_void(owner.data()))) {
        Ok(Some(account)) => account,
        Ok(None) | Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    if ledger::adjust_owner_count(view, &account, owner_count_delta).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }

    Ter::TES_SUCCESS
}

fn nft_get_page_for_token<V: ledger::ApplyView>(
    view: &mut V,
    owner: &AccountID,
    token_id: Uint256,
) -> Result<Option<Arc<STLedgerEntry>>, ledger::ViewError> {
    let base = nft_owner_min(owner);
    let first = protocol::nft_page_keylet(base, token_id);
    let last = nft_owner_max(owner);
    let candidate = view
        .succ(first.key, Some(last.key.next()))?
        .unwrap_or(last.key);

    if let Some(page) = view.peek(Keylet::new(LedgerEntryType::NFTokenPage, candidate))? {
        if page.get_field_array(sf("sfNFTokens")).len() != protocol::DIR_MAX_TOKENS_PER_PAGE {
            return Ok(Some(page));
        }

        let mut tokens: Vec<_> = page
            .get_field_array(sf("sfNFTokens"))
            .iter()
            .cloned()
            .collect();
        let split_cmp = tokens[(protocol::DIR_MAX_TOKENS_PER_PAGE / 2) - 1]
            .get_field_h256(sf("sfNFTokenID"))
            & nft_page_mask();
        let mut split_index = (protocol::DIR_MAX_TOKENS_PER_PAGE / 2..tokens.len())
            .find(|index| {
                (tokens[*index].get_field_h256(sf("sfNFTokenID")) & nft_page_mask()) != split_cmp
            })
            .unwrap_or(tokens.len());
        if split_index == tokens.len() {
            split_index = tokens
                .iter()
                .position(|token| {
                    (token.get_field_h256(sf("sfNFTokenID")) & nft_page_mask()) == split_cmp
                })
                .unwrap_or(tokens.len());
        }
        if split_index == tokens.len() {
            return Ok(None);
        }
        if split_index == 0 {
            match (token_id & nft_page_mask()).cmp(&split_cmp) {
                std::cmp::Ordering::Equal => return Ok(None),
                std::cmp::Ordering::Greater => split_index = tokens.len(),
                std::cmp::Ordering::Less => {}
            }
        }

        let carried = tokens.split_off(split_index);
        let token_id_for_new_page = if tokens.len() == protocol::DIR_MAX_TOKENS_PER_PAGE {
            tokens[protocol::DIR_MAX_TOKENS_PER_PAGE - 1]
                .get_field_h256(sf("sfNFTokenID"))
                .next()
        } else {
            carried[0].get_field_h256(sf("sfNFTokenID"))
        };

        let new_page_keylet = protocol::nft_page_keylet(base, token_id_for_new_page);
        let mut new_page = STLedgerEntry::new(new_page_keylet);
        new_page.set_field_array(sf("sfNFTokens"), starray_from_tokens(tokens));
        new_page.set_field_h256(sf("sfNextPageMin"), *page.key());

        if page.is_field_present(sf("sfPreviousPageMin")) {
            let previous_key = page.get_field_h256(sf("sfPreviousPageMin"));
            new_page.set_field_h256(sf("sfPreviousPageMin"), previous_key);
            let previous = view
                .peek(Keylet::new(LedgerEntryType::NFTokenPage, previous_key))?
                .ok_or_else(|| {
                    ledger::ViewError::Conversion(
                        "NFToken page split encountered a broken previous link".to_owned(),
                    )
                })?;
            let mut previous_obj = previous.clone_as_object();
            previous_obj.set_field_h256(sf("sfNextPageMin"), new_page_keylet.key);
            view.update(Arc::new(STLedgerEntry::from_stobject(
                previous_obj,
                *previous.key(),
            )))?;
        }

        view.insert(Arc::new(new_page))?;

        let mut page_obj = page.clone_as_object();
        page_obj.set_field_array(sf("sfNFTokens"), starray_from_tokens(carried));
        page_obj.set_field_h256(sf("sfPreviousPageMin"), new_page_keylet.key);
        view.update(Arc::new(STLedgerEntry::from_stobject(
            page_obj,
            *page.key(),
        )))?;

        let account = view
            .peek(protocol::account_keylet(Uint160::from_void(owner.data())))?
            .ok_or_else(|| ledger::ViewError::Conversion("NFToken owner disappeared".to_owned()))?;
        ledger::adjust_owner_count(view, &account, 1)?;

        return if first.key < new_page_keylet.key {
            view.peek(new_page_keylet)
        } else {
            view.peek(Keylet::new(LedgerEntryType::NFTokenPage, *page.key()))
        };
    }

    let mut page = STLedgerEntry::new(last);
    page.set_field_array(sf("sfNFTokens"), STArray::new(sf("sfNFTokens")));
    let page = Arc::new(page);
    view.insert(page.clone())?;
    let account = view
        .peek(protocol::account_keylet(Uint160::from_void(owner.data())))?
        .ok_or_else(|| ledger::ViewError::Conversion("NFToken owner disappeared".to_owned()))?;
    ledger::adjust_owner_count(view, &account, 1)?;
    Ok(Some(page))
}

fn nft_insert_token<V: ledger::ApplyView>(view: &mut V, owner: &AccountID, token: STObject) -> Ter {
    let token_id = token.get_field_h256(sf("sfNFTokenID"));
    let page = match nft_get_page_for_token(view, owner, token_id) {
        Ok(Some(page)) => page,
        Ok(None) => return Ter::TEC_NO_SUITABLE_NFTOKEN_PAGE,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    let mut tokens: Vec<_> = page
        .get_field_array(sf("sfNFTokens"))
        .iter()
        .cloned()
        .collect();
    tokens.push(token);
    tokens.sort_by(|left, right| {
        nft_compare_tokens(
            left.get_field_h256(sf("sfNFTokenID")),
            right.get_field_h256(sf("sfNFTokenID")),
        )
    });
    let mut page_obj = page.clone_as_object();
    page_obj.set_field_array(sf("sfNFTokens"), starray_from_tokens(tokens));
    if view
        .update(Arc::new(STLedgerEntry::from_stobject(
            page_obj,
            *page.key(),
        )))
        .is_err()
    {
        return Ter::TEF_BAD_LEDGER;
    }

    Ter::TES_SUCCESS
}

fn nft_transfer_token<V: ledger::ApplyView>(
    view: &mut V,
    buyer: &AccountID,
    seller: &AccountID,
    token_id: Uint256,
) -> Ter {
    let (token, page) = match nft_find_token_and_page(view, seller, token_id) {
        Ok(Some(found)) => found,
        Ok(None) => return Ter::TEC_INTERNAL,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    let remove_result = nft_remove_token_from_page(view, seller, token_id, page);
    if !is_tes_success(remove_result) {
        return remove_result;
    }

    // Match NFTokenAcceptOffer::transferNFToken: capture the buyer's owner
    // count after removing the token from the seller and immediately before
    // insertion. This ordering also matters for the (otherwise unusual)
    // same-account path because removal may merge pages and lower OwnerCount.
    let buyer_keylet = protocol::account_keylet(Uint160::from_void(buyer.data()));
    let buyer_owner_count_before = match view.peek(buyer_keylet) {
        Ok(Some(buyer_root)) => buyer_root.get_field_u32(sf("sfOwnerCount")),
        Ok(None) => return Ter::TEC_INTERNAL,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    let insert_result = nft_insert_token(view, buyer, token);
    if !is_tes_success(insert_result) {
        return insert_result;
    }

    let buyer_root = match view.peek(buyer_keylet) {
        Ok(Some(buyer_root)) => buyer_root,
        Ok(None) => return Ter::TEC_INTERNAL,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    let buyer_owner_count_after = buyer_root.get_field_u32(sf("sfOwnerCount"));
    if buyer_owner_count_after > buyer_owner_count_before {
        let Ok(reserve) = i64::try_from(ledger::effective_account_reserve(
            view.fees(),
            &buyer_root,
            0,
            0,
        )) else {
            return Ter::TEF_BAD_LEDGER;
        };
        if buyer_root.get_field_amount(sf("sfBalance")).xrp().drops() < reserve {
            return Ter::TEC_INSUFFICIENT_RESERVE;
        }
    }

    Ter::TES_SUCCESS
}

fn nft_accept_offer_pay<V: ledger::ApplyView>(
    view: &mut V,
    from: &AccountID,
    to: &AccountID,
    amount: &STAmount,
) -> Ter {
    let result = ledger::ripple_state_helpers::account_send(view, from, to, amount);
    if !is_tes_success(result) {
        return result;
    }
    for account in [from, to] {
        match nft_account_funds(view, account, amount) {
            Ok(funds) if funds.signum() < 0 => return Ter::TEC_INSUFFICIENT_FUNDS,
            Ok(_) => {}
            Err(ter) => return ter,
        }
    }
    Ter::TES_SUCCESS
}

fn nft_account_funds<V: ledger::ApplyView>(
    view: &mut V,
    account: &AccountID,
    amount: &STAmount,
) -> Result<STAmount, Ter> {
    if amount.native() {
        let root = match view.peek(protocol::account_keylet(Uint160::from_void(account.data()))) {
            Ok(Some(root)) => root,
            Ok(None) => return Ok(STAmount::from_xrp_amount(XRPAmount::from_drops(0))),
            Err(_) => return Err(Ter::TEF_BAD_LEDGER),
        };
        let reserve =
            match i64::try_from(ledger::effective_account_reserve(view.fees(), &root, 0, 0)) {
                Ok(reserve) => reserve,
                Err(_) => return Err(Ter::TEF_BAD_LEDGER),
            };
        let liquid = root
            .get_field_amount(sf("sfBalance"))
            .xrp()
            .drops()
            .saturating_sub(reserve);
        return Ok(STAmount::from_xrp_amount(XRPAmount::from_drops(
            liquid.max(0),
        )));
    }
    let issue = amount.issue();
    if *account == issue.account {
        return Ok(amount.clone());
    }
    let issuer = match view.read(protocol::account_keylet(Uint160::from_void(
        issue.account.data(),
    ))) {
        Ok(issuer) => issuer,
        Err(_) => return Err(Ter::TEF_BAD_LEDGER),
    };
    if issuer.is_some_and(|issuer| issuer.is_flag(protocol::lsfGlobalFreeze)) {
        return Ok(STAmount::from_iou_amount(
            sf("sfAmount"),
            protocol::IOUAmount::new(),
            issue,
        ));
    }
    let line = match view.read(protocol::line(*account, issue.account, issue.currency)) {
        Ok(line) => line,
        Err(_) => return Err(Ter::TEF_BAD_LEDGER),
    };
    let Some(line) = line else {
        return Ok(STAmount::from_iou_amount(
            sf("sfAmount"),
            protocol::IOUAmount::new(),
            issue,
        ));
    };
    let issuer_freeze = if issue.account > *account {
        protocol::lsfHighFreeze
    } else {
        protocol::lsfLowFreeze
    };
    if line.is_flag(issuer_freeze) {
        return Ok(STAmount::from_iou_amount(
            sf("sfAmount"),
            protocol::IOUAmount::new(),
            issue,
        ));
    }
    let mut balance = line.get_field_amount(sf("sfBalance"));
    if *account > issue.account {
        balance.negate();
    }
    balance.set_issuer(issue.account);
    Ok(balance)
}

fn nft_account_funds_at_least<V: ledger::ApplyView>(
    view: &mut V,
    account: &AccountID,
    amount: &STAmount,
) -> Result<bool, Ter> {
    nft_account_funds(view, account, amount).map(|funds| funds >= amount.clone())
}

fn nft_transfer_fee_cut(amount: &STAmount, fee: u16) -> Result<STAmount, Ter> {
    const TRANSFER_FEE_DENOMINATOR: u32 = 100_000;
    if amount.native() {
        return protocol::xrp_amount::mul_ratio(
            amount.xrp(),
            u32::from(fee),
            TRANSFER_FEE_DENOMINATOR,
            false,
        )
        .map(STAmount::from_xrp_amount)
        .map_err(|_| Ter::TEC_INTERNAL);
    }
    if amount.holds_mpt_issue() {
        let Asset::MPTIssue(issue) = amount.asset() else {
            return Err(Ter::TEC_INTERNAL);
        };
        return protocol::mpt_amount::mul_ratio(
            amount.mpt(),
            u32::from(fee),
            TRANSFER_FEE_DENOMINATOR,
            false,
        )
        .map(|cut| STAmount::from_mpt_amount(sf("sfAmount"), cut, issue))
        .map_err(|_| Ter::TEC_INTERNAL);
    }
    protocol::iou_amount::mul_ratio(
        amount.iou(),
        u32::from(fee),
        TRANSFER_FEE_DENOMINATOR,
        false,
    )
    .map(|cut| STAmount::from_iou_amount(sf("sfAmount"), cut, amount.issue()))
    .map_err(|_| Ter::TEC_INTERNAL)
}

struct DispatcherTicketCreateSink<'a, V> {
    view: &'a mut V,
    account: AccountID,
    tx_sequence: u32,
    pre_fee_balance_drops: Option<i64>,
    failure: Option<Ter>,
}

impl<V: ledger::ApplyView> TicketCreateDoApplySink for DispatcherTicketCreateSink<'_, V> {
    type OwnerNode = u64;

    fn account_exists(&mut self) -> bool {
        match self
            .view
            .exists(protocol::account_keylet(Uint160::from_void(
                self.account.data(),
            ))) {
            Ok(exists) => exists,
            Err(_) => {
                self.failure = Some(Ter::TEF_BAD_LEDGER);
                false
            }
        }
    }

    fn has_reserve(&mut self, ticket_count: u32) -> bool {
        let account_keylet = protocol::account_keylet(Uint160::from_void(self.account.data()));
        let account_root = match self.view.peek(account_keylet) {
            Ok(Some(account_root)) => account_root,
            Ok(None) => {
                self.failure = Some(Ter::TEF_INTERNAL);
                return false;
            }
            Err(_) => {
                self.failure = Some(Ter::TEF_BAD_LEDGER);
                return false;
            }
        };

        let reserve = ledger::effective_account_reserve(
            self.view.fees(),
            &account_root,
            ticket_count as i32,
            0,
        );
        let Ok(reserve) = i64::try_from(reserve) else {
            self.failure = Some(Ter::TEF_BAD_LEDGER);
            return false;
        };
        let Some(balance) = self.pre_fee_balance_drops else {
            self.failure = Some(Ter::TEF_BAD_LEDGER);
            return false;
        };
        balance >= reserve
    }

    fn first_ticket_sequence(&mut self) -> u32 {
        let keylet = protocol::account_keylet(Uint160::from_void(self.account.data()));
        match self.view.peek(keylet) {
            Ok(Some(account_root)) => account_root.get_field_u32(sf("sfSequence")),
            Ok(None) => {
                self.failure = Some(Ter::TEF_INTERNAL);
                0
            }
            Err(_) => {
                self.failure = Some(Ter::TEF_BAD_LEDGER);
                0
            }
        }
    }

    fn tx_sequence(&mut self) -> u32 {
        self.tx_sequence
    }

    fn create_ticket(&mut self, ticket_sequence: u32) {
        let ticket_keylet =
            protocol::ticket_keylet(Uint160::from_void(self.account.data()), ticket_sequence);
        let mut sle = STLedgerEntry::new(ticket_keylet);
        sle.set_account_id(sf("sfAccount"), self.account);
        sle.set_field_u32(sf("sfTicketSequence"), ticket_sequence);
        if self.view.insert(Arc::new(sle)).is_err() {
            self.failure = Some(Ter::TEF_BAD_LEDGER);
        }
    }

    fn dir_insert_ticket(&mut self, ticket_sequence: u32) -> Option<Self::OwnerNode> {
        let ticket_keylet =
            protocol::ticket_keylet(Uint160::from_void(self.account.data()), ticket_sequence);
        match ledger::dir_insert(
            self.view,
            &owner_dir_keylet(Uint160::from_void(self.account.data())),
            ticket_keylet.key,
            &describe_owner_dir(self.account),
        ) {
            Ok(page) => page,
            Err(_) => {
                self.failure = Some(Ter::TEF_BAD_LEDGER);
                None
            }
        }
    }

    fn set_ticket_owner_node(&mut self, ticket_sequence: u32, page: Self::OwnerNode) {
        let ticket_keylet =
            protocol::ticket_keylet(Uint160::from_void(self.account.data()), ticket_sequence);
        let ticket = match self.view.peek(ticket_keylet) {
            Ok(Some(ticket)) => ticket,
            Ok(None) => {
                self.failure = Some(Ter::TEF_INTERNAL);
                return;
            }
            Err(_) => {
                self.failure = Some(Ter::TEF_BAD_LEDGER);
                return;
            }
        };

        let mut obj = ticket.clone_as_object();
        obj.set_field_u64(sf("sfOwnerNode"), page);
        if self
            .view
            .update(Arc::new(STLedgerEntry::from_stobject(obj, *ticket.key())))
            .is_err()
        {
            self.failure = Some(Ter::TEF_BAD_LEDGER);
        }
    }

    fn old_ticket_count(&mut self) -> u32 {
        let account_keylet = protocol::account_keylet(Uint160::from_void(self.account.data()));
        let account_root = match self.view.peek(account_keylet) {
            Ok(Some(account_root)) => account_root,
            Ok(None) => {
                self.failure = Some(Ter::TEF_INTERNAL);
                return 0;
            }
            Err(_) => {
                self.failure = Some(Ter::TEF_BAD_LEDGER);
                return 0;
            }
        };

        if account_root.is_field_present(sf("sfTicketCount")) {
            account_root.get_field_u32(sf("sfTicketCount"))
        } else {
            0
        }
    }

    fn set_ticket_count(&mut self, ticket_count: u32) {
        let account_keylet = protocol::account_keylet(Uint160::from_void(self.account.data()));
        let account_root = match self.view.peek(account_keylet) {
            Ok(Some(account_root)) => account_root,
            Ok(None) => {
                self.failure = Some(Ter::TEF_INTERNAL);
                return;
            }
            Err(_) => {
                self.failure = Some(Ter::TEF_BAD_LEDGER);
                return;
            }
        };

        let mut obj = account_root.clone_as_object();
        obj.set_field_u32(sf("sfTicketCount"), ticket_count);
        if self
            .view
            .update(Arc::new(STLedgerEntry::from_stobject(
                obj,
                *account_root.key(),
            )))
            .is_err()
        {
            self.failure = Some(Ter::TEF_BAD_LEDGER);
        }
    }

    fn adjust_owner_count(&mut self, ticket_count: u32) {
        let account_keylet = protocol::account_keylet(Uint160::from_void(self.account.data()));
        match self.view.peek(account_keylet) {
            Ok(Some(account_root)) => {
                if ledger::adjust_owner_count(self.view, &account_root, ticket_count as i32)
                    .is_err()
                {
                    self.failure = Some(Ter::TEF_BAD_LEDGER);
                }
            }
            Ok(None) => self.failure = Some(Ter::TEF_INTERNAL),
            Err(_) => self.failure = Some(Ter::TEF_BAD_LEDGER),
        }
    }

    fn set_account_sequence(&mut self, sequence: u32) {
        let account_keylet = protocol::account_keylet(Uint160::from_void(self.account.data()));
        let account_root = match self.view.peek(account_keylet) {
            Ok(Some(account_root)) => account_root,
            Ok(None) => {
                self.failure = Some(Ter::TEF_INTERNAL);
                return;
            }
            Err(_) => {
                self.failure = Some(Ter::TEF_BAD_LEDGER);
                return;
            }
        };

        let mut obj = account_root.clone_as_object();
        obj.set_field_u32(sf("sfSequence"), sequence);
        if self
            .view
            .update(Arc::new(STLedgerEntry::from_stobject(
                obj,
                *account_root.key(),
            )))
            .is_err()
        {
            self.failure = Some(Ter::TEF_BAD_LEDGER);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct DispatcherSignerEntry {
    account: AccountID,
    weight: u16,
    wallet_locator: Option<Uint256>,
}

impl SignerListSetWriteEntry for DispatcherSignerEntry {
    type AccountId = AccountID;
    type WalletLocator = Uint256;

    fn account(&self) -> &Self::AccountId {
        &self.account
    }

    fn weight(&self) -> u16 {
        self.weight
    }

    fn wallet_locator(&self) -> Option<&Self::WalletLocator> {
        self.wallet_locator.as_ref()
    }
}

fn parse_signer_entries(
    sttx: &STTx,
) -> Result<
    (
        Vec<SignerListSetEntry<AccountID>>,
        Vec<DispatcherSignerEntry>,
    ),
    Ter,
> {
    if !sttx.is_field_present(sf("sfSignerEntries")) {
        return Ok((Vec::new(), Vec::new()));
    }

    let signer_entries = sttx.get_field_array(sf("sfSignerEntries"));
    let mut operation_entries = Vec::with_capacity(signer_entries.len());
    let mut write_entries = Vec::with_capacity(signer_entries.len());

    for signer in signer_entries.iter() {
        let signer_account = signer.get_account_id(sf("sfAccount"));
        let weight = signer.get_field_u16(sf("sfSignerWeight"));
        let wallet_locator = signer
            .is_field_present(sf("sfWalletLocator"))
            .then(|| signer.get_field_h256(sf("sfWalletLocator")));

        operation_entries.push(SignerListSetEntry {
            account: signer_account,
            weight,
        });
        write_entries.push(DispatcherSignerEntry {
            account: signer_account,
            weight,
            wallet_locator,
        });
    }

    write_entries.sort();
    Ok((operation_entries, write_entries))
}

fn remove_signer_list<V: ledger::ApplyView>(view: &mut V, account: AccountID) -> Ter {
    let account_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
    let owner_dir = owner_dir_keylet(Uint160::from_void(account.data()));
    let signer_keylet = signers_keylet(Uint160::from_void(account.data()));
    let signer_list = match view.peek(signer_keylet) {
        Ok(sle) => sle,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    // Inline removal logic to avoid multiple mutable borrows
    if let Some(signer_sle) = signer_list {
        let flags = signer_sle.get_field_u32(sf("sfFlags"));
        let signer_entries_len = signer_sle.get_field_array(sf("sfSignerEntries")).len();
        let owner_node = signer_sle.get_field_u64(sf("sfOwnerNode"));
        match ledger::dir_remove(view, &owner_dir, owner_node, signer_keylet.key, false) {
            Ok(true) => {}
            Ok(false) => return Ter::TEF_BAD_LEDGER,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        }
        // Modern signer lists carry lsfOneOwnerCount and consume exactly one
        // reserve unit.  Only legacy pre-MultiSignReserve lists use the old
        // `2 + signer_count` accounting.  This distinction is consensus
        // critical when destroying or replacing a signer list.
        let count = if flags & LSF_ONE_OWNER_COUNT != 0 {
            1
        } else {
            signer_entries_len as u32 + 2
        };
        let account_sle = match view.peek(account_keylet) {
            Ok(Some(sle)) => sle,
            Ok(None) => return Ter::TEF_BAD_LEDGER,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        if ledger::decrease_owner_count_for_object(view, &account_sle, &signer_sle, count).is_err()
        {
            return Ter::TEF_BAD_LEDGER;
        }
        if view.erase(signer_sle).is_err() {
            return Ter::TEF_BAD_LEDGER;
        }
    }
    Ter::TES_SUCCESS
}

fn destroy_signer_list<V: ledger::ApplyView>(view: &mut V, account: AccountID) -> Ter {
    let account_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
    let account_sle = match view.peek(account_keylet) {
        Ok(account_sle) => account_sle,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    let master_disabled = account_sle
        .as_ref()
        .is_some_and(|sle| sle.get_field_u32(sf("sfFlags")) & lsfDisableMaster != 0);
    let regular_key_present = account_sle
        .as_ref()
        .is_some_and(|sle| sle.is_field_present(sf("sfRegularKey")));

    run_signer_list_set_destroy_signer_list(
        account_sle.is_some(),
        master_disabled,
        regular_key_present,
        || remove_signer_list(view, account),
    )
}

fn replace_signer_list<V: ledger::ApplyView>(
    view: &mut V,
    sttx: &STTx,
    account: AccountID,
    quorum: u32,
    signers: &[DispatcherSignerEntry],
    pre_fee_balance_drops: Option<i64>,
) -> Ter {
    let ter = remove_signer_list(view, account);
    if ter != Ter::TES_SUCCESS {
        return ter;
    }

    let account_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
    let owner_dir = owner_dir_keylet(Uint160::from_void(account.data()));
    let signer_keylet = signers_keylet(Uint160::from_void(account.data()));
    let account_sle = match view.peek(account_keylet) {
        Ok(Some(sle)) => sle,
        Ok(None) => return Ter::TEF_INTERNAL,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    let sponsor_sle = match check_cash_reserve_sponsor(view, sttx) {
        Ok(sponsor) => sponsor,
        Err(ter) => return ter,
    };

    let has_reserve = match check_cash_has_object_reserve(
        view,
        &account_sle,
        pre_fee_balance_drops,
        sponsor_sle.as_ref(),
    ) {
        Ok(has_reserve) => has_reserve,
        Err(ter) => return ter,
    };
    if !has_reserve {
        return Ter::TEC_INSUFFICIENT_RESERVE;
    }

    let plan = build_signer_list_set_ledger_write_plan(
        view.rules()
            .enabled(&protocol::feature_id("fixIncludeKeyletFields")),
        account,
        quorum,
        LSF_ONE_OWNER_COUNT,
        signers,
    );

    let owner_page = match ledger::dir_insert(
        view,
        &owner_dir,
        signer_keylet.key,
        &describe_owner_dir(account),
    ) {
        Ok(Some(page)) => page,
        Ok(None) => return Ter::TEC_DIR_FULL,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    let mut signer_list = STLedgerEntry::new(signer_keylet);
    if let Some(owner) = plan.owner {
        signer_list.set_account_id(sf("sfOwner"), owner);
    }
    signer_list.set_field_u32(sf("sfSignerQuorum"), plan.signer_quorum);
    signer_list.set_field_u32(sf("sfSignerListID"), plan.signer_list_id);
    if let Some(flags) = plan.flags {
        signer_list.set_field_u32(sf("sfFlags"), flags);
    }
    signer_list.set_field_u64(sf("sfOwnerNode"), owner_page);

    let mut signer_array = STArray::new(sf("sfSignerEntries"));
    signer_array.reserve(plan.signer_entries.len());
    for signer in plan.signer_entries {
        let mut signer_entry = STObject::make_inner_object(sf("sfSignerEntry"));
        signer_entry.set_account_id(sf("sfAccount"), signer.account);
        signer_entry.set_field_u16(sf("sfSignerWeight"), signer.weight);
        if let Some(wallet_locator) = signer.wallet_locator {
            signer_entry.set_field_h256(sf("sfWalletLocator"), wallet_locator);
        }
        signer_array.push_back(signer_entry);
    }
    signer_list.set_field_array(sf("sfSignerEntries"), signer_array);

    if let Some(sponsor_sle) = sponsor_sle.as_ref() {
        signer_list.set_account_id(sf("sfSponsor"), sponsor_sle.get_account_id(sf("sfAccount")));
    }

    if view.insert(Arc::new(signer_list)).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }
    if ledger::increase_owner_count_for_object(view, &account_sle, sponsor_sle.as_ref()).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }

    Ter::TES_SUCCESS
}

fn sorted_deposit_preauth_credentials(credentials: &STArray) -> Vec<(AccountID, Vec<u8>)> {
    let mut sorted = credentials
        .iter()
        .map(|credential| {
            (
                credential.get_account_id(sf("sfIssuer")),
                credential.get_field_vl(sf("sfCredentialType")),
            )
        })
        .collect::<Vec<_>>();
    sorted.sort_unstable();
    sorted
}

fn deposit_preauth_credential_hashes(credentials: &[(AccountID, Vec<u8>)]) -> Vec<Uint256> {
    credentials
        .iter()
        .map(|(issuer, credential_type)| {
            protocol::sha512_half_slices(&[issuer.data(), credential_type])
        })
        .collect()
}

fn remove_deposit_preauth_entry<V: ledger::ApplyView>(
    view: &mut V,
    preauth: Arc<STLedgerEntry>,
) -> Ter {
    let owner = preauth.get_account_id(sf("sfAccount"));
    let owner_node = preauth.get_field_u64(sf("sfOwnerNode"));
    let owner_dir = owner_dir_keylet(Uint160::from_void(owner.data()));
    if !ledger::dir_remove(view, &owner_dir, owner_node, *preauth.key(), false).unwrap_or(false) {
        return Ter::TEF_BAD_LEDGER;
    }
    let owner_sle = match view.peek(protocol::account_keylet(Uint160::from_void(owner.data()))) {
        Ok(Some(sle)) => sle,
        Ok(None) => return Ter::TEF_INTERNAL,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    if ledger::decrease_owner_count_for_object(view, &owner_sle, &preauth, 1).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }
    view.erase(preauth)
        .map(|_| Ter::TES_SUCCESS)
        .unwrap_or(Ter::TEF_BAD_LEDGER)
}

fn remove_account_delete_owned_entry<V: ledger::ApplyView>(
    view: &mut V,
    account: AccountID,
    entry: Arc<STLedgerEntry>,
) -> Ter {
    let owner_dir = owner_dir_keylet(Uint160::from_void(account.data()));
    if !ledger::dir_remove(
        view,
        &owner_dir,
        entry.get_field_u64(sf("sfOwnerNode")),
        *entry.key(),
        false,
    )
    .unwrap_or(false)
    {
        return Ter::TEF_BAD_LEDGER;
    }
    let account_sle = match view.peek(protocol::account_keylet(Uint160::from_void(account.data())))
    {
        Ok(Some(sle)) => sle,
        _ => return Ter::TEF_BAD_LEDGER,
    };
    if ledger::decrease_owner_count_for_object(view, &account_sle, &entry, 1).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }
    view.erase(entry)
        .map(|_| Ter::TES_SUCCESS)
        .unwrap_or(Ter::TEF_BAD_LEDGER)
}

fn remove_account_delete_delegate<V: ledger::ApplyView>(
    view: &mut V,
    account: AccountID,
    entry: Arc<STLedgerEntry>,
) -> Ter {
    let owner_dir = owner_dir_keylet(Uint160::from_void(account.data()));
    if !ledger::dir_remove(
        view,
        &owner_dir,
        entry.get_field_u64(sf("sfOwnerNode")),
        *entry.key(),
        false,
    )
    .unwrap_or(false)
    {
        return Ter::TEF_BAD_LEDGER;
    }
    if entry.is_field_present(sf("sfDestinationNode")) {
        let authorized = entry.get_account_id(sf("sfAuthorize"));
        let destination_dir = owner_dir_keylet(Uint160::from_void(authorized.data()));
        if !ledger::dir_remove(
            view,
            &destination_dir,
            entry.get_field_u64(sf("sfDestinationNode")),
            *entry.key(),
            false,
        )
        .unwrap_or(false)
        {
            return Ter::TEF_BAD_LEDGER;
        }
    }
    let account_sle = match view.peek(protocol::account_keylet(Uint160::from_void(account.data())))
    {
        Ok(Some(sle)) => sle,
        _ => return Ter::TEF_BAD_LEDGER,
    };
    if ledger::decrease_owner_count_for_object(view, &account_sle, &entry, 1).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }
    view.erase(entry)
        .map_or(Ter::TEF_BAD_LEDGER, |_| Ter::TES_SUCCESS)
}

pub fn handle_real_dispatch<V: ledger::ApplyView>(
    view: &mut V,
    sttx: &STTx,
    txn_type: TxType,
    pre_fee_balance_drops: Option<i64>,
) -> Ter {
    let tx_hash = sttx.get_hash(protocol::HashPrefix::TransactionId);
    tracing::trace!(target: "tx", tx_type = %format!("{:?}", txn_type), hash = %tx_hash, "Transaction preflight");
    let result = handle_real_dispatch_inner(view, sttx, txn_type, pre_fee_balance_drops);

    if protocol::is_tes_success(result) || protocol::is_tec_claim(result) {
        tracing::debug!(target: "tx", tx_type = %format!("{:?}", txn_type), hash = %tx_hash, result = %format!("{:?}", result), "Transaction applied");
    } else {
        tracing::debug!(target: "tx", tx_type = %format!("{:?}", txn_type), hash = %tx_hash, result = %format!("{:?}", result), "Transaction not applied");
    }

    // Comprehensive per-tx debug log — logs every tx with key fields and result.
    // Controlled by a global counter so we don't flood the log.
    static TX_LOG: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    let c = TX_LOG.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    if c < 5000 {
        let account = sttx.get_account_id(sf("sfAccount"));
        let flags = sttx.get_field_u32(sf("sfFlags"));
        let seq = sttx.get_seq_value();

        // Key amounts for each tx type
        let detail = match txn_type {
            TxType::OFFER_CREATE => {
                let tp = sttx.get_field_amount(sf("sfTakerPays"));
                let tg = sttx.get_field_amount(sf("sfTakerGets"));
                format!(
                    "TakerPays_native={} TakerGets_native={} TakerPays_signum={} TakerGets_signum={}",
                    tp.native(),
                    tg.native(),
                    tp.signum(),
                    tg.signum()
                )
            }
            TxType::PAYMENT => {
                let amt = sttx.get_field_amount(sf("sfAmount"));
                let has_sm = sttx.is_field_present(sf("sfSendMax"));
                let has_paths = sttx.is_field_present(sf("sfPaths"));
                let sm_native = if has_sm {
                    sttx.get_field_amount(sf("sfSendMax")).native()
                } else {
                    true
                };
                format!(
                    "Amount_native={} has_sendmax={} sendmax_native={} has_paths={} partial={}",
                    amt.native(),
                    has_sm,
                    sm_native,
                    has_paths,
                    (flags & 0x0002_0000) != 0
                )
            }
            TxType::CHECK_CASH => {
                let has_amt = sttx.is_field_present(sf("sfAmount"));
                let has_dmin = sttx.is_field_present(sf("sfDeliverMin"));
                format!("has_amount={} has_deliver_min={}", has_amt, has_dmin)
            }
            _ => String::new(),
        };

        tracing::debug!(target: "tx",
            "[tx_trace] type={:?} seq={} flags=0x{:08x} acct={:02x}{:02x}{:02x}{:02x} result={:?} {}",
            txn_type,
            seq,
            flags,
            account.data()[0],
            account.data()[1],
            account.data()[2],
            account.data()[3],
            result,
            detail,
        );
    }

    result
}

fn require_pre_fee_balance(pre_fee_balance_drops: Option<i64>) -> Result<i64, Ter> {
    pre_fee_balance_drops.ok_or(Ter::TEF_BAD_LEDGER)
}

/// Apply routes whose reserve decisions use the submitting AccountRoot must
/// receive the balance captured before fee payment. Pinned rippled's
/// `preFeeBalance_` is mandatory whenever the source account exists.
fn requires_source_pre_fee_balance(txn_type: TxType) -> bool {
    matches!(
        txn_type,
        TxType::SIGNER_LIST_SET
            | TxType::XCHAIN_COMMIT
            | TxType::XCHAIN_ACCOUNT_CREATE_COMMIT
            | TxType::CHECK_CREATE
            | TxType::CHECK_CASH
            | TxType::CREDENTIAL_CREATE
            | TxType::CREDENTIAL_ACCEPT
            | TxType::DELEGATE_SET
            | TxType::AMM_CLAWBACK
            | TxType::AMM_WITHDRAW
            | TxType::PAYMENT
            | TxType::OFFER_CREATE
            | TxType::TRUST_SET
            | TxType::TICKET_CREATE
            | TxType::ESCROW_FINISH
            | TxType::ESCROW_CANCEL
            | TxType::LOAN_BROKER_SET
            | TxType::LOAN_BROKER_COVER_WITHDRAW
            | TxType::LOAN_SET
            | TxType::DEPOSIT_PREAUTH
            | TxType::PAYCHAN_CREATE
            | TxType::NFTOKEN_MINT
            | TxType::NFTOKEN_CREATE_OFFER
            | TxType::MPTOKEN_AUTHORIZE
            | TxType::MPTOKEN_ISSUANCE_CREATE
            | TxType::VAULT_CREATE
            | TxType::VAULT_DEPOSIT
            | TxType::VAULT_WITHDRAW
            | TxType::SPONSORSHIP_TRANSFER
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ApplyDispatchRoute {
    AccountAndPayment,
    Dex,
    NfToken,
    XChain,
    CredentialAndDomain,
    Token,
    Vault,
    Lending,
    Sponsorship,
    ConfidentialMpt,
    SystemChange,
}

/// Pure classification of every protocol-dispatchable transaction into its
/// concrete apply owner. The dispatcher checks this before entering its large
/// semantic match so registry additions fail closed until deliberately routed.
pub(crate) fn apply_dispatch_route(txn_type: TxType) -> Option<ApplyDispatchRoute> {
    use ApplyDispatchRoute::*;
    Some(match txn_type {
        TxType::PAYMENT
        | TxType::ESCROW_CREATE
        | TxType::ESCROW_FINISH
        | TxType::ACCOUNT_SET
        | TxType::ESCROW_CANCEL
        | TxType::REGULAR_KEY_SET
        | TxType::OFFER_CANCEL
        | TxType::TICKET_CREATE
        | TxType::SIGNER_LIST_SET
        | TxType::PAYCHAN_CREATE
        | TxType::PAYCHAN_FUND
        | TxType::PAYCHAN_CLAIM
        | TxType::CHECK_CREATE
        | TxType::CHECK_CASH
        | TxType::CHECK_CANCEL
        | TxType::DEPOSIT_PREAUTH
        | TxType::ACCOUNT_DELETE
        | TxType::DELEGATE_SET
        | TxType::BATCH => AccountAndPayment,
        TxType::OFFER_CREATE
        | TxType::TRUST_SET
        | TxType::CLAWBACK
        | TxType::AMM_CLAWBACK
        | TxType::AMM_CREATE
        | TxType::AMM_DEPOSIT
        | TxType::AMM_WITHDRAW
        | TxType::AMM_VOTE
        | TxType::AMM_BID
        | TxType::AMM_DELETE => Dex,
        TxType::NFTOKEN_MINT
        | TxType::NFTOKEN_BURN
        | TxType::NFTOKEN_CREATE_OFFER
        | TxType::NFTOKEN_CANCEL_OFFER
        | TxType::NFTOKEN_ACCEPT_OFFER
        | TxType::NFTOKEN_MODIFY => NfToken,
        TxType::XCHAIN_CREATE_CLAIM_ID
        | TxType::XCHAIN_COMMIT
        | TxType::XCHAIN_CLAIM
        | TxType::XCHAIN_ACCOUNT_CREATE_COMMIT
        | TxType::XCHAIN_ADD_CLAIM_ATTESTATION
        | TxType::XCHAIN_ADD_ACCOUNT_CREATE_ATTESTATION
        | TxType::XCHAIN_MODIFY_BRIDGE
        | TxType::XCHAIN_CREATE_BRIDGE => XChain,
        TxType::DID_SET
        | TxType::DID_DELETE
        | TxType::ORACLE_SET
        | TxType::ORACLE_DELETE
        | TxType::CREDENTIAL_CREATE
        | TxType::CREDENTIAL_ACCEPT
        | TxType::CREDENTIAL_DELETE
        | TxType::PERMISSIONED_DOMAIN_SET
        | TxType::PERMISSIONED_DOMAIN_DELETE => CredentialAndDomain,
        TxType::LEDGER_STATE_FIX
        | TxType::MPTOKEN_ISSUANCE_CREATE
        | TxType::MPTOKEN_ISSUANCE_DESTROY
        | TxType::MPTOKEN_ISSUANCE_SET
        | TxType::MPTOKEN_AUTHORIZE => Token,
        TxType::VAULT_CREATE
        | TxType::VAULT_SET
        | TxType::VAULT_DELETE
        | TxType::VAULT_DEPOSIT
        | TxType::VAULT_WITHDRAW
        | TxType::VAULT_CLAWBACK => Vault,
        TxType::LOAN_BROKER_SET
        | TxType::LOAN_BROKER_DELETE
        | TxType::LOAN_BROKER_COVER_DEPOSIT
        | TxType::LOAN_BROKER_COVER_WITHDRAW
        | TxType::LOAN_BROKER_COVER_CLAWBACK
        | TxType::LOAN_SET
        | TxType::LOAN_DELETE
        | TxType::LOAN_MANAGE
        | TxType::LOAN_PAY => Lending,
        TxType::SPONSORSHIP_TRANSFER | TxType::SPONSORSHIP_SET => Sponsorship,
        TxType::CONFIDENTIAL_MPT_CONVERT
        | TxType::CONFIDENTIAL_MPT_MERGE_INBOX
        | TxType::CONFIDENTIAL_MPT_CONVERT_BACK
        | TxType::CONFIDENTIAL_MPT_SEND
        | TxType::CONFIDENTIAL_MPT_CLAWBACK => ConfidentialMpt,
        TxType::AMENDMENT | TxType::FEE | TxType::UNL_MODIFY => SystemChange,
        _ => return None,
    })
}

fn handle_real_dispatch_inner<V: ledger::ApplyView>(
    view: &mut V,
    sttx: &STTx,
    txn_type: TxType,
    pre_fee_balance_drops: Option<i64>,
) -> Ter {
    if apply_dispatch_route(txn_type).is_none() {
        return Ter::TEM_UNKNOWN;
    }
    if requires_source_pre_fee_balance(txn_type) && pre_fee_balance_drops.is_none() {
        return Ter::TEF_BAD_LEDGER;
    }
    // Signature authorization is complete before apply in shared
    // `invoke_preclaim`. Rechecking here would incorrectly authorize against
    // sfAccount instead of sfDelegate for delegated transactions.
    match txn_type {
        // --- XChain Bridge ---
        TxType::XCHAIN_CREATE_BRIDGE => {
            if !view.rules().enabled(&protocol::feature_id("XChainBridge")) {
                return Ter::TEM_DISABLED;
            }
            crate::state::xchain::apply_xchain_create_bridge(view, sttx)
        }
        TxType::XCHAIN_MODIFY_BRIDGE => {
            if !view.rules().enabled(&protocol::feature_id("XChainBridge")) {
                return Ter::TEM_DISABLED;
            }
            crate::state::xchain::apply_xchain_modify_bridge(view, sttx)
        }
        TxType::XCHAIN_CLAIM => {
            if !view.rules().enabled(&protocol::feature_id("XChainBridge")) {
                return Ter::TEM_DISABLED;
            }
            crate::state::xchain::apply_xchain_claim(view, sttx)
        }
        TxType::XCHAIN_COMMIT => {
            if !view.rules().enabled(&protocol::feature_id("XChainBridge")) {
                return Ter::TEM_DISABLED;
            }
            crate::state::xchain::apply_xchain_commit(view, sttx, pre_fee_balance_drops)
        }
        TxType::XCHAIN_CREATE_CLAIM_ID => {
            if !view.rules().enabled(&protocol::feature_id("XChainBridge")) {
                return Ter::TEM_DISABLED;
            }
            crate::state::xchain::apply_xchain_create_claim_id(view, sttx)
        }
        TxType::XCHAIN_ADD_CLAIM_ATTESTATION => {
            if !view.rules().enabled(&protocol::feature_id("XChainBridge")) {
                return Ter::TEM_DISABLED;
            }
            crate::state::xchain::apply_xchain_add_claim_attestation(view, sttx)
        }
        TxType::XCHAIN_ADD_ACCOUNT_CREATE_ATTESTATION => {
            if !view.rules().enabled(&protocol::feature_id("XChainBridge")) {
                return Ter::TEM_DISABLED;
            }
            crate::state::xchain::apply_xchain_add_account_create_attestation(view, sttx)
        }
        TxType::XCHAIN_ACCOUNT_CREATE_COMMIT => {
            if !view.rules().enabled(&protocol::feature_id("XChainBridge")) {
                return Ter::TEM_DISABLED;
            }
            crate::state::xchain::apply_xchain_account_create_commit(
                view,
                sttx,
                pre_fee_balance_drops,
            )
        }

        // --- Vault / Loan / Batch / Delegate ---
        TxType::VAULT_CREATE => {
            let pre_fee_balance_drops = match require_pre_fee_balance(pre_fee_balance_drops) {
                Ok(balance) => balance,
                Err(ter) => return ter,
            };
            crate::state::vault::apply_vault_create(view, sttx, pre_fee_balance_drops)
        }
        TxType::VAULT_SET => crate::state::vault::apply_vault_set(view, sttx),
        TxType::VAULT_DELETE => crate::state::vault::apply_vault_delete(view, sttx),
        TxType::VAULT_DEPOSIT => crate::state::vault::apply_vault_deposit(view, sttx),
        TxType::VAULT_WITHDRAW => crate::state::vault::apply_vault_withdraw(view, sttx),
        TxType::VAULT_CLAWBACK => crate::state::vault::apply_vault_clawback(view, sttx),
        TxType::BATCH => {
            if !view.rules().enabled(&protocol::feature_id("BatchV1_1")) {
                return Ter::TEM_DISABLED;
            }
            crate::state::batch::apply_batch(view, sttx)
        }
        TxType::LOAN_SET => {
            let pre_fee_balance_drops = match require_pre_fee_balance(pre_fee_balance_drops) {
                Ok(balance) => balance,
                Err(error) => return error,
            };
            crate::state::lending::apply_loan_set(view, sttx, pre_fee_balance_drops)
        }
        TxType::LOAN_DELETE => crate::state::lending::apply_loan_delete(view, sttx),
        TxType::LOAN_MANAGE => crate::state::lending::apply_loan_manage(view, sttx),
        TxType::LOAN_PAY => crate::state::lending::apply_loan_pay(view, sttx),
        TxType::LOAN_BROKER_SET => {
            let pre_fee_balance_drops = match require_pre_fee_balance(pre_fee_balance_drops) {
                Ok(balance) => balance,
                Err(error) => return error,
            };
            crate::state::lending::apply_loan_broker_set(view, sttx, pre_fee_balance_drops)
        }
        TxType::LOAN_BROKER_DELETE => crate::state::lending::apply_loan_broker_delete(view, sttx),
        TxType::LOAN_BROKER_COVER_DEPOSIT => {
            crate::state::lending::apply_loan_broker_cover_deposit(view, sttx)
        }
        TxType::LOAN_BROKER_COVER_WITHDRAW => {
            let pre_fee_balance_drops = match require_pre_fee_balance(pre_fee_balance_drops) {
                Ok(balance) => balance,
                Err(error) => return error,
            };
            crate::state::lending::apply_loan_broker_cover_withdraw(
                view,
                sttx,
                pre_fee_balance_drops,
            )
        }
        TxType::LOAN_BROKER_COVER_CLAWBACK => {
            crate::state::lending::apply_loan_broker_cover_clawback(view, sttx)
        }
        TxType::DELEGATE_SET => {
            if !view
                .rules()
                .enabled(&protocol::feature_id("PermissionDelegationV1_1"))
            {
                return Ter::TEM_DISABLED;
            }
            let account = sttx.get_account_id(sf("sfAccount"));
            let authorize = sttx.get_account_id(sf("sfAuthorize"));
            let permissions = sttx
                .get_field_array(sf("sfPermissions"))
                .iter()
                .map(|permission| permission.get_field_u32(sf("sfPermissionValue")))
                .collect::<Vec<_>>();
            let balance_for_reserve = match pre_fee_balance_drops {
                Some(balance) => balance,
                None => match delegate_reserve_balance_from_lookup(
                    view.peek(protocol::account_keylet(Uint160::from_void(account.data()))),
                ) {
                    Ok(balance) => balance,
                    Err(ter) => return ter,
                },
            };
            let reserve_sponsor = match check_cash_reserve_sponsor(view, sttx) {
                Ok(sponsor) => sponsor,
                Err(ter) => return ter,
            };
            let mut sink = ViewBackedDelegateSetSink::new(
                view,
                account,
                authorize,
                balance_for_reserve,
                reserve_sponsor,
            );
            let result = run_delegate_set_do_apply(&permissions, &mut sink);
            finish_delegate_apply(result, sink.failure)
        }
        TxType::SPONSORSHIP_TRANSFER | TxType::SPONSORSHIP_SET => {
            crate::state::sponsorship::apply(view, sttx, pre_fee_balance_drops)
        }

        // --- Payment: full compatibility (payment.rs) ---
        TxType::PAYMENT => crate::state::payment::do_payment(view, sttx, pre_fee_balance_drops),

        // --- TrustSet: full flag handling ---
        // --- TrustSet: full compatibility (trust_set.rs) ---
        TxType::TRUST_SET => {
            crate::state::trust_set::do_trust_set(view, sttx, pre_fee_balance_drops)
        }

        // --- OfferCreate: full compatibility (offer_create.rs) ---
        TxType::OFFER_CREATE => {
            crate::state::offer_create::do_offer_create(view, sttx, pre_fee_balance_drops)
        }

        // --- OfferCancel ---
        TxType::OFFER_CANCEL => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let account_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
            if let Err(ter) = required_source_account_from_lookup(view.read(account_keylet)) {
                return ter;
            }
            let seq = sttx.get_field_u32(sf("sfOfferSequence"));
            let keylet = protocol::offer_keylet(Uint160::from_void(account.data()), seq);
            match view.peek(keylet) {
                Ok(Some(offer)) => {
                    crate::state::offer_create::offer_delete_pub(view, &account, offer)
                }
                Ok(None) => Ter::TES_SUCCESS,
                Err(_) => Ter::TEF_BAD_LEDGER,
            }
        }

        // --- Account operations ---
        TxType::ACCOUNT_SET => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let keylet = protocol::account_keylet(Uint160::from_void(account.data()));
            match view.peek(keylet) {
                Ok(Some(sle)) => {
                    let mut obj = sle.clone_as_object();
                    if sttx.is_field_present(sf("sfDomain")) {
                        let domain = sttx.get_field_vl(sf("sfDomain"));
                        if domain.is_empty() {
                            obj.make_field_absent(sf("sfDomain"));
                        } else {
                            obj.set_stbase(protocol::STBlob::from_buffer(
                                sf("sfDomain"),
                                basics::buffer::Buffer::from(&domain[..]),
                            ));
                        }
                    }
                    if sttx.is_field_present(sf("sfTransferRate")) {
                        let rate = sttx.get_field_u32(sf("sfTransferRate"));
                        if rate == 0 || rate == 1_000_000_000 {
                            obj.make_field_absent(sf("sfTransferRate"));
                        } else {
                            obj.set_field_u32(sf("sfTransferRate"), rate);
                        }
                    }
                    if sttx.is_field_present(sf("sfTickSize")) {
                        let tick = sttx.get_field_u8(sf("sfTickSize"));
                        // rippled treats both zero and the maximum precision as
                        // the canonical absence of a TickSize field.
                        if tick == 0 || tick == 16 {
                            obj.make_field_absent(sf("sfTickSize"));
                        } else {
                            obj.set_field_u8(sf("sfTickSize"), tick);
                        }
                    }
                    if sttx.is_field_present(sf("sfEmailHash")) {
                        let hash = sttx.get_field_h128(sf("sfEmailHash"));
                        if hash.is_zero() {
                            obj.make_field_absent(sf("sfEmailHash"));
                        } else {
                            obj.set_field_h128(sf("sfEmailHash"), hash);
                        }
                    }
                    if sttx.is_field_present(sf("sfWalletLocator")) {
                        let locator = sttx.get_field_h256(sf("sfWalletLocator"));
                        if locator.is_zero() {
                            obj.make_field_absent(sf("sfWalletLocator"));
                        } else {
                            obj.set_field_h256(sf("sfWalletLocator"), locator);
                        }
                    }
                    if sttx.is_field_present(sf("sfMessageKey")) {
                        let vl = sttx.get_field_vl(sf("sfMessageKey"));
                        if vl.is_empty() {
                            obj.make_field_absent(sf("sfMessageKey"));
                        } else {
                            obj.set_stbase(protocol::STBlob::from_buffer(
                                sf("sfMessageKey"),
                                basics::buffer::Buffer::from(&vl[..]),
                            ));
                        }
                    }
                    // AccountSet::doApply has several deliberately asymmetric
                    // flags (NoFreeze and Clawback are irreversible), so this is
                    // kept in the same order as rippled instead of applying a
                    // generic set/clear mapping.
                    let flags_in = obj.get_field_u32(sf("sfFlags"));
                    let mut flags = flags_in;
                    let tx_flags = sttx.get_flags();
                    let set_flag = sttx.get_field_u32(sf("sfSetFlag"));
                    let clear_flag = sttx.get_field_u32(sf("sfClearFlag"));

                    let set_require_dest =
                        tx_flags & protocol::tfRequireDestTag != 0 || set_flag == 1;
                    let clear_require_dest =
                        tx_flags & protocol::tfOptionalDestTag != 0 || clear_flag == 1;
                    let set_require_auth = tx_flags & protocol::tfRequireAuth != 0 || set_flag == 2;
                    let clear_require_auth =
                        tx_flags & protocol::tfOptionalAuth != 0 || clear_flag == 2;
                    let set_disallow_xrp = tx_flags & protocol::tfDisallowXRP != 0 || set_flag == 3;
                    let clear_disallow_xrp =
                        tx_flags & protocol::tfAllowXRP != 0 || clear_flag == 3;

                    if set_require_auth {
                        flags |= protocol::lsfRequireAuth;
                    }
                    if clear_require_auth {
                        flags &= !protocol::lsfRequireAuth;
                    }
                    if set_require_dest {
                        flags |= protocol::lsfRequireDestTag;
                    }
                    if clear_require_dest {
                        flags &= !protocol::lsfRequireDestTag;
                    }
                    if set_disallow_xrp {
                        flags |= protocol::lsfDisallowXRP;
                    }
                    if clear_disallow_xrp {
                        flags &= !protocol::lsfDisallowXRP;
                    }

                    let sig_with_master = {
                        let signing_pub_key = sttx.get_field_vl(sf("sfSigningPubKey"));
                        if signing_pub_key.is_empty() {
                            false
                        } else {
                            use sha2::Digest;
                            let sha = sha2::Sha256::digest(&signing_pub_key);
                            let ripe = ripemd::Ripemd160::digest(sha);
                            AccountID::from_slice(&ripe).is_some_and(|signer| signer == account)
                        }
                    };

                    if set_flag == 4 && flags_in & protocol::lsfDisableMaster == 0 {
                        if !sig_with_master {
                            return Ter::TEC_NEED_MASTER_KEY;
                        }
                        let has_alternative = if obj.is_field_present(sf("sfRegularKey")) {
                            true
                        } else {
                            match signer_list_exists_from_lookup(view.exists(
                                protocol::signers_keylet(Uint160::from_void(account.data())),
                            )) {
                                Ok(exists) => exists,
                                Err(ter) => return ter,
                            }
                        };
                        if !has_alternative {
                            return Ter::TEC_NO_ALTERNATIVE_KEY;
                        }
                        flags |= protocol::lsfDisableMaster;
                    }
                    if clear_flag == 4 {
                        flags &= !protocol::lsfDisableMaster;
                    }

                    if set_flag == 8 {
                        flags |= protocol::lsfDefaultRipple;
                    } else if clear_flag == 8 {
                        flags &= !protocol::lsfDefaultRipple;
                    }

                    if set_flag == 6 {
                        if !sig_with_master && flags_in & protocol::lsfDisableMaster == 0 {
                            return Ter::TEC_NEED_MASTER_KEY;
                        }
                        flags |= protocol::lsfNoFreeze;
                    }

                    if set_flag == 7 {
                        flags |= protocol::lsfGlobalFreeze;
                    }
                    if set_flag != 7 && clear_flag == 7 && flags & protocol::lsfNoFreeze == 0 {
                        flags &= !protocol::lsfGlobalFreeze;
                    }

                    if set_flag == 5 && !obj.is_field_present(sf("sfAccountTxnID")) {
                        obj.set_field_h256(sf("sfAccountTxnID"), Uint256::default());
                    }
                    if clear_flag == 5 {
                        obj.make_field_absent(sf("sfAccountTxnID"));
                    }

                    if set_flag == 9 {
                        flags |= protocol::lsfDepositAuth;
                    } else if clear_flag == 9 {
                        flags &= !protocol::lsfDepositAuth;
                    }

                    if set_flag == 10 {
                        obj.set_account_id(
                            sf("sfNFTokenMinter"),
                            sttx.get_account_id(sf("sfNFTokenMinter")),
                        );
                    }
                    if clear_flag == 10 {
                        obj.make_field_absent(sf("sfNFTokenMinter"));
                    }

                    for (asf, lsf) in [
                        (12, protocol::lsfDisallowIncomingNFTokenOffer),
                        (13, protocol::lsfDisallowIncomingCheck),
                        (14, protocol::lsfDisallowIncomingPayChan),
                        (15, protocol::lsfDisallowIncomingTrustline),
                    ] {
                        if set_flag == asf {
                            flags |= lsf;
                        } else if clear_flag == asf {
                            flags &= !lsf;
                        }
                    }

                    if view.rules().enabled(&protocol::feature_id("TokenEscrow")) {
                        if set_flag == 17 {
                            flags |= protocol::lsfAllowTrustLineLocking;
                        } else if clear_flag == 17 {
                            flags &= !protocol::lsfAllowTrustLineLocking;
                        }
                    }
                    if set_flag == 16 {
                        flags |= protocol::lsfAllowTrustLineClawback;
                    }
                    obj.set_field_u32(sf("sfFlags"), flags);
                    if view
                        .update(Arc::new(STLedgerEntry::from_stobject(obj, *sle.key())))
                        .is_err()
                    {
                        return Ter::TEF_BAD_LEDGER;
                    }
                }
                Ok(None) => return Ter::TEF_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
            Ter::TES_SUCCESS
        }

        TxType::ACCOUNT_DELETE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let destination_field = sf("sfDestination");
            if !sttx.is_field_present(destination_field) {
                return Ter::TEM_MALFORMED;
            }
            let destination = sttx.get_account_id(destination_field);
            let credential_ids_present = sttx.is_field_present(sf("sfCredentialIDs"));
            if !account_delete_check_extra_features(
                credential_ids_present,
                view.rules().enabled(&protocol::feature_id("Credentials")),
            ) {
                return Ter::TEM_DISABLED;
            }
            let preflight = run_account_delete_preflight(
                AccountDeletePreflightFacts {
                    account,
                    destination,
                },
                || ledger::credential_helpers::check_fields(sttx, &view.rules()),
            );
            if preflight != Ter::TES_SUCCESS {
                return preflight;
            }

            let src_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
            let dst_keylet = protocol::account_keylet(Uint160::from_void(destination.data()));
            let src = match view.peek(src_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TER_NO_ACCOUNT,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let dst = match view.peek(dst_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TEC_NO_DST,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if dst.is_flag(protocol::lsfRequireDestTag)
                && !sttx.is_field_present(sf("sfDestinationTag"))
            {
                return Ter::TEC_DST_TAG_NEEDED;
            }
            let credentials_valid = ledger::credential_helpers::valid(view, sttx, &account)
                .unwrap_or(Ter::TEF_BAD_LEDGER);
            if credentials_valid != Ter::TES_SUCCESS {
                return credentials_valid;
            }
            if !credential_ids_present && dst.is_flag(protocol::lsfDepositAuth) {
                let preauth = protocol::deposit_preauth_keylet(
                    Uint160::from_void(destination.data()),
                    Uint160::from_void(account.data()),
                );
                let authorized = match view.exists(preauth) {
                    Ok(exists) => exists,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                if !authorized {
                    return Ter::TEC_NO_PERMISSION;
                }
            }

            if src.get_field_u32(sf("sfMintedNFTokens"))
                != src.get_field_u32(sf("sfBurnedNFTokens"))
            {
                return Ter::TEC_HAS_OBLIGATIONS;
            }
            let nft_min = protocol::nft_page_min_keylet(Uint160::from_void(account.data()));
            let nft_max = protocol::nft_page_max_keylet(Uint160::from_void(account.data()));
            match view.succ(nft_min.key, Some(nft_max.key.next())) {
                Ok(Some(_)) => return Ter::TEC_HAS_OBLIGATIONS,
                Ok(None) => {}
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }

            if src.is_field_present(sf("sfSponsor"))
                && src.get_account_id(sf("sfSponsor")) != destination
            {
                return Ter::TEC_NO_SPONSOR_PERMISSION;
            }
            if src.is_field_present(sf("sfSponsoringOwnerCount"))
                || src.is_field_present(sf("sfSponsoringAccountCount"))
            {
                return Ter::TEC_HAS_OBLIGATIONS;
            }

            let owner_dir = owner_dir_keylet(Uint160::from_void(account.data()));
            let mut entries = Vec::new();
            let owner_dir_exists = match view.exists(owner_dir) {
                Ok(exists) => exists,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if owner_dir_exists {
                let mut page = 0_u64;
                let mut visited_pages = std::collections::HashSet::new();
                loop {
                    if !visited_pages.insert(page) {
                        return Ter::TEF_BAD_LEDGER;
                    }
                    let page_keylet = protocol::page_keylet(owner_dir, page);
                    let node = match view.peek(page_keylet) {
                        Ok(Some(node)) => node,
                        Ok(None) => return Ter::TEF_BAD_LEDGER,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    };
                    entries.extend(node.get_field_v256(sf("sfIndexes")).value().iter().copied());
                    let next = node.get_field_u64(sf("sfIndexNext"));
                    if next == 0 || next == page {
                        break;
                    }
                    page = next;
                }
            }
            if entries.len() > ACCOUNT_DELETE_MAX_DELETABLE_DIR_ENTRIES as usize {
                return Ter::TEF_TOO_BIG;
            }
            for entry_key in &entries {
                let entry = match view.peek(protocol::child_keylet(*entry_key)) {
                    Ok(Some(entry)) => entry,
                    Ok(None) | Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                if !matches!(
                    entry.get_type(),
                    LedgerEntryType::Offer
                        | LedgerEntryType::SignerList
                        | LedgerEntryType::Ticket
                        | LedgerEntryType::DepositPreauth
                        | LedgerEntryType::NFTokenOffer
                        | LedgerEntryType::DID
                        | LedgerEntryType::Oracle
                        | LedgerEntryType::Credential
                        | LedgerEntryType::Delegate
                ) {
                    return Ter::TEC_HAS_OBLIGATIONS;
                }
            }

            if credential_ids_present {
                let verified = ledger::credential_helpers::verify_deposit_preauth(
                    sttx,
                    view,
                    &account,
                    &destination,
                    Some(dst.as_ref()),
                )
                .unwrap_or(Ter::TEF_BAD_LEDGER);
                if verified != Ter::TES_SUCCESS {
                    return verified;
                }
            }

            for entry_key in entries {
                let entry = match view.peek(protocol::child_keylet(entry_key)) {
                    Ok(Some(entry)) => entry,
                    Ok(None) | Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let result = match entry.get_type() {
                    LedgerEntryType::Offer => {
                        crate::state::offer_create::offer_delete_pub(view, &account, entry)
                    }
                    LedgerEntryType::SignerList => remove_signer_list(view, account),
                    LedgerEntryType::Ticket | LedgerEntryType::DID | LedgerEntryType::Oracle => {
                        remove_account_delete_owned_entry(view, account, entry)
                    }
                    LedgerEntryType::DepositPreauth => remove_deposit_preauth_entry(view, entry),
                    LedgerEntryType::NFTokenOffer => {
                        match ledger::nftoken_helpers::delete_token_offer(view, entry) {
                            Ok(true) => Ter::TES_SUCCESS,
                            Ok(false) => Ter::TEF_BAD_LEDGER,
                            Err(_) => Ter::TEF_BAD_LEDGER,
                        }
                    }
                    LedgerEntryType::Credential => {
                        ledger::credential_helpers::delete_sle(view, entry)
                            .unwrap_or(Ter::TEF_BAD_LEDGER)
                    }
                    LedgerEntryType::Delegate => {
                        remove_account_delete_delegate(view, account, entry)
                    }
                    _ => Ter::TEC_HAS_OBLIGATIONS,
                };
                if result != Ter::TES_SUCCESS {
                    return result;
                }
            }

            let owner_dir_exists = match view.exists(owner_dir) {
                Ok(exists) => exists,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if owner_dir_exists {
                match ledger::empty_dir_delete(view, &owner_dir) {
                    Ok(true) => {}
                    Ok(false) => return Ter::TEC_HAS_OBLIGATIONS,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                }
            }

            // Child cleanup mutates the source OwnerCount and may mutate the
            // destination when it sponsors one of those children. Refresh
            // both snapshots before constructing final AccountRoot states.
            let src = match view.peek(src_keylet) {
                Ok(Some(sle)) => sle,
                _ => return Ter::TEF_BAD_LEDGER,
            };
            let dst = match view.peek(dst_keylet) {
                Ok(Some(sle)) => sle,
                _ => return Ter::TEF_BAD_LEDGER,
            };
            let balance = src.get_field_amount(sf("sfBalance")).xrp();
            let mut src_obj = src.clone_as_object();
            src_obj.set_field_amount(
                sf("sfBalance"),
                STAmount::from_xrp_amount(XRPAmount::from_drops(0)),
            );
            let mut dst_obj = dst.clone_as_object();
            let dst_balance = dst.get_field_amount(sf("sfBalance")).xrp();
            dst_obj.set_field_amount(
                sf("sfBalance"),
                STAmount::from_xrp_amount(XRPAmount::from_drops(
                    dst_balance.drops().saturating_add(balance.drops()),
                )),
            );
            if src.is_field_present(sf("sfSponsor")) {
                // AccountDelete preclaim requires the destination to be the
                // account's sponsor, so `dst_obj` is also rippled's
                // `sponsorSle`. Keep both mutations on this one object.
                let sponsoring_account_count = dst.get_field_u32(sf("sfSponsoringAccountCount"));
                if sponsoring_account_count == 0 {
                    return Ter::TEF_INTERNAL;
                }
                if sponsoring_account_count == 1 {
                    dst_obj.make_field_absent(sf("sfSponsoringAccountCount"));
                } else {
                    dst_obj.set_field_u32(
                        sf("sfSponsoringAccountCount"),
                        sponsoring_account_count - 1,
                    );
                }
                // sfSponsor must not survive in the DeletedNode FinalFields;
                // the sponsorship invariant also requires it absent after.
                src_obj.make_field_absent(sf("sfSponsor"));
            }
            let destination_flags = dst.get_field_u32(sf("sfFlags"));
            if balance.drops() > 0 && destination_flags & protocol::lsfPasswordSpent != 0 {
                dst_obj.set_field_u32(
                    sf("sfFlags"),
                    destination_flags & !protocol::lsfPasswordSpent,
                );
            }
            if view
                .update(Arc::new(STLedgerEntry::from_stobject(dst_obj, *dst.key())))
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            if view
                .erase(Arc::new(STLedgerEntry::from_stobject(src_obj, *src.key())))
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            crate::state::payment::record_delivered_amount(STAmount::from_xrp_amount(balance));
            Ter::TES_SUCCESS
        }

        TxType::LEDGER_STATE_FIX => apply_ledger_state_fix(view, sttx),

        TxType::REGULAR_KEY_SET => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let keylet = protocol::account_keylet(Uint160::from_void(account.data()));
            let sle = match view.peek(keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TEF_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let mut obj = sle.clone_as_object();

            // SetRegularKey::doApply arms the one-time password-change fee when
            // this transaction's specialized minimum fee is zero.  This is
            // deliberately based on the calculated fee, not sfFee: a caller may
            // overpay a transaction whose minimum is still zero.
            match crate::state::application_root::calculate_sttx_base_fee(view, sttx) {
                Ok(0) => {
                    let flags = obj.get_field_u32(sf("sfFlags"));
                    obj.set_field_u32(sf("sfFlags"), flags | protocol::lsfPasswordSpent);
                }
                Ok(_) => {}
                Err(ter) => return ter,
            }

            if sttx.is_field_present(sf("sfRegularKey")) {
                obj.set_account_id(sf("sfRegularKey"), sttx.get_account_id(sf("sfRegularKey")));
            } else {
                // Removing the final alternative signing method while the
                // master key is disabled is forbidden.
                if obj.get_field_u32(sf("sfFlags")) & protocol::lsfDisableMaster != 0 {
                    let signer_list = match view
                        .peek(protocol::signers_keylet(Uint160::from_void(account.data())))
                    {
                        Ok(signer_list) => signer_list,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    };
                    if signer_list.is_none() {
                        return Ter::TEC_NO_ALTERNATIVE_KEY;
                    }
                }
                obj.make_field_absent(sf("sfRegularKey"));
            }

            if view
                .update(Arc::new(STLedgerEntry::from_stobject(obj, *sle.key())))
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }

        TxType::SIGNER_LIST_SET => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let quorum = sttx.get_field_u32(sf("sfSignerQuorum"));
            let (operation_entries, write_entries) = match parse_signer_entries(sttx) {
                Ok(parsed) => parsed,
                Err(err) => return err,
            };

            if !operation_entries.is_empty() {
                let validation = tx::run_signer_list_set_validate_quorum_and_signer_entries(
                    quorum,
                    &operation_entries,
                    &account,
                );
                if validation != Ter::TES_SUCCESS {
                    return validation;
                }
            }

            let operation = run_signer_list_set_determine_operation(
                quorum,
                sttx.is_field_present(sf("sfSignerEntries")),
                Ok(operation_entries),
            );
            if operation.result != Ter::TES_SUCCESS {
                return operation.result;
            }

            run_signer_list_set_do_apply(
                operation.operation,
                || Ter::TES_SUCCESS, // replace handled below
                || Ter::TES_SUCCESS, // destroy handled below
            );
            match operation.operation {
                SignerListSetOperation::Set => replace_signer_list(
                    view,
                    sttx,
                    account,
                    operation.quorum,
                    &write_entries,
                    pre_fee_balance_drops,
                ),
                SignerListSetOperation::Destroy => destroy_signer_list(view, account),
                _ => Ter::TES_SUCCESS,
            }
        }

        TxType::DEPOSIT_PREAUTH => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let authorize_field = sf("sfAuthorize");
            let unauthorize_field = sf("sfUnauthorize");
            let authorize_credentials_field = sf("sfAuthorizeCredentials");
            let unauthorize_credentials_field = sf("sfUnauthorizeCredentials");
            let authorize = sttx
                .is_field_present(authorize_field)
                .then(|| sttx.get_account_id(authorize_field));
            let unauthorize = sttx
                .is_field_present(unauthorize_field)
                .then(|| sttx.get_account_id(unauthorize_field));
            let authorize_credentials_present = sttx.is_field_present(authorize_credentials_field);
            let unauthorize_credentials_present =
                sttx.is_field_present(unauthorize_credentials_field);
            if !deposit_preauth_check_extra_features(
                authorize_credentials_present,
                unauthorize_credentials_present,
                view.rules().enabled(&protocol::feature_id("Credentials")),
            ) {
                return Ter::TEM_DISABLED;
            }
            let preflight = run_deposit_preauth_preflight(
                DepositPreauthPreflightFacts {
                    account,
                    authorize,
                    unauthorize,
                    authorize_is_zero: authorize.is_some_and(|value| value.is_zero()),
                    unauthorize_is_zero: unauthorize.is_some_and(|value| value.is_zero()),
                    authorize_credentials_present,
                    unauthorize_credentials_present,
                },
                || {
                    let credentials = sttx.get_field_array(if authorize_credentials_present {
                        authorize_credentials_field
                    } else {
                        unauthorize_credentials_field
                    });
                    ledger::credential_helpers::check_array(
                        &credentials,
                        ledger::credential_helpers::MAX_CREDENTIALS_ARRAY_SIZE,
                    )
                },
            );
            if preflight != Ter::TES_SUCCESS {
                return preflight;
            }

            let account_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
            let owner = match view.peek(account_keylet) {
                Ok(Some(owner)) => owner,
                Ok(None) => return Ter::TEF_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let sponsor_sle = match check_cash_reserve_sponsor(view, sttx) {
                Ok(sponsor) => sponsor,
                Err(ter) => return ter,
            };
            let owner_dir = owner_dir_keylet(Uint160::from_void(account.data()));

            if let Some(authorized) = authorize {
                let keylet = protocol::deposit_preauth_keylet(
                    Uint160::from_void(account.data()),
                    Uint160::from_void(authorized.data()),
                );
                let target_exists = match view.exists(protocol::account_keylet(Uint160::from_void(
                    authorized.data(),
                ))) {
                    Ok(exists) => exists,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                if !target_exists {
                    return Ter::TEC_NO_TARGET;
                }
                if view.rules().enabled(&protocol::fix_cleanup_3_3_0()) {
                    let authorized_root = match view.peek(protocol::account_keylet(
                        Uint160::from_void(authorized.data()),
                    )) {
                        Ok(Some(sle)) => sle,
                        _ => return Ter::TEF_BAD_LEDGER,
                    };
                    if ledger::is_pseudo_account(&authorized_root) {
                        return Ter::TEC_PSEUDO_ACCOUNT;
                    }
                }
                if match view.exists(keylet) {
                    Ok(exists) => exists,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                } {
                    return Ter::TEC_DUPLICATE;
                }
                let has_reserve = match check_cash_has_object_reserve(
                    view,
                    owner.as_ref(),
                    pre_fee_balance_drops,
                    sponsor_sle.as_ref(),
                ) {
                    Ok(has_reserve) => has_reserve,
                    Err(ter) => return ter,
                };
                if !has_reserve {
                    return Ter::TEC_INSUFFICIENT_RESERVE;
                }
                let owner_node = match ledger::dir_insert(
                    view,
                    &owner_dir,
                    keylet.key,
                    &describe_owner_dir(account),
                ) {
                    Ok(Some(page)) => page,
                    Ok(None) => return Ter::TEC_DIR_FULL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let mut preauth = STLedgerEntry::new(keylet);
                preauth.set_account_id(sf("sfAccount"), account);
                preauth.set_account_id(authorize_field, authorized);
                preauth.set_field_u64(sf("sfOwnerNode"), owner_node);
                if let Some(sponsor) = sponsor_sle.as_ref() {
                    preauth
                        .set_account_id(sf("sfSponsor"), sponsor.get_account_id(sf("sfAccount")));
                }
                if view.insert(Arc::new(preauth)).is_err() {
                    return Ter::TEF_BAD_LEDGER;
                }
                if ledger::increase_owner_count_for_object(view, &owner, sponsor_sle.as_ref())
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
                return Ter::TES_SUCCESS;
            }

            if let Some(unauthorized) = unauthorize {
                let keylet = protocol::deposit_preauth_keylet(
                    Uint160::from_void(account.data()),
                    Uint160::from_void(unauthorized.data()),
                );
                let preauth = match view.peek(keylet) {
                    Ok(Some(preauth)) => preauth,
                    Ok(None) => return Ter::TEC_NO_ENTRY,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                return remove_deposit_preauth_entry(view, preauth);
            }

            let credentials_field = if authorize_credentials_present {
                authorize_credentials_field
            } else {
                unauthorize_credentials_field
            };
            let credential_pairs =
                sorted_deposit_preauth_credentials(&sttx.get_field_array(credentials_field));
            let credential_hashes = deposit_preauth_credential_hashes(&credential_pairs);
            let keylet = protocol::deposit_preauth_credentials_keylet(
                Uint160::from_void(account.data()),
                &credential_hashes,
            );
            if authorize_credentials_present {
                for (issuer, _) in &credential_pairs {
                    let issuer_exists = match view
                        .exists(protocol::account_keylet(Uint160::from_void(issuer.data())))
                    {
                        Ok(exists) => exists,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    };
                    if !issuer_exists {
                        return Ter::TEC_NO_ISSUER;
                    }
                }
                if match view.exists(keylet) {
                    Ok(exists) => exists,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                } {
                    return Ter::TEC_DUPLICATE;
                }
                let has_reserve = match check_cash_has_object_reserve(
                    view,
                    owner.as_ref(),
                    pre_fee_balance_drops,
                    sponsor_sle.as_ref(),
                ) {
                    Ok(has_reserve) => has_reserve,
                    Err(ter) => return ter,
                };
                if !has_reserve {
                    return Ter::TEC_INSUFFICIENT_RESERVE;
                }
                let owner_node = match ledger::dir_insert(
                    view,
                    &owner_dir,
                    keylet.key,
                    &describe_owner_dir(account),
                ) {
                    Ok(Some(page)) => page,
                    Ok(None) => return Ter::TEC_DIR_FULL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let mut sorted_credentials = STArray::new(authorize_credentials_field);
                for (issuer, credential_type) in credential_pairs {
                    let mut credential = STObject::make_inner_object(sf("sfCredential"));
                    credential.set_account_id(sf("sfIssuer"), issuer);
                    credential.set_field_vl(sf("sfCredentialType"), &credential_type);
                    sorted_credentials.push_back(credential);
                }
                let mut preauth = STLedgerEntry::new(keylet);
                preauth.set_account_id(sf("sfAccount"), account);
                preauth.set_field_array(authorize_credentials_field, sorted_credentials);
                preauth.set_field_u64(sf("sfOwnerNode"), owner_node);
                if let Some(sponsor) = sponsor_sle.as_ref() {
                    preauth
                        .set_account_id(sf("sfSponsor"), sponsor.get_account_id(sf("sfAccount")));
                }
                if view.insert(Arc::new(preauth)).is_err() {
                    return Ter::TEF_BAD_LEDGER;
                }
                if ledger::increase_owner_count_for_object(view, &owner, sponsor_sle.as_ref())
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
                Ter::TES_SUCCESS
            } else {
                let preauth = match view.peek(keylet) {
                    Ok(Some(preauth)) => preauth,
                    Ok(None) => return Ter::TEC_NO_ENTRY,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                remove_deposit_preauth_entry(view, preauth)
            }
        }

        // --- Escrows ---
        TxType::ESCROW_CREATE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let dst_account = sttx.get_account_id(sf("sfDestination"));
            let amount = sttx.get_field_amount(sf("sfAmount"));
            let finish_after = if sttx.is_field_present(sf("sfFinishAfter")) {
                Some(sttx.get_field_u32(sf("sfFinishAfter")))
            } else {
                None
            };
            let cancel_after = if sttx.is_field_present(sf("sfCancelAfter")) {
                Some(sttx.get_field_u32(sf("sfCancelAfter")))
            } else {
                None
            };
            let condition = sttx
                .is_field_present(sf("sfCondition"))
                .then(|| sttx.get_field_vl(sf("sfCondition")).to_vec());
            let preflight = run_escrow_create_sttx_preflight(sttx, &view.rules());
            if preflight != Ter::TES_SUCCESS {
                return preflight;
            }
            if let protocol::Asset::MPTIssue(issue) = amount.asset() {
                if issue.issuer() == account {
                    return Ter::TEC_NO_PERMISSION;
                }
                let issuance =
                    match view.peek(protocol::mpt_issuance_keylet_from_mptid(issue.mpt_id())) {
                        Ok(Some(issuance)) => issuance,
                        Ok(None) => return Ter::TEC_OBJECT_NOT_FOUND,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    };
                if !issuance.is_flag(protocol::lsfMPTCanEscrow)
                    || issuance.get_account_id(sf("sfIssuer")) != issue.issuer()
                {
                    return Ter::TEC_NO_PERMISSION;
                }
                let sender_token = match view.peek(protocol::mptoken_keylet_from_mptid(
                    issue.mpt_id(),
                    Uint160::from_void(account.data()),
                )) {
                    Ok(Some(sender_token)) => sender_token,
                    Ok(None) => return Ter::TEC_OBJECT_NOT_FOUND,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                for party in [account, dst_account] {
                    let auth = ledger::mptoken_helpers::require_auth_mpt(view, &issue, &party)
                        .unwrap_or(Ter::TEF_BAD_LEDGER);
                    if auth != Ter::TES_SUCCESS {
                        return auth;
                    }
                    if party != issue.issuer() {
                        let frozen = frozen_mpt_result(ledger::mptoken_helpers::is_frozen_mpt(
                            view, &party, &issue,
                        ));
                        if frozen != Ter::TES_SUCCESS {
                            return frozen;
                        }
                    }
                }
                let transfer =
                    ledger::mptoken_helpers::can_transfer_mpt(view, &issue, &account, &dst_account)
                        .unwrap_or(Ter::TEF_BAD_LEDGER);
                if transfer != Ter::TES_SUCCESS {
                    return transfer;
                }
                if sender_token.get_field_u64(sf("sfMPTAmount")) < amount.mpt().value() as u64 {
                    return Ter::TEC_INSUFFICIENT_FUNDS;
                }
            }
            let mut facts = match build_escrow_create_facts(
                view,
                &account,
                &dst_account,
                &amount,
                finish_after,
                cancel_after,
            ) {
                Ok(facts) => facts,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            facts.destination_tag_present = sttx.is_field_present(sf("sfDestinationTag"));
            let reserve_sponsor = if view.rules().enabled(&protocol::feature_id("Sponsor")) {
                let source_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
                let source = match view.peek(source_keylet) {
                    Ok(Some(source)) => source,
                    Ok(None) => return Ter::TEF_INTERNAL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let sponsor = match check_cash_reserve_sponsor(view, sttx) {
                    Ok(sponsor) => sponsor,
                    Err(result) => return result,
                };
                facts.reserve_sufficient =
                    match check_cash_has_object_reserve(view, &source, None, sponsor.as_ref()) {
                        Ok(result) => result,
                        Err(result) => return result,
                    };
                if amount.native() {
                    let balance = source.get_field_amount(sf("sfBalance")).xrp().drops();
                    let owner_delta = if sponsor.is_some() { 0 } else { 1 };
                    let reserve =
                        ledger::effective_account_reserve(view.fees(), &source, owner_delta, 0)
                            as i64;
                    facts.xrp_balance_covers_amount = balance
                        .checked_sub(amount.xrp().drops())
                        .is_some_and(|remaining| remaining >= reserve);
                }
                sponsor
            } else {
                None
            };
            let source_tag = if sttx.is_field_present(sf("sfSourceTag")) {
                Some(sttx.get_field_u32(sf("sfSourceTag")))
            } else {
                None
            };
            let destination_tag = if sttx.is_field_present(sf("sfDestinationTag")) {
                Some(sttx.get_field_u32(sf("sfDestinationTag")))
            } else {
                None
            };
            let mut sink = ViewBackedEscrowCreateSink {
                view,
                account,
                dst_account,
                amount,
                escrow_key: Uint256::default(),
                escrow_seq: sttx.get_seq_value(),
                finish_after,
                cancel_after,
                condition,
                source_tag,
                destination_tag,
                reserve_sponsor,
                failure: None,
            };
            let result = run_escrow_create_do_apply(facts, &mut sink);
            sink.failure.unwrap_or(result)
        }
        TxType::ESCROW_FINISH => {
            let owner = sttx.get_account_id(sf("sfOwner"));
            let offer_seq = sttx.get_field_u32(sf("sfOfferSequence"));
            let escrow_keylet =
                protocol::escrow_keylet(Uint160::from_void(owner.data()), offer_seq);
            let escrow_sle = match view.peek(escrow_keylet) {
                Ok(Some(escrow_sle)) => escrow_sle,
                Ok(None) => {
                    return if view.rules().enabled(&protocol::feature_token_escrow()) {
                        Ter::TEC_INTERNAL
                    } else {
                        Ter::TEC_NO_TARGET
                    };
                }
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if escrow_sle.is_field_present(sf("sfFinishAfter")) {
                let finish_after = escrow_sle.get_field_u32(sf("sfFinishAfter"));
                if view.header().parent_close_time <= finish_after {
                    return Ter::TEC_NO_PERMISSION;
                }
            }
            if escrow_sle.is_field_present(sf("sfCancelAfter")) {
                let cancel_after = escrow_sle.get_field_u32(sf("sfCancelAfter"));
                if view.header().parent_close_time > cancel_after {
                    return Ter::TEC_NO_PERMISSION;
                }
            }
            let tx_condition = sttx
                .is_field_present(sf("sfCondition"))
                .then(|| sttx.get_field_vl(sf("sfCondition")));
            let tx_fulfillment = sttx
                .is_field_present(sf("sfFulfillment"))
                .then(|| sttx.get_field_vl(sf("sfFulfillment")));
            if tx_condition.is_some() != tx_fulfillment.is_some() {
                return Ter::TEM_MALFORMED;
            }
            if escrow_sle.is_field_present(sf("sfCondition")) {
                let stored_condition = escrow_sle.get_field_vl(sf("sfCondition"));
                let (Some(tx_condition), Some(tx_fulfillment)) = (tx_condition, tx_fulfillment)
                else {
                    return Ter::TEC_CRYPTOCONDITION_ERROR;
                };
                let Ok(condition) =
                    protocol::crypto::conditions::deserialize_condition(&stored_condition)
                else {
                    return Ter::TEC_CRYPTOCONDITION_ERROR;
                };
                let Ok(fulfillment) =
                    protocol::crypto::conditions::deserialize_fulfillment(&tx_fulfillment)
                else {
                    return Ter::TEC_CRYPTOCONDITION_ERROR;
                };
                if tx_condition != stored_condition
                    || !protocol::crypto::conditions::validate_no_message(&fulfillment, &condition)
                {
                    return Ter::TEC_CRYPTOCONDITION_ERROR;
                }
            } else if tx_condition.is_some() {
                return Ter::TEC_CRYPTOCONDITION_ERROR;
            }
            let destination = escrow_sle.get_account_id(sf("sfDestination"));
            let destination_keylet =
                protocol::account_keylet(Uint160::from_void(destination.data()));
            let destination_sle = match view.peek(destination_keylet) {
                Ok(Some(destination_sle)) => destination_sle,
                Ok(None) => return Ter::TEC_NO_DST,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let submitter = sttx.get_account_id(sf("sfAccount"));
            let deposit_auth = match ledger::credential_helpers::verify_deposit_preauth(
                sttx,
                view,
                &submitter,
                &destination,
                Some(&destination_sle),
            ) {
                Ok(result) => result,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if !is_tes_success(deposit_auth) {
                return deposit_auth;
            }

            let escrow_owner = escrow_sle.get_account_id(sf("sfAccount"));
            let owner_node = escrow_sle.get_field_u64(sf("sfOwnerNode"));
            if !ledger::dir_remove(
                view,
                &owner_dir_keylet(Uint160::from_void(escrow_owner.data())),
                owner_node,
                *escrow_sle.key(),
                true,
            )
            .unwrap_or(false)
            {
                return Ter::TEF_BAD_LEDGER;
            }
            if escrow_sle.is_field_present(sf("sfDestinationNode"))
                && !ledger::dir_remove(
                    view,
                    &owner_dir_keylet(Uint160::from_void(destination.data())),
                    escrow_sle.get_field_u64(sf("sfDestinationNode")),
                    *escrow_sle.key(),
                    true,
                )
                .unwrap_or(false)
            {
                return Ter::TEF_BAD_LEDGER;
            }

            let owner_keylet = protocol::account_keylet(Uint160::from_void(escrow_owner.data()));
            let owner_sle = match view.peek(owner_keylet) {
                Ok(Some(owner_sle)) => owner_sle,
                Ok(None) => return Ter::TEF_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let sponsor_enabled = view.rules().enabled(&protocol::feature_id("Sponsor"));
            if sponsor_enabled
                && ledger::decrease_owner_count_for_object(view, &owner_sle, &escrow_sle, 1)
                    .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }

            let amount = escrow_sle.get_field_amount(sf("sfAmount"));
            if amount.native() {
                let balance = destination_sle
                    .get_field_amount(sf("sfBalance"))
                    .xrp()
                    .drops();
                let Some(new_balance) = balance.checked_add(amount.xrp().drops()) else {
                    return Ter::TEF_BAD_LEDGER;
                };
                let mut obj = destination_sle.clone_as_object();
                obj.set_field_amount(
                    sf("sfBalance"),
                    STAmount::from_xrp_amount(XRPAmount::from_drops(new_balance)),
                );
                if view
                    .update(Arc::new(STLedgerEntry::from_stobject(
                        obj,
                        *destination_sle.key(),
                    )))
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
            } else {
                match amount.asset() {
                    protocol::Asset::Issue(_) => {
                        let locked_rate = if escrow_sle.is_field_present(sf("sfTransferRate")) {
                            escrow_sle.get_field_u32(sf("sfTransferRate"))
                        } else {
                            protocol::PARITY_RATE.value
                        };
                        let reserve_sponsor = if destination == submitter
                            && view.rules().enabled(&protocol::feature_id("Sponsor"))
                        {
                            match check_cash_reserve_sponsor(view, sttx) {
                                Ok(sponsor) => sponsor,
                                Err(result) => return result,
                            }
                        } else {
                            None
                        };
                        let result = unlock_escrow_iou(
                            view,
                            &amount,
                            locked_rate,
                            &escrow_owner,
                            &destination,
                            &submitter,
                            pre_fee_balance_drops,
                            reserve_sponsor.as_ref(),
                        );
                        if result != Ter::TES_SUCCESS {
                            return result;
                        }
                    }
                    protocol::Asset::MPTIssue(_) => {
                        let locked_rate = if escrow_sle.is_field_present(sf("sfTransferRate")) {
                            escrow_sle.get_field_u32(sf("sfTransferRate"))
                        } else {
                            protocol::PARITY_RATE.value
                        };
                        let (net_amount, gross_amount) = match escrow_mpt_unlock_amounts(
                            view,
                            &amount,
                            locked_rate,
                            &escrow_owner,
                            &destination,
                        ) {
                            Ok(amounts) => amounts,
                            Err(ter) => return ter,
                        };
                        let gross_amount = if view
                            .rules()
                            .enabled(&protocol::feature_id("fixTokenEscrowV1"))
                        {
                            &gross_amount
                        } else {
                            &net_amount
                        };
                        let reserve_sponsor = if destination == submitter
                            && view.rules().enabled(&protocol::feature_id("Sponsor"))
                        {
                            match check_cash_reserve_sponsor(view, sttx) {
                                Ok(sponsor) => sponsor,
                                Err(result) => return result,
                            }
                        } else {
                            None
                        };
                        let result = ledger::mptoken_helpers::unlock_escrow_mpt(
                            view,
                            &escrow_owner,
                            &destination,
                            &net_amount,
                            gross_amount,
                            destination == submitter,
                            pre_fee_balance_drops,
                            reserve_sponsor.as_ref(),
                        )
                        .unwrap_or(Ter::TEF_BAD_LEDGER);
                        if result != Ter::TES_SUCCESS {
                            return result;
                        }
                    }
                }
                if escrow_sle.is_field_present(sf("sfIssuerNode")) {
                    let issuer = amount.asset().issuer();
                    if !ledger::dir_remove(
                        view,
                        &owner_dir_keylet(Uint160::from_void(issuer.data())),
                        escrow_sle.get_field_u64(sf("sfIssuerNode")),
                        *escrow_sle.key(),
                        true,
                    )
                    .unwrap_or(false)
                    {
                        return Ter::TEF_BAD_LEDGER;
                    }
                }

                // rippled unconditionally updates the destination AccountRoot
                // after delivering an escrow.  For an IOU delivery this is not
                // a no-op: transaction threading records PreviousTxnID and
                // PreviousTxnLgrSeq on the destination account even when no
                // XRP balance field changed. Re-read the entry because the IOU
                // helper may have changed its owner count while creating a
                // destination trust line.
                let destination_sle = match view.peek(destination_keylet) {
                    Ok(Some(destination_sle)) => destination_sle,
                    _ => return Ter::TEF_BAD_LEDGER,
                };
                if view.update(destination_sle).is_err() {
                    return Ter::TEF_BAD_LEDGER;
                }
            }

            if !sponsor_enabled {
                let current_owner = match view.peek(owner_keylet) {
                    Ok(Some(owner_sle)) => owner_sle,
                    _ => return Ter::TEF_BAD_LEDGER,
                };
                if ledger::decrease_owner_count_for_object(view, &current_owner, &escrow_sle, 1)
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
            }
            if view.erase(escrow_sle).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }
        TxType::ESCROW_CANCEL => {
            let owner = sttx.get_account_id(sf("sfOwner"));
            let offer_seq = sttx.get_field_u32(sf("sfOfferSequence"));
            let escrow_keylet =
                protocol::escrow_keylet(Uint160::from_void(owner.data()), offer_seq);
            let escrow_sle = match view.peek(escrow_keylet) {
                Ok(Some(escrow_sle)) => escrow_sle,
                Ok(None) => {
                    return if view.rules().enabled(&protocol::feature_token_escrow()) {
                        Ter::TEC_INTERNAL
                    } else {
                        Ter::TEC_NO_TARGET
                    };
                }
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if !escrow_sle.is_field_present(sf("sfCancelAfter")) {
                return Ter::TEC_NO_PERMISSION;
            }
            let cancel_after = escrow_sle.get_field_u32(sf("sfCancelAfter"));
            if view.header().parent_close_time <= cancel_after {
                return Ter::TEC_NO_PERMISSION;
            }
            let escrow_owner = escrow_sle.get_account_id(sf("sfAccount"));
            if !ledger::dir_remove(
                view,
                &owner_dir_keylet(Uint160::from_void(escrow_owner.data())),
                escrow_sle.get_field_u64(sf("sfOwnerNode")),
                *escrow_sle.key(),
                true,
            )
            .unwrap_or(false)
            {
                return Ter::TEF_BAD_LEDGER;
            }
            let destination = escrow_sle.get_account_id(sf("sfDestination"));
            if escrow_sle.is_field_present(sf("sfDestinationNode"))
                && !ledger::dir_remove(
                    view,
                    &owner_dir_keylet(Uint160::from_void(destination.data())),
                    escrow_sle.get_field_u64(sf("sfDestinationNode")),
                    *escrow_sle.key(),
                    true,
                )
                .unwrap_or(false)
            {
                return Ter::TEF_BAD_LEDGER;
            }

            let owner_keylet = protocol::account_keylet(Uint160::from_void(escrow_owner.data()));
            let owner_sle = match view.peek(owner_keylet) {
                Ok(Some(owner_sle)) => owner_sle,
                Ok(None) => return Ter::TEF_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let amount = escrow_sle.get_field_amount(sf("sfAmount"));
            if amount.native() {
                let balance = owner_sle.get_field_amount(sf("sfBalance")).xrp().drops();
                let Some(new_balance) = balance.checked_add(amount.xrp().drops()) else {
                    return Ter::TEF_BAD_LEDGER;
                };
                let mut obj = owner_sle.clone_as_object();
                obj.set_field_amount(
                    sf("sfBalance"),
                    STAmount::from_xrp_amount(XRPAmount::from_drops(new_balance)),
                );
                if view
                    .update(Arc::new(STLedgerEntry::from_stobject(
                        obj,
                        *owner_sle.key(),
                    )))
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
            } else {
                match amount.asset() {
                    protocol::Asset::Issue(issue) => {
                        let result = ledger::ripple_state_helpers::issue_iou(
                            view,
                            &escrow_owner,
                            &amount,
                            &issue,
                        );
                        if result != Ter::TES_SUCCESS {
                            return result;
                        }
                    }
                    protocol::Asset::MPTIssue(issue) => {
                        let submitter = sttx.get_account_id(sf("sfAccount"));
                        let (net_amount, gross_amount) = match escrow_mpt_unlock_amounts(
                            view,
                            &amount,
                            protocol::PARITY_RATE.value,
                            &escrow_owner,
                            &escrow_owner,
                        ) {
                            Ok(amounts) => amounts,
                            Err(ter) => return ter,
                        };
                        let gross_amount = if view
                            .rules()
                            .enabled(&protocol::feature_id("fixTokenEscrowV1"))
                        {
                            &gross_amount
                        } else {
                            &net_amount
                        };
                        let create_asset = escrow_owner == submitter;
                        if create_asset
                            && escrow_owner != issue.issuer()
                            && !view
                                .rules()
                                .enabled(&protocol::feature_id("fixCleanup3_2_0"))
                        {
                            let token = protocol::mptoken_keylet_from_mptid(
                                issue.mpt_id(),
                                Uint160::from_void(escrow_owner.data()),
                            );
                            match view.peek(token) {
                                Ok(None) => return Ter::TEF_INTERNAL,
                                Ok(Some(_)) => {}
                                Err(_) => return Ter::TEF_BAD_LEDGER,
                            }
                        }
                        let reserve_sponsor = if escrow_owner == submitter
                            && view.rules().enabled(&protocol::feature_id("Sponsor"))
                        {
                            match check_cash_reserve_sponsor(view, sttx) {
                                Ok(sponsor) => sponsor,
                                Err(result) => return result,
                            }
                        } else {
                            None
                        };
                        let result = ledger::mptoken_helpers::unlock_escrow_mpt(
                            view,
                            &escrow_owner,
                            &escrow_owner,
                            &net_amount,
                            gross_amount,
                            create_asset,
                            pre_fee_balance_drops,
                            reserve_sponsor.as_ref(),
                        )
                        .unwrap_or(Ter::TEF_BAD_LEDGER);
                        if result != Ter::TES_SUCCESS {
                            return result;
                        }
                    }
                }
            }
            if !amount.native() && escrow_sle.is_field_present(sf("sfIssuerNode")) {
                let issuer = amount.asset().issuer();
                if !ledger::dir_remove(
                    view,
                    &owner_dir_keylet(Uint160::from_void(issuer.data())),
                    escrow_sle.get_field_u64(sf("sfIssuerNode")),
                    *escrow_sle.key(),
                    true,
                )
                .unwrap_or(false)
                {
                    return Ter::TEF_BAD_LEDGER;
                }
            }
            let current_owner = match view.peek(owner_keylet) {
                Ok(Some(owner_sle)) => owner_sle,
                _ => return Ter::TEF_BAD_LEDGER,
            };
            if ledger::decrease_owner_count_for_object(view, &current_owner, &escrow_sle, 1)
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            if view.erase(escrow_sle).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }

        // --- Checks ---
        TxType::CHECK_CREATE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let dst = sttx.get_account_id(sf("sfDestination"));
            let send_max = sttx.get_field_amount(sf("sfSendMax"));
            // Preclaim: destination must exist
            let dst_keylet = protocol::account_keylet(Uint160::from_void(dst.data()));
            let dst_sle = match view.peek(dst_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TEC_NO_DST,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            // Preclaim: check lsfDisallowIncomingCheck on destination
            if dst_sle.is_flag(protocol::lsfDisallowIncomingCheck) {
                return Ter::TEC_NO_PERMISSION;
            }
            // Pseudo-accounts cannot cash checks. The discriminator fields
            // themselves are amendment-gated, so rippled applies this check
            // unconditionally once such an AccountRoot exists.
            if ledger::is_pseudo_account(&dst_sle) {
                return Ter::TEC_NO_PERMISSION;
            }
            // Preclaim: destination requires DestinationTag
            if dst_sle.is_flag(protocol::lsfRequireDestTag)
                && !sttx.is_field_present(sf("sfDestinationTag"))
            {
                return Ter::TEC_DST_TAG_NEEDED;
            }
            let mpt_result = check_mpt_check_create_allowed(view, &account, &dst, &send_max);
            if mpt_result != Ter::TES_SUCCESS {
                return mpt_result;
            }
            if sttx.is_field_present(sf("sfExpiration"))
                && view.header().parent_close_time >= sttx.get_field_u32(sf("sfExpiration"))
            {
                return Ter::TEC_EXPIRED;
            }
            // A Check adds one owned object. Match rippled CheckCreate's
            // pre-fee reserve check so paying the fee may dip into reserve but
            // creating the Check may not.
            let source_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
            let source_sle = match view.peek(source_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TEF_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let reserve_sponsor = if view.rules().enabled(&protocol::feature_id("Sponsor")) {
                match check_cash_reserve_sponsor(view, sttx) {
                    Ok(sponsor) => sponsor,
                    Err(result) => return result,
                }
            } else {
                None
            };
            match check_cash_has_object_reserve(
                view,
                &source_sle,
                pre_fee_balance_drops,
                reserve_sponsor.as_ref(),
            ) {
                Ok(true) => {}
                Ok(false) => return Ter::TEC_INSUFFICIENT_RESERVE,
                Err(result) => return result,
            }
            let check_keylet =
                protocol::check_keylet(Uint160::from_void(account.data()), sttx.get_seq_value());
            let mut sle = STLedgerEntry::new(check_keylet);
            sle.set_account_id(sf("sfAccount"), account);
            sle.set_account_id(sf("sfDestination"), dst);
            sle.set_field_amount(sf("sfSendMax"), send_max);
            sle.set_field_u32(sf("sfSequence"), sttx.get_seq_value());
            if sttx.is_field_present(sf("sfSourceTag")) {
                sle.set_field_u32(sf("sfSourceTag"), sttx.get_field_u32(sf("sfSourceTag")));
            }
            if sttx.is_field_present(sf("sfDestinationTag")) {
                sle.set_field_u32(
                    sf("sfDestinationTag"),
                    sttx.get_field_u32(sf("sfDestinationTag")),
                );
            }
            if sttx.is_field_present(sf("sfExpiration")) {
                sle.set_field_u32(sf("sfExpiration"), sttx.get_field_u32(sf("sfExpiration")));
            }
            if sttx.is_field_present(sf("sfInvoiceID")) {
                sle.set_field_h256(sf("sfInvoiceID"), sttx.get_field_h256(sf("sfInvoiceID")));
            }
            if let Some(sponsor) = reserve_sponsor.as_ref() {
                sle.set_account_id(sf("sfSponsor"), sponsor.get_account_id(sf("sfAccount")));
            }
            // Insert the destination link first, as rippled does, unless the
            // Check is self-directed. The sandbox discards the entire attempt
            // on any following TER, so a failed link cannot leave partial state.
            if dst != account {
                let dst_dir = owner_dir_keylet(Uint160::from_void(dst.data()));
                match ledger::dir_insert(view, &dst_dir, check_keylet.key, &describe_owner_dir(dst))
                {
                    Ok(Some(page)) => sle.set_field_u64(sf("sfDestinationNode"), page),
                    Ok(None) => return Ter::TEC_DIR_FULL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                }
            }
            // Add to owner directory.
            let owner_dir = owner_dir_keylet(Uint160::from_void(account.data()));
            match ledger::dir_insert(
                view,
                &owner_dir,
                check_keylet.key,
                &describe_owner_dir(account),
            ) {
                Ok(Some(page)) => sle.set_field_u64(sf("sfOwnerNode"), page),
                Ok(None) => return Ter::TEC_DIR_FULL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
            if view.insert(Arc::new(sle)).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            if ledger::increase_owner_count_for_object(view, &source_sle, reserve_sponsor.as_ref())
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }
        TxType::CHECK_CANCEL => {
            let tx_account = sttx.get_account_id(sf("sfAccount"));
            let check_id = sttx.get_field_h256(sf("sfCheckID"));
            let check_keylet = protocol::unchecked_keylet(check_id);
            match view.peek(check_keylet) {
                Ok(Some(check_sle)) => {
                    let owner = check_sle.get_account_id(sf("sfAccount"));
                    let destination = check_sle.get_account_id(sf("sfDestination"));
                    // Preclaim: if check is not expired, only creator or destination may cancel
                    let expired = if check_sle.is_field_present(sf("sfExpiration")) {
                        let exp = check_sle.get_field_u32(sf("sfExpiration"));
                        view.header().parent_close_time >= exp
                    } else {
                        false
                    };
                    if !expired && tx_account != owner && tx_account != destination {
                        return Ter::TEC_NO_PERMISSION;
                    }
                    // Match rippled CheckCancel::doApply: remove the destination
                    // link first (unless self-issued), then the owner link. A
                    // malformed directory must fail the transaction rather than
                    // allowing a partially-unlinked Check to be erased.
                    if owner != destination {
                        let dst_node = check_sle.get_field_u64(sf("sfDestinationNode"));
                        let dst_dir = owner_dir_keylet(Uint160::from_void(destination.data()));
                        if !matches!(
                            ledger::dir_remove(view, &dst_dir, dst_node, *check_sle.key(), true),
                            Ok(true)
                        ) {
                            return Ter::TEF_BAD_LEDGER;
                        }
                    }
                    let owner_node = check_sle.get_field_u64(sf("sfOwnerNode"));
                    let owner_dir = owner_dir_keylet(Uint160::from_void(owner.data()));
                    if !matches!(
                        ledger::dir_remove(view, &owner_dir, owner_node, *check_sle.key(), true),
                        Ok(true)
                    ) {
                        return Ter::TEF_BAD_LEDGER;
                    }
                    let Ok(Some(acct)) =
                        view.peek(protocol::account_keylet(Uint160::from_void(owner.data())))
                    else {
                        return Ter::TEF_BAD_LEDGER;
                    };
                    if ledger::decrease_owner_count_for_object(view, &acct, &check_sle, 1).is_err()
                    {
                        return Ter::TEF_BAD_LEDGER;
                    }
                    if view.erase(check_sle).is_err() {
                        return Ter::TEF_BAD_LEDGER;
                    }
                }
                Ok(None) => return Ter::TEC_NO_ENTRY,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
            Ter::TES_SUCCESS
        }
        TxType::CHECK_CASH => {
            let check_id = sttx.get_field_h256(sf("sfCheckID"));
            let check_keylet = protocol::unchecked_keylet(check_id);
            let check_sle = match view.peek(check_keylet) {
                Ok(Some(check_sle)) => check_sle,
                Ok(None) => return Ter::TEC_NO_ENTRY,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };

            let source = check_sle.get_account_id(sf("sfAccount"));
            let destination = check_sle.get_account_id(sf("sfDestination"));
            let tx_account = sttx.get_account_id(sf("sfAccount"));
            if tx_account != destination {
                return Ter::TEC_NO_PERMISSION;
            }
            if check_sle.is_field_present(sf("sfExpiration"))
                && view.header().parent_close_time >= check_sle.get_field_u32(sf("sfExpiration"))
            {
                return Ter::TEC_EXPIRED;
            }

            let amount_present = sttx.is_field_present(sf("sfAmount"));
            let deliver_min_present = sttx.is_field_present(sf("sfDeliverMin"));
            if amount_present == deliver_min_present {
                return Ter::TEM_MALFORMED;
            }
            let requested = if amount_present {
                sttx.get_field_amount(sf("sfAmount"))
            } else {
                sttx.get_field_amount(sf("sfDeliverMin"))
            };
            let send_max = check_sle.get_field_amount(sf("sfSendMax"));
            if requested.asset() != send_max.asset() {
                return Ter::TEM_MALFORMED;
            }
            if requested > send_max {
                return Ter::TEC_PATH_PARTIAL;
            }
            if view
                .rules()
                .enabled(&protocol::feature_id("fixCleanup3_2_0"))
                && !send_max.is_legal_mpt()
            {
                return Ter::TEF_BAD_LEDGER;
            }

            let mpt_result = check_mpt_check_cash_allowed(view, &source, &destination, &requested);
            if mpt_result != Ter::TES_SUCCESS {
                return mpt_result;
            }
            let reserve_sponsor = match check_cash_reserve_sponsor(view, sttx) {
                Ok(sponsor) => sponsor,
                Err(ter) => return ter,
            };

            let mut delivered_amount = None;
            if requested.native() {
                // The Check will be removed below, so release one owner-reserve
                // increment before calculating what its source can send.
                // rippled uses owner-count delta zero when the Check is
                // sponsored: deleting the Check releases the sponsor's
                // reserve, not the source account's reserve.
                let source_owner_delta = if check_sle.is_field_present(sf("sfSponsor")) {
                    0
                } else {
                    -1
                };
                let src_liquid =
                    match ledger::apply_view::xrp_liquid(view, &source, source_owner_delta) {
                        Ok(liquid) => liquid,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    };
                let xrp_deliver = if deliver_min_present {
                    XRPAmount::from_drops(
                        requested
                            .xrp()
                            .drops()
                            .max(send_max.xrp().drops().min(src_liquid.drops())),
                    )
                } else {
                    requested.xrp()
                };
                if src_liquid < xrp_deliver {
                    return Ter::TEC_UNFUNDED_PAYMENT;
                }
                let result = ledger::ripple_state_helpers::transfer_xrp(
                    view,
                    &source,
                    &destination,
                    xrp_deliver,
                );
                if !is_tes_success(result) {
                    return result;
                }
                if source != destination && deliver_min_present {
                    delivered_amount = Some(STAmount::from_xrp_amount(xrp_deliver));
                }
            } else if matches!(requested.asset(), Asset::Issue(_)) {
                // CheckCash.cpp runs ordinary default-path flow for IOUs. For
                // DeliverMin it requests a deliberately unreachable maximum,
                // allowing flow to deliver everything affordable under
                // SendMax, then verifies the minimum afterward.
                let flow_deliver = if deliver_min_present {
                    STAmount::new_with_asset(
                        sf("sfAmount"),
                        requested.asset(),
                        protocol::ST_AMOUNT_MAX_MANTISSA / 2,
                        protocol::ST_AMOUNT_MAX_OFFSET,
                        false,
                    )
                } else {
                    requested.clone()
                };
                let Asset::Issue(issue) = requested.asset() else {
                    unreachable!("IOU branch")
                };
                let mut limit_override = None;
                if destination != issue.issuer() {
                    let line_keylet = protocol::line(destination, issue.issuer(), issue.currency);
                    let line_missing = match view.read(line_keylet) {
                        Ok(line) => line.is_none(),
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    };
                    if line_missing {
                        let Ok(Some(destination_sle)) = view.peek(protocol::account_keylet(
                            Uint160::from_void(destination.data()),
                        )) else {
                            return Ter::TEF_BAD_LEDGER;
                        };
                        match check_cash_has_object_reserve(
                            view,
                            &destination_sle,
                            pre_fee_balance_drops,
                            reserve_sponsor.as_ref(),
                        ) {
                            Ok(true) => {}
                            Ok(false) => return Ter::TEC_NO_LINE_INSUF_RESERVE,
                            Err(ter) => return ter,
                        }
                        let limit = STAmount::new_with_asset(
                            sf("sfLimitAmount"),
                            protocol::Asset::Issue(protocol::Issue::new(
                                issue.currency,
                                destination,
                            )),
                            0,
                            0,
                            false,
                        );
                        let create = crate::state::trust_set::trust_create(
                            view,
                            destination > issue.issuer(),
                            &destination,
                            &issue.issuer(),
                            line_keylet.key,
                            &destination_sle,
                            false,
                            !destination_sle.is_flag(protocol::lsfDefaultRipple),
                            false,
                            false,
                            &limit,
                            0,
                            0,
                            reserve_sponsor.as_ref(),
                        );
                        if create != Ter::TES_SUCCESS {
                            return create;
                        }
                    }
                    let line = match view.peek(line_keylet) {
                        Ok(Some(line)) => line,
                        Ok(None) => return Ter::TEC_NO_LINE,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    };
                    let limit_field = if destination < issue.issuer() {
                        sf("sfLowLimit")
                    } else {
                        sf("sfHighLimit")
                    };
                    let saved_limit = line.get_field_amount(limit_field);
                    let mut updated = line.clone_as_object();
                    updated.set_field_amount(
                        limit_field,
                        STAmount::new_with_asset(
                            limit_field,
                            saved_limit.asset(),
                            protocol::ST_AMOUNT_MAX_MANTISSA,
                            protocol::ST_AMOUNT_MAX_OFFSET,
                            false,
                        ),
                    );
                    if view
                        .update(Arc::new(STLedgerEntry::from_stobject(updated, *line.key())))
                        .is_err()
                    {
                        return Ter::TEF_BAD_LEDGER;
                    }
                    limit_override = Some((*line.key(), limit_field, saved_limit));
                }
                let paths = protocol::STPathSet::new(sf("sfPaths"));
                let (strand_ter, strands) = ledger::flow_engine::strand_builder::to_strands_checked(
                    view,
                    &source,
                    &destination,
                    &flow_deliver.asset(),
                    Some(&send_max.asset()),
                    &paths,
                    true,
                    true,
                    false,
                );
                if strand_ter != Ter::TES_SUCCESS {
                    return strand_ter;
                }
                let flow = ledger::flow_engine::strand_flow::execute_strands(
                    view,
                    &strands,
                    &flow_deliver,
                    deliver_min_present,
                    ledger::ripple_calc::OfferCrossing::No,
                    Some(&send_max),
                    &source,
                    &destination,
                    None,
                    None,
                );
                if let Some((line_key, limit_field, saved_limit)) = limit_override {
                    match view.peek(protocol::unchecked_keylet(line_key)) {
                        Ok(Some(line)) => {
                            let mut restored = line.clone_as_object();
                            restored.set_field_amount(limit_field, saved_limit);
                            if view
                                .update(Arc::new(STLedgerEntry::from_stobject(restored, line_key)))
                                .is_err()
                            {
                                return Ter::TEF_BAD_LEDGER;
                            }
                        }
                        Ok(None) | Err(_) => return Ter::TEF_BAD_LEDGER,
                    }
                }
                if flow.ter != Ter::TES_SUCCESS {
                    return flow.ter;
                }
                if flow.actual_out < requested {
                    return Ter::TEC_PATH_PARTIAL;
                }
                delivered_amount = Some(flow.actual_out);
            } else {
                // CheckCash.cpp routes MPTs through the same default-path Flow
                // engine as IOUs. In particular, DeliverMin requests the
                // largest integral output whose rounded-up input remains
                // within SendMax; a hand-written endpoint transfer can differ
                // in pass ordering, transfer-fee rounding, or metadata.
                let Asset::MPTIssue(issue) = requested.asset() else {
                    unreachable!("native and IOU handled above")
                };
                if destination != issue.issuer() {
                    let token_keylet = protocol::mptoken_keylet_from_mptid(
                        issue.mpt_id(),
                        Uint160::from_void(destination.data()),
                    );
                    let token_missing = match view.read(token_keylet) {
                        Ok(token) => token.is_none(),
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    };
                    if token_missing {
                        let Ok(Some(destination_sle)) = view.peek(protocol::account_keylet(
                            Uint160::from_void(destination.data()),
                        )) else {
                            return Ter::TEF_BAD_LEDGER;
                        };
                        match check_cash_has_object_reserve(
                            view,
                            &destination_sle,
                            pre_fee_balance_drops,
                            reserve_sponsor.as_ref(),
                        ) {
                            Ok(true) => {}
                            Ok(false) => return Ter::TEC_INSUFFICIENT_RESERVE,
                            Err(ter) => return ter,
                        }
                        let create = ledger::mptoken_helpers::check_create_mpt_with_sponsor(
                            view,
                            &issue,
                            &destination,
                            reserve_sponsor.as_ref(),
                        )
                        .unwrap_or(Ter::TEF_BAD_LEDGER);
                        if create != Ter::TES_SUCCESS {
                            return create;
                        }
                    }
                }
                let flow_deliver = if deliver_min_present {
                    let mut maximum = send_max.mpt();
                    if source != issue.issuer() && destination != issue.issuer() {
                        let rate = match ledger::mptoken_helpers::transfer_rate_mpt(
                            view,
                            issue.mpt_id(),
                        ) {
                            Ok(rate) => rate,
                            Err(_) => return Ter::TEF_BAD_LEDGER,
                        };
                        maximum = match protocol::mpt_amount::mul_ratio(
                            maximum,
                            protocol::QUALITY_ONE,
                            rate.value,
                            false,
                        ) {
                            Ok(maximum) => maximum,
                            Err(_) => return Ter::TEC_INTERNAL,
                        };
                    }
                    STAmount::from_mpt_amount(sf("sfAmount"), maximum, issue)
                } else {
                    requested.clone()
                };
                let paths = protocol::STPathSet::new(sf("sfPaths"));
                let (strand_ter, strands) = ledger::flow_engine::strand_builder::to_strands_checked(
                    view,
                    &source,
                    &destination,
                    &flow_deliver.asset(),
                    Some(&send_max.asset()),
                    &paths,
                    true,
                    true,
                    false,
                );
                if strand_ter != Ter::TES_SUCCESS {
                    return strand_ter;
                }
                let flow = ledger::flow_engine::strand_flow::execute_strands(
                    view,
                    &strands,
                    &flow_deliver,
                    deliver_min_present,
                    ledger::ripple_calc::OfferCrossing::No,
                    Some(&send_max),
                    &source,
                    &destination,
                    None,
                    None,
                );
                if flow.ter != Ter::TES_SUCCESS {
                    return flow.ter;
                }
                if flow.actual_out < requested {
                    return Ter::TEC_PATH_PARTIAL;
                }
                delivered_amount = Some(flow.actual_out);
            }

            // CheckCash.cpp removes the destination directory first, then the
            // source owner directory, decrements the *source* owner count, and
            // only then erases the Check. Each missing directory entry is a
            // malformed ledger, not a best-effort cleanup.
            let destination_node = check_sle.get_field_u64(sf("sfDestinationNode"));
            if !ledger::dir_remove(
                view,
                &owner_dir_keylet(Uint160::from_void(destination.data())),
                destination_node,
                *check_sle.key(),
                true,
            )
            .unwrap_or(false)
            {
                return Ter::TEF_BAD_LEDGER;
            }
            let owner_node = check_sle.get_field_u64(sf("sfOwnerNode"));
            if !ledger::dir_remove(
                view,
                &owner_dir_keylet(Uint160::from_void(source.data())),
                owner_node,
                *check_sle.key(),
                true,
            )
            .unwrap_or(false)
            {
                return Ter::TEF_BAD_LEDGER;
            }
            if let Ok(Some(source_sle)) =
                view.peek(protocol::account_keylet(Uint160::from_void(source.data())))
            {
                if ledger::decrease_owner_count_for_object(view, &source_sle, &check_sle, 1)
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
            } else {
                return Ter::TEF_BAD_LEDGER;
            }
            if view.erase(check_sle).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            if let Some(delivered_amount) = delivered_amount {
                crate::state::payment::record_delivered_amount(delivered_amount);
            }
            Ter::TES_SUCCESS
        }

        // --- PayChans ---
        TxType::PAYCHAN_CREATE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let dst = sttx.get_account_id(sf("sfDestination"));
            let amount = sttx.get_field_amount(sf("sfAmount"));
            let settle_delay = sttx.get_field_u32(sf("sfSettleDelay"));
            let src_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
            let src_sle = match view.peek(src_keylet) {
                Ok(Some(src_sle)) => src_sle,
                Ok(None) => return Ter::TEF_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };

            if view
                .rules()
                .enabled(&protocol::feature_id("fixPayChanCancelAfter"))
                && sttx.is_field_present(sf("sfCancelAfter"))
                && view.header().parent_close_time > sttx.get_field_u32(sf("sfCancelAfter"))
            {
                return Ter::TEC_EXPIRED;
            }

            let reserve_sponsor = if view.rules().enabled(&protocol::feature_id("Sponsor")) {
                let sponsor = match check_cash_reserve_sponsor(view, sttx) {
                    Ok(sponsor) => sponsor,
                    Err(result) => return result,
                };
                let has_reserve = match check_cash_has_object_reserve(
                    view,
                    &src_sle,
                    pre_fee_balance_drops,
                    sponsor.as_ref(),
                ) {
                    Ok(has_reserve) => has_reserve,
                    Err(result) => return result,
                };
                if !has_reserve {
                    return Ter::TEC_INSUFFICIENT_RESERVE;
                }
                let Some(pre_fee_balance) = pre_fee_balance_drops else {
                    return Ter::TEF_BAD_LEDGER;
                };
                let owner_delta = if sponsor.is_some() { 0 } else { 1 };
                let source_reserve =
                    ledger::effective_account_reserve(view.fees(), &src_sle, owner_delta, 0) as i64;
                if pre_fee_balance.saturating_sub(amount.xrp().drops()) < source_reserve {
                    return Ter::TEC_UNFUNDED;
                }
                sponsor
            } else {
                None
            };

            // Check destination's lsfRequireDestTag
            match view.peek(protocol::account_keylet(Uint160::from_void(dst.data()))) {
                Ok(Some(dst_sle)) => {
                    if ledger::is_pseudo_account(&dst_sle) {
                        return Ter::TEC_NO_PERMISSION;
                    }
                    let dst_flags = dst_sle.get_field_u32(sf("sfFlags"));
                    // lsfRequireDestTag = 0x00020000
                    if (dst_flags & 0x00020000) != 0
                        && !sttx.is_field_present(sf("sfDestinationTag"))
                    {
                        return Ter::TEC_DST_TAG_NEEDED;
                    }
                    // lsfDisallowIncomingPayChan = 0x10000000
                    if (dst_flags & 0x10000000) != 0 {
                        return Ter::TEC_NO_PERMISSION;
                    }
                }
                Ok(None) => return Ter::TEC_NO_DST,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }

            let chan_keylet = protocol::pay_channel_keylet(
                Uint160::from_void(account.data()),
                Uint160::from_void(dst.data()),
                sttx.get_seq_value(),
            );
            let mut sle = STLedgerEntry::new(chan_keylet);
            sle.set_account_id(sf("sfAccount"), account);
            sle.set_account_id(sf("sfDestination"), dst);
            sle.set_field_amount(sf("sfAmount"), amount.clone());
            sle.set_field_amount(sf("sfBalance"), STAmount::from_xrp_amount(XRPAmount::new()));
            sle.set_field_u32(sf("sfSettleDelay"), settle_delay);
            if view
                .rules()
                .enabled(&protocol::feature_id("fixIncludeKeyletFields"))
            {
                sle.set_field_u32(sf("sfSequence"), sttx.get_seq_value());
            }
            let pk = sttx.get_field_vl(sf("sfPublicKey"));
            sle.set_field_vl(sf("sfPublicKey"), &pk);
            // Copy optional fields
            if sttx.is_field_present(sf("sfCancelAfter")) {
                sle.set_field_u32(sf("sfCancelAfter"), sttx.get_field_u32(sf("sfCancelAfter")));
            }
            if sttx.is_field_present(sf("sfSourceTag")) {
                sle.set_field_u32(sf("sfSourceTag"), sttx.get_field_u32(sf("sfSourceTag")));
            }
            if sttx.is_field_present(sf("sfDestinationTag")) {
                sle.set_field_u32(
                    sf("sfDestinationTag"),
                    sttx.get_field_u32(sf("sfDestinationTag")),
                );
            }
            // Add to owner directory
            let owner_dir = owner_dir_keylet(Uint160::from_void(account.data()));
            match ledger::dir_insert(
                view,
                &owner_dir,
                chan_keylet.key,
                &describe_owner_dir(account),
            ) {
                Ok(Some(page)) => sle.set_field_u64(sf("sfOwnerNode"), page),
                Ok(None) => return Ter::TEC_DIR_FULL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
            // Add to destination's owner directory
            let dst_dir = owner_dir_keylet(Uint160::from_void(dst.data()));
            match ledger::dir_insert(view, &dst_dir, chan_keylet.key, &describe_owner_dir(dst)) {
                Ok(Some(page)) => sle.set_field_u64(sf("sfDestinationNode"), page),
                Ok(None) => return Ter::TEC_DIR_FULL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
            if let Some(sponsor) = reserve_sponsor.as_ref() {
                sle.set_account_id(sf("sfSponsor"), sponsor.get_account_id(sf("sfAccount")));
            }
            if view.insert(Arc::new(sle)).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }

            let bal = src_sle.get_field_amount(sf("sfBalance")).xrp().drops();
            let Some(new_balance) = bal.checked_sub(amount.xrp().drops()) else {
                return Ter::TEF_BAD_LEDGER;
            };
            let mut obj = src_sle.clone_as_object();
            obj.set_field_amount(
                sf("sfBalance"),
                STAmount::from_xrp_amount(XRPAmount::from_drops(new_balance)),
            );
            if view
                .update(Arc::new(STLedgerEntry::from_stobject(obj, *src_sle.key())))
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            let updated_src = match view.peek(src_keylet) {
                Ok(Some(src_sle)) => src_sle,
                _ => return Ter::TEF_BAD_LEDGER,
            };
            if ledger::increase_owner_count_for_object(view, &updated_src, reserve_sponsor.as_ref())
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }
        TxType::PAYCHAN_FUND => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let channel_id = sttx.get_field_h256(sf("sfChannel"));
            let amount = sttx.get_field_amount(sf("sfAmount"));
            let chan_keylet = protocol::pay_channel_keylet_from_key(channel_id);
            let chan = match view.peek(chan_keylet) {
                Ok(Some(chan)) => chan,
                Ok(None) => return Ter::TEC_NO_ENTRY,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };

            let current_expiration = chan
                .is_field_present(sf("sfExpiration"))
                .then(|| chan.get_field_u32(sf("sfExpiration")));
            let cancel_after = chan
                .is_field_present(sf("sfCancelAfter"))
                .then(|| chan.get_field_u32(sf("sfCancelAfter")));
            if cancel_after.is_some_and(|expiration| paychan_is_expired(view, expiration))
                || current_expiration.is_some_and(|expiration| paychan_is_expired(view, expiration))
            {
                return close_channel(view, &chan, chan_keylet.key);
            }

            // Only the channel source can fund it
            let chan_src = chan.get_account_id(sf("sfAccount"));
            if chan_src != account {
                return Ter::TEC_NO_PERMISSION;
            }

            let new_expiration = sttx
                .is_field_present(sf("sfExpiration"))
                .then(|| sttx.get_field_u32(sf("sfExpiration")));
            if let Some(new_expiration) = new_expiration {
                let mut minimum = paychan_saturating_add(
                    view,
                    view.header().parent_close_time,
                    chan.get_field_u32(sf("sfSettleDelay")),
                );
                if let Some(current) = current_expiration
                    && current < minimum
                {
                    minimum = current;
                }
                if new_expiration < minimum {
                    return if view
                        .rules()
                        .enabled(&protocol::feature_id("fixCleanup3_2_0"))
                    {
                        Ter::TEC_NO_PERMISSION
                    } else {
                        Ter::TEM_BAD_EXPIRATION
                    };
                }
            }

            let src_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
            let src_sle = match view.peek(src_keylet) {
                Ok(Some(src_sle)) => src_sle,
                Ok(None) => return Ter::TEF_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let balance = src_sle.get_field_amount(sf("sfBalance")).xrp().drops();
            let reserve_sponsor = match check_cash_reserve_sponsor(view, sttx) {
                Ok(sponsor) => sponsor,
                Err(result) => return result,
            };
            let reserve_bearer = reserve_sponsor.as_deref().unwrap_or(src_sle.as_ref());
            let reserve_bearer_balance = reserve_bearer
                .get_field_amount(sf("sfBalance"))
                .xrp()
                .drops();
            let reserve_bearer_requirement =
                ledger::effective_account_reserve(view.fees(), reserve_bearer, 0, 0) as i64;
            if reserve_bearer_balance < reserve_bearer_requirement {
                return Ter::TEC_INSUFFICIENT_RESERVE;
            }
            let source_reserve =
                ledger::effective_account_reserve(view.fees(), &src_sle, 0, 0) as i64;
            let required = source_reserve.saturating_add(amount.xrp().drops());
            if balance < required {
                return Ter::TEC_UNFUNDED;
            }

            let destination = chan.get_account_id(sf("sfDestination"));
            match view.read(protocol::account_keylet(Uint160::from_void(
                destination.data(),
            ))) {
                Ok(Some(_)) => {}
                Ok(None) => return Ter::TEC_NO_DST,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }

            let mut chan_obj = chan.clone_as_object();
            if let Some(expiration) = new_expiration {
                chan_obj.set_field_u32(sf("sfExpiration"), expiration);
            }
            chan_obj.set_field_amount(
                sf("sfAmount"),
                chan.get_field_amount(sf("sfAmount")) + amount.clone(),
            );
            if view
                .update(Arc::new(STLedgerEntry::from_stobject(
                    chan_obj,
                    *chan.key(),
                )))
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }

            let mut src_obj = src_sle.clone_as_object();
            src_obj.set_field_amount(
                sf("sfBalance"),
                STAmount::from_xrp_amount(XRPAmount::from_drops(balance - amount.xrp().drops())),
            );
            if view
                .update(Arc::new(STLedgerEntry::from_stobject(
                    src_obj,
                    *src_sle.key(),
                )))
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }
        TxType::PAYCHAN_CLAIM => {
            let channel_id = sttx.get_field_h256(sf("sfChannel"));
            let chan_keylet = protocol::pay_channel_keylet_from_key(channel_id);
            let chan = match view.peek(chan_keylet) {
                Ok(Some(chan)) => chan,
                Ok(None) => return Ter::TEC_NO_TARGET,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };

            let src = chan.get_account_id(sf("sfAccount"));
            let dst = chan.get_account_id(sf("sfDestination"));
            let tx_account = sttx.get_account_id(sf("sfAccount"));
            let tx_flags = sttx.get_field_u32(sf("sfFlags"));
            let current_expiration = chan
                .is_field_present(sf("sfExpiration"))
                .then(|| chan.get_field_u32(sf("sfExpiration")));

            let close_time = view.header().parent_close_time;
            if (chan.is_field_present(sf("sfCancelAfter"))
                && paychan_is_expired(view, chan.get_field_u32(sf("sfCancelAfter"))))
                || (chan.is_field_present(sf("sfExpiration"))
                    && paychan_is_expired(view, chan.get_field_u32(sf("sfExpiration"))))
            {
                return close_channel(view, &chan, chan_keylet.key);
            }

            // reference: permission check
            if tx_account != src && tx_account != dst {
                return Ter::TEC_NO_PERMISSION;
            }

            if sttx.is_field_present(sf("sfBalance")) {
                if tx_account == dst && !sttx.is_field_present(sf("sfSignature")) {
                    return if view
                        .rules()
                        .enabled(&protocol::feature_id("fixCleanup3_2_0"))
                    {
                        Ter::TEC_NO_PERMISSION
                    } else {
                        Ter::TEM_BAD_SIGNATURE
                    };
                }
                if sttx.is_field_present(sf("sfSignature"))
                    && sttx.get_field_vl(sf("sfPublicKey")) != chan.get_field_vl(sf("sfPublicKey"))
                {
                    return if view
                        .rules()
                        .enabled(&protocol::feature_id("fixCleanup3_2_0"))
                    {
                        Ter::TEC_NO_PERMISSION
                    } else {
                        Ter::TEM_BAD_SIGNER
                    };
                }

                let chan_balance = chan.get_field_amount(sf("sfBalance")).xrp().drops();
                let chan_funds = chan.get_field_amount(sf("sfAmount")).xrp().drops();
                let req_balance = sttx.get_field_amount(sf("sfBalance")).xrp().drops();

                if req_balance > chan_funds || req_balance <= chan_balance {
                    return Ter::TEC_UNFUNDED_PAYMENT;
                }

                let delta = req_balance - chan_balance;

                let dst_keylet = protocol::account_keylet(Uint160::from_void(dst.data()));
                let dst_sle = match view.peek(dst_keylet) {
                    Ok(Some(dst_sle)) => dst_sle,
                    Ok(None) => return Ter::TEC_NO_DST,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let auth = match ledger::credential_helpers::verify_deposit_preauth(
                    sttx,
                    view,
                    &tx_account,
                    &dst,
                    Some(&dst_sle),
                ) {
                    Ok(result) => result,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                if !is_tes_success(auth) {
                    return auth;
                }

                let mut obj = chan.clone_as_object();
                obj.set_field_amount(sf("sfBalance"), sttx.get_field_amount(sf("sfBalance")));
                if view
                    .update(Arc::new(STLedgerEntry::from_stobject(obj, *chan.key())))
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
                let dst_bal = dst_sle.get_field_amount(sf("sfBalance")).xrp().drops();
                let Some(new_dst_balance) = dst_bal.checked_add(delta) else {
                    return Ter::TEF_BAD_LEDGER;
                };
                let mut dst_obj = dst_sle.clone_as_object();
                dst_obj.set_field_amount(
                    sf("sfBalance"),
                    STAmount::from_xrp_amount(XRPAmount::from_drops(new_dst_balance)),
                );
                if view
                    .update(Arc::new(STLedgerEntry::from_stobject(
                        dst_obj,
                        *dst_sle.key(),
                    )))
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
            }

            // reference: tfRenew — clear expiration (only source can renew)
            if (tx_flags & 0x0001_0000) != 0 {
                if src != tx_account {
                    return Ter::TEC_NO_PERMISSION;
                }
                let cur = match view.peek(chan_keylet) {
                    Ok(Some(cur)) => cur,
                    _ => return Ter::TEF_BAD_LEDGER,
                };
                let mut obj = cur.clone_as_object();
                obj.make_field_absent(sf("sfExpiration"));
                if view
                    .update(Arc::new(STLedgerEntry::from_stobject(obj, chan_keylet.key)))
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
            }

            // reference: tfClose — close channel or set expiration
            if (tx_flags & 0x0002_0000) != 0 {
                match view.peek(chan_keylet) {
                    Ok(Some(cur)) => {
                        let cur_balance = cur.get_field_amount(sf("sfBalance")).xrp().drops();
                        let cur_amount = cur.get_field_amount(sf("sfAmount")).xrp().drops();

                        if dst == tx_account || cur_balance == cur_amount {
                            return close_channel(view, &cur, chan_keylet.key);
                        }

                        let settle_expiration = paychan_saturating_add(
                            view,
                            close_time,
                            cur.get_field_u32(sf("sfSettleDelay")),
                        );

                        let should_update = current_expiration
                            .is_none_or(|expiration| expiration > settle_expiration);

                        if should_update {
                            let mut obj = cur.clone_as_object();
                            obj.set_field_u32(sf("sfExpiration"), settle_expiration);
                            if view
                                .update(Arc::new(STLedgerEntry::from_stobject(
                                    obj,
                                    chan_keylet.key,
                                )))
                                .is_err()
                            {
                                return Ter::TEF_BAD_LEDGER;
                            }
                        }
                    }
                    _ => return Ter::TEF_BAD_LEDGER,
                }
            }

            Ter::TES_SUCCESS
        }

        // --- AMM ---
        TxType::AMM_CREATE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let amount1 = sttx.get_field_amount(sf("sfAmount"));
            let amount2 = sttx.get_field_amount(sf("sfAmount2"));
            // AMMCreate::preflight and AMMCreate::preclaim have already run
            // against the immutable, pre-fee ledger.  rippled's doApply does
            // not repeat those decisions: it enters applyCreate directly.
            // In particular, rechecking XRP liquidity here observes the
            // post-fee balance and can turn a canonical tesSUCCESS into
            // tecUNFUNDED_AMM at the exact reserve boundary.
            let facts = AMMCreateApplyFacts {
                amount1: amount1.clone(),
                amount2: amount2.clone(),
                trading_fee: sttx.get_field_u16(sf("sfTradingFee")),
                account,
                amm_account: account,
            };
            let mut sink = ViewBackedAMMCreateSink {
                view,
                account,
                amount1,
                amount2,
                trading_fee: facts.trading_fee,
                amm_keylet: None,
                amm_account: None,
                lp_tokens: None,
            };
            run_amm_create_do_apply(facts, &mut sink)
        }
        TxType::AMM_DEPOSIT => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let asset1 = tx_amm_asset(sttx, sf("sfAsset"));
            let asset2 = tx_amm_asset(sttx, sf("sfAsset2"));
            let amount = optional_tx_amount(sttx, sf("sfAmount"));
            let amount2 = optional_tx_amount(sttx, sf("sfAmount2"));
            let e_price = optional_tx_amount(sttx, sf("sfEPrice"));
            let lp_token_out = optional_tx_amount(sttx, sf("sfLPTokenOut"));
            let mut gated_assets = vec![asset1, asset2];
            if let Some(amount) = &amount {
                gated_assets.push(amount.asset());
            }
            if let Some(amount2) = &amount2 {
                gated_assets.push(amount2.asset());
            }
            let mpt_gate = check_amm_mptokens_v2_gate(view, &gated_assets);
            if mpt_gate != Ter::TES_SUCCESS {
                return mpt_gate;
            }
            let mpt_result = check_mpt_amm_asset_allowed(view, &account, asset1, false);
            if mpt_result != Ter::TES_SUCCESS {
                return mpt_result;
            }
            let mpt_result = check_mpt_amm_asset_allowed(view, &account, asset2, false);
            if mpt_result != Ter::TES_SUCCESS {
                return mpt_result;
            }
            let amm_keylet = protocol::keylet::amm(asset1, asset2);
            let amm_sle = match view.peek(amm_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TER_NO_AMM,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            {
                let amm_account = amm_sle.get_account_id(sf("sfAccount"));
                let mpt_result = check_mpt_amm_pool_asset_unlocked(view, &amm_account, asset1);
                if mpt_result != Ter::TES_SUCCESS {
                    return mpt_result;
                }
                let mpt_result = check_mpt_amm_pool_asset_unlocked(view, &amm_account, asset2);
                if mpt_result != Ter::TES_SUCCESS {
                    return mpt_result;
                }
                let flags = sttx.get_flags();
                if let Some(amount) = &amount {
                    let mpt_result =
                        check_mpt_amm_pool_asset_unlocked(view, &amm_account, amount.asset());
                    if mpt_result != Ter::TES_SUCCESS {
                        return mpt_result;
                    }
                    let mpt_result =
                        check_mpt_amm_asset_allowed(view, &account, amount.asset(), true);
                    if mpt_result != Ter::TES_SUCCESS {
                        return mpt_result;
                    }
                }
                if let Some(amount2) = &amount2 {
                    let mpt_result =
                        check_mpt_amm_pool_asset_unlocked(view, &amm_account, amount2.asset());
                    if mpt_result != Ter::TES_SUCCESS {
                        return mpt_result;
                    }
                    let mpt_result =
                        check_mpt_amm_asset_allowed(view, &account, amount2.asset(), true);
                    if mpt_result != Ter::TES_SUCCESS {
                        return mpt_result;
                    }
                }
                let lp_tokens = amm_sle.get_field_amount(sf("sfLPTokenBalance"));
                let lp_issue = lp_tokens.issue();
                let pool_asset1 = amount.as_ref().map(STAmount::asset).unwrap_or(asset1);
                let pool_asset2 = amount2.as_ref().map(STAmount::asset).unwrap_or(asset2);
                let pool1 = amm_holds_or_return!(view, &amm_account, pool_asset1, sf("sfAmount"));
                let pool2 = amm_holds_or_return!(view, &amm_account, pool_asset2, sf("sfAmount2"));
                let trading_fee = if lp_tokens.signum() == 0 {
                    if sttx.is_field_present(sf("sfTradingFee")) {
                        sttx.get_field_u16(sf("sfTradingFee"))
                    } else {
                        0
                    }
                } else {
                    // Match rippled's getTradingFee(): an active auction-slot
                    // owner (or authorized account) pays sfDiscountedFee.
                    ledger::amm_utils::get_trading_fee(view, &amm_sle, account)
                };
                let math_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    tx::run_amm_deposit_apply_math_facts(&tx::AMMDepositApplyMathFacts {
                        amount1: amount,
                        amount2,
                        e_price,
                        lp_token_out,
                        pool_amount1: pool1,
                        pool_amount2: pool2,
                        lp_token_balance: lp_tokens,
                        trading_fee,
                        rules: view.rules(),
                        flags,
                    })
                }));
                let math = match math_result {
                    Ok(Ok(math)) => math,
                    Ok(Err(ter)) => return ter,
                    Err(_) => return amm_math_panic_ter(&view.rules()),
                };

                // AMMDeposit is intentionally different from AMMCreate here.
                // rippled recalculates the actual deposit in doApply and then
                // checks native liquidity on the post-fee view, adjusting for
                // the LP trust line that this deposit may create.
                let has_lp_line =
                    match view.read(protocol::line(account, amm_account, lp_issue.currency)) {
                        Ok(line) => line.is_some(),
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    };
                for deposit in [math.amount1.as_ref(), math.amount2.as_ref()]
                    .into_iter()
                    .flatten()
                {
                    if deposit.native() {
                        let liquid = match ledger::apply_view::xrp_liquid(
                            view,
                            &account,
                            i32::from(!has_lp_line),
                        ) {
                            Ok(liquid) => liquid,
                            Err(_) => return Ter::TEF_BAD_LEDGER,
                        };
                        if liquid < deposit.xrp() {
                            return Ter::TEC_UNFUNDED_AMM;
                        }
                    }
                }

                if let Some(amount) = &math.amount1 {
                    let mpt_result =
                        check_mpt_amm_pool_asset_unlocked(view, &amm_account, amount.asset());
                    if mpt_result != Ter::TES_SUCCESS {
                        return mpt_result;
                    }
                    let mpt_result =
                        check_mpt_amm_asset_allowed(view, &account, amount.asset(), true);
                    if mpt_result != Ter::TES_SUCCESS {
                        return mpt_result;
                    }
                    let deposit_result = amm_deposit_asset(view, &account, &amm_account, amount);
                    if deposit_result != Ter::TES_SUCCESS {
                        return deposit_result;
                    }
                }
                if let Some(amount2) = &math.amount2 {
                    let mpt_result =
                        check_mpt_amm_pool_asset_unlocked(view, &amm_account, amount2.asset());
                    if mpt_result != Ter::TES_SUCCESS {
                        return mpt_result;
                    }
                    let mpt_result =
                        check_mpt_amm_asset_allowed(view, &account, amount2.asset(), true);
                    if mpt_result != Ter::TES_SUCCESS {
                        return mpt_result;
                    }
                    let deposit2_result = amm_deposit_asset(view, &account, &amm_account, amount2);
                    if deposit2_result != Ter::TES_SUCCESS {
                        return deposit2_result;
                    }
                }

                let lp_result = ledger::ripple_state_helpers::direct_send_no_fee_iou_pub(
                    view,
                    &amm_account,
                    &account,
                    &math.lp_tokens,
                );
                if lp_result != Ter::TES_SUCCESS {
                    return lp_result;
                }

                if view
                    .rules()
                    .enabled(&protocol::feature_id("fixCleanup3_3_0"))
                    && view.rules().enabled(&protocol::feature_id("fixAMMv1_3"))
                {
                    let remaining1 =
                        amm_holds_or_return!(view, &amm_account, asset1, sf("sfAmount"));
                    let remaining2 =
                        amm_holds_or_return!(view, &amm_account, asset2, sf("sfAmount2"));
                    let precision = ledger::check_amm_precision_loss(
                        &remaining1,
                        &remaining2,
                        &math.new_lp_token_balance,
                    );
                    if precision != Ter::TES_SUCCESS {
                        return precision;
                    }
                }

                let mut obj = amm_sle.clone_as_object();
                obj.set_field_amount(sf("sfLPTokenBalance"), math.new_lp_token_balance.clone());
                if math.empty_pool_reinit {
                    // Match `initializeFeeAuctionVote`: reviving an empty AMM
                    // installs the depositor as its sole voter and free-slot
                    // owner, and resets every fee/auction field.
                    let mut vote_slots = STArray::new(sf("sfVoteSlots"));
                    let mut vote = STObject::make_inner_object(sf("sfVoteEntry"));
                    if trading_fee != 0 {
                        vote.set_field_u16(sf("sfTradingFee"), trading_fee);
                    }
                    vote.set_field_u32(sf("sfVoteWeight"), VOTE_WEIGHT_SCALE_FACTOR);
                    vote.set_account_id(sf("sfAccount"), account);
                    vote_slots.push_back(vote);
                    obj.set_field_array(sf("sfVoteSlots"), vote_slots);

                    let mut auction_slot = if obj.is_field_present(sf("sfAuctionSlot")) {
                        obj.peek_field_object(sf("sfAuctionSlot")).clone()
                    } else {
                        STObject::make_inner_object(sf("sfAuctionSlot"))
                    };
                    auction_slot.set_account_id(sf("sfAccount"), account);
                    auction_slot.set_field_u32(
                        sf("sfExpiration"),
                        view.header()
                            .parent_close_time
                            .saturating_add(protocol::TOTAL_TIME_SLOT_SECS),
                    );
                    auction_slot
                        .set_field_amount(sf("sfPrice"), math.new_lp_token_balance.zeroed());
                    if trading_fee != 0 {
                        obj.set_field_u16(sf("sfTradingFee"), trading_fee);
                    } else if obj.is_field_present(sf("sfTradingFee")) {
                        obj.make_field_absent(sf("sfTradingFee"));
                    }
                    let discounted_fee =
                        trading_fee / protocol::AUCTION_SLOT_DISCOUNTED_FEE_FRACTION as u16;
                    if discounted_fee != 0 {
                        auction_slot.set_field_u16(sf("sfDiscountedFee"), discounted_fee);
                    } else if auction_slot.is_field_present(sf("sfDiscountedFee")) {
                        auction_slot.make_field_absent(sf("sfDiscountedFee"));
                    }
                    if view
                        .rules()
                        .enabled(&protocol::feature_id("fixCleanup3_2_0"))
                        && auction_slot.is_field_present(sf("sfAuthAccounts"))
                    {
                        auction_slot.make_field_absent(sf("sfAuthAccounts"));
                    }
                    obj.set_field_object(sf("sfAuctionSlot"), auction_slot);
                }
                if view
                    .update(Arc::new(STLedgerEntry::from_stobject(obj, *amm_sle.key())))
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
            }
            Ter::TES_SUCCESS
        }
        TxType::AMM_WITHDRAW => {
            let pre_fee_balance_drops = match require_pre_fee_balance(pre_fee_balance_drops) {
                Ok(balance) => balance,
                Err(ter) => return ter,
            };
            let prior_balance = XRPAmount::from_drops(pre_fee_balance_drops);
            let account = sttx.get_account_id(sf("sfAccount"));
            let asset1 = tx_amm_asset(sttx, sf("sfAsset"));
            let asset2 = tx_amm_asset(sttx, sf("sfAsset2"));
            let amount = optional_tx_amount(sttx, sf("sfAmount"));
            let amount2 = optional_tx_amount(sttx, sf("sfAmount2"));
            let e_price = optional_tx_amount(sttx, sf("sfEPrice"));
            let lp_token_in = optional_tx_amount(sttx, sf("sfLPTokenIn"));
            let mut gated_assets = vec![asset1, asset2];
            if let Some(amount) = &amount {
                gated_assets.push(amount.asset());
            }
            if let Some(amount2) = &amount2 {
                gated_assets.push(amount2.asset());
            }
            let mpt_gate = check_amm_mptokens_v2_gate(view, &gated_assets);
            if mpt_gate != Ter::TES_SUCCESS {
                return mpt_gate;
            }
            let mpt_result = check_mpt_amm_withdraw_asset_allowed(view, &account, asset1);
            if mpt_result != Ter::TES_SUCCESS {
                return mpt_result;
            }
            let mpt_result = check_mpt_amm_withdraw_asset_allowed(view, &account, asset2);
            if mpt_result != Ter::TES_SUCCESS {
                return mpt_result;
            }
            let amm_keylet = protocol::keylet::amm(asset1, asset2);
            let mut amm_sle = match view.peek(amm_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TER_NO_AMM,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            {
                let amm_account = amm_sle.get_account_id(sf("sfAccount"));
                let mpt_result = check_mpt_amm_pool_asset_unlocked(view, &amm_account, asset1);
                if mpt_result != Ter::TES_SUCCESS {
                    return mpt_result;
                }
                let mpt_result = check_mpt_amm_pool_asset_unlocked(view, &amm_account, asset2);
                if mpt_result != Ter::TES_SUCCESS {
                    return mpt_result;
                }
                let mut lp_total = amm_sle.get_field_amount(sf("sfLPTokenBalance"));
                let account_lp_tokens = match amm_lp_holds_in_view(view, &amm_sle, account) {
                    Ok(Some(amount)) => amount,
                    Ok(None) => return Ter::TEC_AMM_BALANCE,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                if view.rules().enabled(&protocol::feature_id("fixAMMv1_1")) {
                    if let Err(ter) = ledger::verify_and_adjust_lp_token_balance(
                        view,
                        &account_lp_tokens,
                        &mut amm_sle,
                        account,
                    ) {
                        return ter;
                    }
                    lp_total = amm_sle.get_field_amount(sf("sfLPTokenBalance"));
                }
                let lp_issue = lp_total.issue();
                let trading_fee = ledger::get_trading_fee(view, &amm_sle, account);
                let pool_asset1 = amount.as_ref().map(STAmount::asset).unwrap_or(asset1);
                let pool_asset2 = amount2.as_ref().map(STAmount::asset).unwrap_or(asset2);
                let pool1 = amm_holds_or_return!(view, &amm_account, pool_asset1, sf("sfAmount"));
                let pool2 = amm_holds_or_return!(view, &amm_account, pool_asset2, sf("sfAmount2"));
                let math_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    tx::run_amm_withdraw_apply_math_facts(&tx::AMMWithdrawApplyMathFacts {
                        amount1: amount,
                        amount2,
                        e_price,
                        lp_token_in,
                        pool_amount1: pool1,
                        pool_amount2: pool2,
                        lp_token_balance: lp_total,
                        account_lp_tokens,
                        trading_fee,
                        rules: view.rules(),
                        flags: sttx.get_flags(),
                    })
                }));
                let math = match math_result {
                    Ok(Ok(math)) => math,
                    Ok(Err(ter)) => return ter,
                    Err(_) => return amm_math_panic_ter(&view.rules()),
                };

                if let Some(amount) = &math.amount1 {
                    let holding_result = amm_prepare_withdraw_holding(
                        view,
                        sttx,
                        &account,
                        amount.asset(),
                        prior_balance,
                        None,
                    );
                    if holding_result != Ter::TES_SUCCESS {
                        return holding_result;
                    }
                    let withdraw_result = amm_withdraw_asset(view, &amm_account, &account, amount);
                    if withdraw_result != Ter::TES_SUCCESS {
                        return withdraw_result;
                    }
                }
                if let Some(amount2) = &math.amount2 {
                    let holding_result = amm_prepare_withdraw_holding(
                        view,
                        sttx,
                        &account,
                        amount2.asset(),
                        prior_balance,
                        None,
                    );
                    if holding_result != Ter::TES_SUCCESS {
                        return holding_result;
                    }
                    let withdraw2_result =
                        amm_withdraw_asset(view, &amm_account, &account, amount2);
                    if withdraw2_result != Ter::TES_SUCCESS {
                        return withdraw2_result;
                    }
                }
                let burn_result = crate::state::amm_bid_apply::redeem_iou_pub(
                    view,
                    &account,
                    &math.lp_tokens,
                    &lp_issue,
                );
                if burn_result != Ter::TES_SUCCESS {
                    return burn_result;
                }
                if view
                    .rules()
                    .enabled(&protocol::feature_id("fixCleanup3_3_0"))
                    && view.rules().enabled(&protocol::feature_id("fixAMMv1_3"))
                {
                    let remaining1 =
                        amm_holds_or_return!(view, &amm_account, asset1, sf("sfAmount"));
                    let remaining2 =
                        amm_holds_or_return!(view, &amm_account, asset2, sf("sfAmount2"));
                    let precision = ledger::check_amm_precision_loss(
                        &remaining1,
                        &remaining2,
                        &math.new_lp_token_balance,
                    );
                    if precision != Ter::TES_SUCCESS {
                        return precision;
                    }
                }
                if math.new_lp_token_balance.signum() == 0 {
                    let delete_result = delete_amm_account(view, &amm_sle);
                    if delete_result == Ter::TES_SUCCESS {
                        return Ter::TES_SUCCESS;
                    }
                    if delete_result != Ter::TEC_INCOMPLETE {
                        return delete_result;
                    }
                }
                let mut obj = amm_sle.clone_as_object();
                obj.set_field_amount(sf("sfLPTokenBalance"), math.new_lp_token_balance.clone());
                if view
                    .update(Arc::new(STLedgerEntry::from_stobject(obj, *amm_sle.key())))
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
            }
            Ter::TES_SUCCESS
        }
        TxType::AMM_VOTE => {
            let asset1 = sttx.get_field_issue(sf("sfAsset")).asset();
            let asset2 = sttx.get_field_issue(sf("sfAsset2")).asset();
            let mpt_gate = check_amm_mptokens_v2_gate(view, &[asset1, asset2]);
            if mpt_gate != Ter::TES_SUCCESS {
                return mpt_gate;
            }
            let fee_vote = sttx.get_field_u16(sf("sfTradingFee"));
            let account = sttx.get_account_id(sf("sfAccount"));
            let amm_keylet = protocol::keylet::amm(asset1, asset2);
            let amm_sle = match view.peek(amm_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TER_NO_AMM,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let lp_amm_balance = amm_sle.get_field_amount(sf("sfLPTokenBalance"));
            if lp_amm_balance.signum() == 0 {
                return Ter::TEC_AMM_EMPTY;
            }
            let lp_tokens_new = match amm_lp_holds_in_view(view, &amm_sle, account) {
                Ok(Some(tokens)) => tokens,
                Ok(None) => return Ter::TEC_AMM_INVALID_TOKENS,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if lp_tokens_new.signum() == 0 {
                return Ter::TEC_AMM_INVALID_TOKENS;
            }

            let lp_total = ledger::amm_helpers::stamount_as_number(&lp_amm_balance);
            let lp_tokens_new_num = ledger::amm_helpers::stamount_as_number(&lp_tokens_new);
            let mut updated_vote_slots = STArray::new(sf("sfVoteSlots"));
            let mut numerator = RuntimeNumber::zero();
            let mut denominator = RuntimeNumber::zero();
            let mut found_account = false;
            let mut min_tokens: Option<RuntimeNumber> = None;
            let mut min_pos = 0usize;
            let mut min_account = AccountID::from_array([0; 20]);
            let mut min_fee = 0u32;

            let existing_slots = if amm_sle.is_field_present(sf("sfVoteSlots")) {
                amm_sle.get_field_array(sf("sfVoteSlots"))
            } else {
                STArray::new(sf("sfVoteSlots"))
            };

            for entry in existing_slots.iter() {
                let entry_account = entry.get_account_id(sf("sfAccount"));
                let mut lp_tokens = match amm_lp_holds_in_view(view, &amm_sle, entry_account) {
                    Ok(Some(tokens)) => tokens,
                    Ok(None) => continue,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                if lp_tokens.signum() == 0 {
                    continue;
                }
                let mut fee_val = u32::from(entry.get_field_u16(sf("sfTradingFee")));
                if entry_account == account {
                    lp_tokens = lp_tokens_new.clone();
                    fee_val = u32::from(fee_vote);
                    found_account = true;
                }
                let lp_tokens_num = ledger::amm_helpers::stamount_as_number(&lp_tokens);
                numerator += number_from_i64(fee_val as i64) * lp_tokens_num;
                denominator += lp_tokens_num;

                let vote_weight =
                    ((lp_tokens_num * number_from_i64(VOTE_WEIGHT_SCALE_FACTOR as i64)) / lp_total)
                        .try_to_i64()
                        .unwrap_or(0)
                        .max(0) as u32;

                let mut new_entry = STObject::make_inner_object(sf("sfVoteEntry"));
                new_entry.set_account_id(sf("sfAccount"), entry_account);
                if fee_val != 0 {
                    new_entry.set_field_u16(sf("sfTradingFee"), fee_val as u16);
                }
                new_entry.set_field_u32(sf("sfVoteWeight"), vote_weight);

                let is_new_minimum = min_tokens.is_none_or(|minimum| {
                    lp_tokens_num < minimum
                        || (lp_tokens_num == minimum
                            && (fee_val < min_fee
                                || (fee_val == min_fee && entry_account < min_account)))
                });
                if is_new_minimum {
                    min_tokens = Some(lp_tokens_num);
                    min_pos = updated_vote_slots.len();
                    min_account = entry_account;
                    min_fee = fee_val;
                }

                updated_vote_slots.push_back(new_entry);
            }

            if !found_account {
                let update_entry = |slots: &mut STArray, replace_pos: Option<usize>| {
                    let vote_weight = ((lp_tokens_new_num
                        * number_from_i64(VOTE_WEIGHT_SCALE_FACTOR as i64))
                        / lp_total)
                        .try_to_i64()
                        .unwrap_or(0)
                        .max(0) as u32;
                    let mut new_entry = STObject::make_inner_object(sf("sfVoteEntry"));
                    if fee_vote != 0 {
                        new_entry.set_field_u16(sf("sfTradingFee"), fee_vote);
                    }
                    new_entry.set_field_u32(sf("sfVoteWeight"), vote_weight);
                    new_entry.set_account_id(sf("sfAccount"), account);
                    if let Some(pos) = replace_pos {
                        if let Some(slot) = slots.get_mut(pos) {
                            *slot = new_entry;
                        }
                    } else {
                        slots.push_back(new_entry);
                    }
                };

                if updated_vote_slots.len() < usize::from(VOTE_MAX_SLOTS) {
                    numerator += number_from_i64(i64::from(fee_vote)) * lp_tokens_new_num;
                    denominator += lp_tokens_new_num;
                    update_entry(&mut updated_vote_slots, None);
                } else if let Some(min_tokens) = min_tokens
                    && (lp_tokens_new_num > min_tokens
                        || (lp_tokens_new_num == min_tokens && u32::from(fee_vote) > min_fee))
                {
                    let Some(replaced) = updated_vote_slots.get(min_pos).cloned() else {
                        return Ter::TEF_INTERNAL;
                    };
                    let replaced_fee =
                        u32::from(if replaced.is_field_present(sf("sfTradingFee")) {
                            replaced.get_field_u16(sf("sfTradingFee"))
                        } else {
                            0
                        });
                    numerator = numerator - number_from_i64(replaced_fee as i64) * min_tokens
                        + number_from_i64(i64::from(fee_vote)) * lp_tokens_new_num;
                    denominator = denominator - min_tokens + lp_tokens_new_num;
                    update_entry(&mut updated_vote_slots, Some(min_pos));
                }
            }

            let mut obj = amm_sle.clone_as_object();
            obj.set_field_array(sf("sfVoteSlots"), updated_vote_slots);
            if denominator.signum() != 0 {
                let fee = (numerator / denominator).try_to_i64().unwrap_or(0).max(0) as u16;
                if fee != 0 {
                    obj.set_field_u16(sf("sfTradingFee"), fee);
                } else if obj.is_field_present(sf("sfTradingFee")) {
                    obj.make_field_absent(sf("sfTradingFee"));
                }
                if obj.is_field_present(sf("sfAuctionSlot")) {
                    let mut auction_slot = obj.peek_field_object(sf("sfAuctionSlot")).clone();
                    let discounted_fee = fee / AUCTION_SLOT_DISCOUNTED_FEE_FRACTION as u16;
                    if discounted_fee != 0 {
                        auction_slot.set_field_u16(sf("sfDiscountedFee"), discounted_fee);
                    } else if auction_slot.is_field_present(sf("sfDiscountedFee")) {
                        auction_slot.make_field_absent(sf("sfDiscountedFee"));
                    }
                    obj.set_field_object(sf("sfAuctionSlot"), auction_slot);
                }
            } else {
                if obj.is_field_present(sf("sfTradingFee")) {
                    obj.make_field_absent(sf("sfTradingFee"));
                }
                if obj.is_field_present(sf("sfAuctionSlot")) {
                    let mut auction_slot = obj.peek_field_object(sf("sfAuctionSlot")).clone();
                    if auction_slot.is_field_present(sf("sfDiscountedFee")) {
                        auction_slot.make_field_absent(sf("sfDiscountedFee"));
                    }
                    obj.set_field_object(sf("sfAuctionSlot"), auction_slot);
                }
            }
            if view
                .update(Arc::new(STLedgerEntry::from_stobject(obj, *amm_sle.key())))
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }
        TxType::AMM_DELETE => {
            let asset1 = sttx.get_field_issue(sf("sfAsset")).asset();
            let asset2 = sttx.get_field_issue(sf("sfAsset2")).asset();
            let mpt_gate = check_amm_mptokens_v2_gate(view, &[asset1, asset2]);
            if mpt_gate != Ter::TES_SUCCESS {
                return mpt_gate;
            }
            let amm_keylet = protocol::keylet::amm(asset1, asset2);
            let amm_sle = match view.peek(amm_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TER_NO_AMM,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let lp_balance = amm_sle.get_field_amount(sf("sfLPTokenBalance"));
            if lp_balance.signum() != 0 {
                return Ter::TEC_AMM_NOT_EMPTY;
            }
            delete_amm_account(view, &amm_sle)
        }

        // --- NFTs ---
        TxType::NFTOKEN_MINT => {
            let account = sttx.get_account_id(sf("sfAccount"));
            // Determine the actual issuer (sfIssuer if present, otherwise minting account)
            let issuer = if sttx.is_field_present(sf("sfIssuer")) {
                sttx.get_account_id(sf("sfIssuer"))
            } else {
                account
            };

            // Get or create the issuer's MintedNFTokens counter
            let issuer_keylet = protocol::account_keylet(Uint160::from_void(issuer.data()));
            let issuer_sle = match view.peek(issuer_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TEC_NO_ISSUER,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };

            let mut issuer_obj = issuer_sle.clone_as_object();

            // Set FirstNFTokenSequence if not present
            if !issuer_obj.is_field_present(sf("sfFirstNFTokenSequence")) {
                let acct_seq = issuer_obj.get_field_u32(sf("sfSequence"));
                // If minted by owner using sequence (not ticket, not authorized minter):
                // Sequence was already incremented by apply_submit_transactor_shell,
                // so use acct_seq - 1. Otherwise use acct_seq as-is.
                let first_seq =
                    if !sttx.is_field_present(sf("sfIssuer")) && sttx.get_seq_proxy().is_seq() {
                        acct_seq.saturating_sub(1)
                    } else {
                        acct_seq
                    };
                issuer_obj.set_field_u32(sf("sfFirstNFTokenSequence"), first_seq);
            }

            // Get current MintedNFTokens and increment.  rippled rejects both
            // the counter overflow and any overflow in the derived token
            // sequence instead of saturating or wrapping either value.
            let minted_count = if issuer_obj.is_field_present(sf("sfMintedNFTokens")) {
                issuer_obj.get_field_u32(sf("sfMintedNFTokens"))
            } else {
                0
            };
            let Some(next_minted_count) = minted_count.checked_add(1) else {
                return Ter::TEC_MAX_SEQUENCE_REACHED;
            };

            // Compute token sequence = FirstNFTokenSequence + MintedNFTokens (before increment)
            let first_nft_seq = issuer_obj.get_field_u32(sf("sfFirstNFTokenSequence"));
            let Some(token_seq) = first_nft_seq.checked_add(minted_count) else {
                return Ter::TEC_MAX_SEQUENCE_REACHED;
            };
            if token_seq.checked_add(1).is_none() {
                return Ter::TEC_MAX_SEQUENCE_REACHED;
            }
            issuer_obj.set_field_u32(sf("sfMintedNFTokens"), next_minted_count);

            // Update issuer account
            if view
                .update(Arc::new(STLedgerEntry::from_stobject(
                    issuer_obj,
                    *issuer_sle.key(),
                )))
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }

            // Compute the NFTokenID
            let nft_flags = (sttx.get_flags() & 0x0000FFFF) as u16;
            let transfer_fee = if sttx.is_field_present(sf("sfTransferFee")) {
                sttx.get_field_u16(sf("sfTransferFee"))
            } else {
                0
            };
            let taxon = protocol::nft::to_taxon(sttx.get_field_u32(sf("sfNFTokenTaxon")));
            let nftoken_id = protocol::nft::create_nftoken_id(
                nft_flags,
                transfer_fee,
                &issuer,
                taxon,
                token_seq,
            );

            // Read URI from transaction if present
            let uri = if sttx.is_field_present(sf("sfURI")) {
                let uri_bytes = sttx.get_field_vl(sf("sfURI"));
                Some(protocol::STBlob::from_buffer(
                    sf("sfURI"),
                    basics::buffer::Buffer::from(uri_bytes.as_slice()),
                ))
            } else {
                None
            };

            let mut token = STObject::new(sf("sfNFToken"));
            token.set_field_h256(sf("sfNFTokenID"), nftoken_id);
            if let Some(uri) = uri {
                token.set_stbase(uri);
            }

            let account_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
            let owner_count_before = match view.peek(account_keylet) {
                Ok(Some(owner)) => owner.get_field_u32(sf("sfOwnerCount")),
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };

            let insert_result = nft_insert_token(view, &account, token);
            if !is_tes_success(insert_result) {
                return insert_result;
            }

            // NFTokenMint may atomically create a sell offer for the newly
            // minted token.  It shares tokenOfferCreateApply with
            // NFTokenCreateOffer and always supplies tfSellNFToken.
            if sttx.is_field_present(sf("sfAmount")) {
                let amount = sttx.get_field_amount(sf("sfAmount"));
                let destination = sttx
                    .is_field_present(sf("sfDestination"))
                    .then(|| sttx.get_account_id(sf("sfDestination")));
                let expiration = sttx
                    .is_field_present(sf("sfExpiration"))
                    .then(|| sttx.get_field_u32(sf("sfExpiration")));
                let offer_result = ledger::nftoken_helpers::token_offer_create_apply(
                    view,
                    &account,
                    &amount,
                    destination.as_ref(),
                    expiration,
                    sttx.get_seq_value(),
                    &nftoken_id,
                    pre_fee_balance_drops,
                    protocol::tfSellNFToken,
                )
                .unwrap_or(Ter::TEF_BAD_LEDGER);
                if !is_tes_success(offer_result) {
                    return offer_result;
                }
            }

            // A mint only consumes additional reserve when insertion created a
            // page (or the optional sell offer created an owned object).
            let owner = match view.peek(account_keylet) {
                Ok(Some(owner)) => owner,
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let owner_count_after = owner.get_field_u32(sf("sfOwnerCount"));
            if owner_count_after > owner_count_before {
                let balance = pre_fee_balance_drops
                    .unwrap_or_else(|| owner.get_field_amount(sf("sfBalance")).xrp().drops());
                let Ok(reserve) =
                    i64::try_from(ledger::effective_account_reserve(view.fees(), &owner, 0, 0))
                else {
                    return Ter::TEF_BAD_LEDGER;
                };
                if balance < reserve {
                    return Ter::TEC_INSUFFICIENT_RESERVE;
                }
            }

            Ter::TES_SUCCESS
        }
        TxType::NFTOKEN_BURN => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let owner = if sttx.is_field_present(sf("sfOwner")) {
                sttx.get_account_id(sf("sfOwner"))
            } else {
                account
            };
            let token_id = sttx.get_field_h256(sf("sfNFTokenID"));

            // If account != owner, the burner is the issuer trying
            // to burn someone else's NFT. Check the tfBurnable flag (bit 0x0001
            // in the NFTokenID flags field, bytes 0-1).
            if account != owner {
                let id_bytes = token_id.data();
                let nft_flags = ((id_bytes[0] as u16) << 8) | (id_bytes[1] as u16);
                if (nft_flags & 0x0001) == 0 {
                    return Ter::TEC_NO_PERMISSION;
                }
            }

            let page = match nft_locate_page(view, &owner, token_id) {
                Ok(Some(page)) => page,
                Ok(None) => return Ter::TEC_NO_ENTRY,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let remove_result = nft_remove_token_from_page(view, &owner, token_id, page);
            if !is_tes_success(remove_result) {
                return remove_result;
            }

            // Burning is accounted against the issuer, which can differ from
            // both the transaction account and current owner.
            let issuer = protocol::get_nft_issuer(token_id);
            match view.peek(protocol::account_keylet(Uint160::from_void(issuer.data()))) {
                Ok(Some(issuer_sle)) => {
                    let burned = if issuer_sle.is_field_present(sf("sfBurnedNFTokens")) {
                        issuer_sle.get_field_u32(sf("sfBurnedNFTokens"))
                    } else {
                        0
                    };
                    let mut issuer_obj = issuer_sle.clone_as_object();
                    issuer_obj.set_field_u32(sf("sfBurnedNFTokens"), burned.wrapping_add(1));
                    if view
                        .update(Arc::new(STLedgerEntry::from_stobject(
                            issuer_obj,
                            *issuer_sle.key(),
                        )))
                        .is_err()
                    {
                        return Ter::TEF_BAD_LEDGER;
                    }
                }
                Ok(None) => {}
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }

            // Match rippled's bounded cleanup: sell offers are removed first,
            // then buy offers consume the remainder of the 500-entry budget.
            const MAX_DELETABLE_TOKEN_OFFERS: usize = 500;
            let deleted_sells = match ledger::nftoken_helpers::remove_token_offers_with_limit(
                view,
                &protocol::nft_sell_offers_keylet(token_id),
                MAX_DELETABLE_TOKEN_OFFERS,
            ) {
                Ok(deleted) => deleted,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if deleted_sells < MAX_DELETABLE_TOKEN_OFFERS
                && ledger::nftoken_helpers::remove_token_offers_with_limit(
                    view,
                    &protocol::nft_buy_offers_keylet(token_id),
                    MAX_DELETABLE_TOKEN_OFFERS - deleted_sells,
                )
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }
        TxType::NFTOKEN_CREATE_OFFER => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let token_id = sttx.get_field_h256(sf("sfNFTokenID"));
            let tx_flags = sttx.get_flags();
            let is_sell = (tx_flags & protocol::tfSellNFToken) != 0;
            let amount = sttx.get_field_amount(sf("sfAmount"));

            // Determine the NFT owner for lookup purposes.
            // For buy offers, sfOwner specifies who owns the token.
            // For sell offers, the tx account must be the owner.
            let nft_owner = if !is_sell && sttx.is_field_present(sf("sfOwner")) {
                sttx.get_account_id(sf("sfOwner"))
            } else {
                account
            };

            // Verify NFT exists: look up the token in the owner's pages.
            let nft_found = matches!(
                nft_find_token_and_page(view, &nft_owner, token_id),
                Ok(Some(_))
            );
            if !nft_found {
                return Ter::TEC_NO_ENTRY;
            }

            // Sell offers: account must own the NFT (already verified above since nft_owner == account for sell).
            // Buy offers: cannot buy your own NFT.
            if !is_sell {
                if nft_owner == account {
                    // Cannot create a buy offer for your own NFT
                    return Ter::TEC_NO_PERMISSION;
                }
                // Buy offers must have positive amount
                if amount.signum() <= 0 {
                    return Ter::TEM_BAD_AMOUNT;
                }
            }

            // tfOnlyXRP check: if the NFT has the tfOnlyXRP flag set (bit 0x0002 in
            // the high 16 bits of NFTokenID), reject non-XRP amounts.
            let id_bytes = token_id.data();
            let nft_flags_from_id = ((id_bytes[0] as u16) << 8) | (id_bytes[1] as u16);
            if (nft_flags_from_id & 0x0002) != 0 && !amount.native() && amount.signum() != 0 {
                return Ter::TEM_BAD_AMOUNT;
            }

            let destination = sttx
                .is_field_present(sf("sfDestination"))
                .then(|| sttx.get_account_id(sf("sfDestination")));
            let expiration = sttx
                .is_field_present(sf("sfExpiration"))
                .then(|| sttx.get_field_u32(sf("sfExpiration")));
            ledger::nftoken_helpers::token_offer_create_apply(
                view,
                &account,
                &amount,
                destination.as_ref(),
                expiration,
                sttx.get_seq_value(),
                &token_id,
                pre_fee_balance_drops,
                tx_flags,
            )
            .unwrap_or(Ter::TEF_BAD_LEDGER)
        }
        TxType::NFTOKEN_CANCEL_OFFER => {
            let tx_account = sttx.get_account_id(sf("sfAccount"));
            let offers = sttx.get_field_v256(sf("sfNFTokenOffers"));
            for offer_id in offers.value() {
                let offer_keylet = protocol::keylet::nft_offer_keylet(*offer_id);
                match view.peek(offer_keylet) {
                    Ok(Some(offer_sle)) => {
                        // NFTokenCancelOffer::preclaim permits cancellation only
                        // by the owner, the directed recipient, or anyone after
                        // expiration. Preserve that rule defensively before this
                        // apply path mutates either directory.
                        if offer_sle.get_type() != protocol::LedgerEntryType::NFTokenOffer {
                            return Ter::TEC_NO_PERMISSION;
                        }
                        let expired = offer_sle.is_field_present(sf("sfExpiration"))
                            && ledger::has_expired(
                                view,
                                Some(offer_sle.get_field_u32(sf("sfExpiration"))),
                            );
                        let offer_owner = offer_sle.get_account_id(sf("sfOwner"));
                        let recipient = offer_sle
                            .is_field_present(sf("sfDestination"))
                            .then(|| offer_sle.get_account_id(sf("sfDestination")));
                        if !expired && tx_account != offer_owner && recipient != Some(tx_account) {
                            return Ter::TEC_NO_PERMISSION;
                        }

                        match ledger::nftoken_helpers::delete_token_offer(view, offer_sle) {
                            Ok(true) => {}
                            Ok(false) | Err(_) => return Ter::TEF_BAD_LEDGER,
                        }
                    }
                    Ok(None) => {}
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                }
            }
            Ter::TES_SUCCESS
        }
        TxType::NFTOKEN_ACCEPT_OFFER => {
            let tx_account = sttx.get_account_id(sf("sfAccount"));

            // Load offers
            let sell_offer = if sttx.is_field_present(sf("sfNFTokenSellOffer")) {
                let id = sttx.get_field_h256(sf("sfNFTokenSellOffer"));
                match view.peek(protocol::keylet::nft_offer_keylet(Uint256::from(id))) {
                    Ok(value) => value,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                }
            } else {
                None
            };
            let buy_offer = if sttx.is_field_present(sf("sfNFTokenBuyOffer")) {
                let id = sttx.get_field_h256(sf("sfNFTokenBuyOffer"));
                match view.peek(protocol::keylet::nft_offer_keylet(Uint256::from(id))) {
                    Ok(value) => value,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                }
            } else {
                None
            };

            // Validate: at least one offer must exist
            if sell_offer.is_none() && buy_offer.is_none() {
                return Ter::TEC_OBJECT_NOT_FOUND;
            }

            // Before fixCleanup3_1_3, expiration is a preclaim failure and
            // the offer remains in the ledger. With the amendment enabled we
            // defer it to apply, delete every expired supplied offer, and
            // return tecEXPIRED.
            let buy_offer_expired = buy_offer.as_ref().is_some_and(|offer| {
                offer.is_field_present(sf("sfExpiration"))
                    && ledger::has_expired(view, Some(offer.get_field_u32(sf("sfExpiration"))))
            });
            let sell_offer_expired = sell_offer.as_ref().is_some_and(|offer| {
                offer.is_field_present(sf("sfExpiration"))
                    && ledger::has_expired(view, Some(offer.get_field_u32(sf("sfExpiration"))))
            });
            let fix_cleanup_3_1_3 = view.rules().enabled(&protocol::fix_cleanup_3_1_3());
            if !fix_cleanup_3_1_3 {
                if buy_offer_expired || sell_offer_expired {
                    return Ter::TEC_EXPIRED;
                }
            } else {
                let mut found_expired = false;
                if buy_offer_expired {
                    let Some(offer) = buy_offer.as_ref().cloned() else {
                        return Ter::TEF_INTERNAL;
                    };
                    match nft_accept_delete_result(ledger::nftoken_helpers::delete_token_offer(
                        view, offer,
                    )) {
                        Ter::TES_SUCCESS => found_expired = true,
                        result => return result,
                    }
                }
                if sell_offer_expired {
                    let Some(offer) = sell_offer.as_ref().cloned() else {
                        return Ter::TEF_INTERNAL;
                    };
                    match nft_accept_delete_result(ledger::nftoken_helpers::delete_token_offer(
                        view, offer,
                    )) {
                        Ter::TES_SUCCESS => found_expired = true,
                        result => return result,
                    }
                }
                if found_expired {
                    return Ter::TEC_EXPIRED;
                }
            }

            if buy_offer
                .as_ref()
                .is_some_and(|offer| offer.get_field_amount(sf("sfAmount")).signum() < 0)
                || sell_offer
                    .as_ref()
                    .is_some_and(|offer| offer.get_field_amount(sf("sfAmount")).signum() < 0)
            {
                return Ter::TEM_BAD_OFFER;
            }

            if let (Some(bo), Some(so)) = (&buy_offer, &sell_offer) {
                let buy_amount = bo.get_field_amount(sf("sfAmount"));
                let sell_amount = so.get_field_amount(sf("sfAmount"));
                if bo.get_field_h256(sf("sfNFTokenID")) != so.get_field_h256(sf("sfNFTokenID"))
                    || buy_amount.asset() != sell_amount.asset()
                {
                    return Ter::TEC_NFTOKEN_BUY_SELL_MISMATCH;
                }
                if bo.get_account_id(sf("sfOwner")) == so.get_account_id(sf("sfOwner")) {
                    return Ter::TEC_CANT_ACCEPT_OWN_NFTOKEN_OFFER;
                }
                if sell_amount > buy_amount {
                    return Ter::TEC_INSUFFICIENT_PAYMENT;
                }
                if sttx.is_field_present(sf("sfNFTokenBrokerFee")) {
                    let broker_fee = sttx.get_field_amount(sf("sfNFTokenBrokerFee"));
                    if broker_fee.asset() != buy_amount.asset() {
                        return Ter::TEC_NFTOKEN_BUY_SELL_MISMATCH;
                    }
                    if broker_fee >= buy_amount.clone()
                        || sell_amount > buy_amount.clone() - broker_fee.clone()
                    {
                        return Ter::TEC_INSUFFICIENT_PAYMENT;
                    }
                    if !broker_fee.native()
                        && view
                            .rules()
                            .enabled(&protocol::fix_enforce_nftoken_trustline_v2())
                    {
                        let issue = broker_fee.issue();
                        match ledger::nftoken_helpers::check_trustline_authorized(
                            view,
                            &tx_account,
                            &issue,
                        ) {
                            Ok(ter) if !is_tes_success(ter) => return ter,
                            Err(_) => return Ter::TEF_BAD_LEDGER,
                            _ => {}
                        }
                        match ledger::nftoken_helpers::check_trustline_deep_frozen(
                            view,
                            &tx_account,
                            &issue,
                        ) {
                            Ok(ter) if !is_tes_success(ter) => return ter,
                            Err(_) => return Ter::TEF_BAD_LEDGER,
                            _ => {}
                        }
                    }
                }
            }

            if let Some(bo) = &buy_offer {
                if bo.is_flag(protocol::lsfSellNFToken) {
                    return Ter::TEC_NFTOKEN_OFFER_TYPE_MISMATCH;
                }
                if bo.get_account_id(sf("sfOwner")) == tx_account {
                    return Ter::TEC_CANT_ACCEPT_OWN_NFTOKEN_OFFER;
                }
                if sell_offer.is_none() {
                    match nft_find_token_and_page(
                        view,
                        &tx_account,
                        bo.get_field_h256(sf("sfNFTokenID")),
                    ) {
                        Ok(Some(_)) => {}
                        Ok(None) => return Ter::TEC_NO_PERMISSION,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                    }
                }
                let needed = bo.get_field_amount(sf("sfAmount"));
                match nft_account_funds_at_least(view, &bo.get_account_id(sf("sfOwner")), &needed) {
                    Ok(true) => {}
                    Ok(false) => return Ter::TEC_INSUFFICIENT_FUNDS,
                    Err(ter) => return ter,
                }
                if !needed.native()
                    && view
                        .rules()
                        .enabled(&protocol::fix_enforce_nftoken_trustline_v2())
                {
                    let issue = needed.issue();
                    match ledger::nftoken_helpers::check_trustline_authorized(
                        view,
                        &bo.get_account_id(sf("sfOwner")),
                        &issue,
                    ) {
                        Ok(ter) if !is_tes_success(ter) => return ter,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                        _ => {}
                    }
                    if sell_offer.is_none() {
                        for check in [
                            ledger::nftoken_helpers::check_trustline_authorized(
                                view,
                                &tx_account,
                                &issue,
                            ),
                            ledger::nftoken_helpers::check_trustline_deep_frozen(
                                view,
                                &tx_account,
                                &issue,
                            ),
                        ] {
                            match check {
                                Ok(ter) if !is_tes_success(ter) => return ter,
                                Err(_) => return Ter::TEF_BAD_LEDGER,
                                _ => {}
                            }
                        }
                    }
                }
            }

            if let Some(so) = &sell_offer {
                if !so.is_flag(protocol::lsfSellNFToken) {
                    return Ter::TEC_NFTOKEN_OFFER_TYPE_MISMATCH;
                }
                if so.get_account_id(sf("sfOwner")) == tx_account {
                    return Ter::TEC_CANT_ACCEPT_OWN_NFTOKEN_OFFER;
                }
                match nft_find_token_and_page(
                    view,
                    &so.get_account_id(sf("sfOwner")),
                    so.get_field_h256(sf("sfNFTokenID")),
                ) {
                    Ok(Some(_)) => {}
                    Ok(None) => return Ter::TEC_NO_PERMISSION,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                }
                let needed = so.get_field_amount(sf("sfAmount"));
                if buy_offer.is_none() {
                    match nft_account_funds_at_least(view, &tx_account, &needed) {
                        Ok(true) => {}
                        Ok(false) => return Ter::TEC_INSUFFICIENT_FUNDS,
                        Err(ter) => return ter,
                    }
                }
                if !needed.native() {
                    let issue = needed.issue();
                    if view
                        .rules()
                        .enabled(&protocol::fix_enforce_nftoken_trustline_v2())
                    {
                        match ledger::nftoken_helpers::check_trustline_authorized(
                            view,
                            &so.get_account_id(sf("sfOwner")),
                            &issue,
                        ) {
                            Ok(ter) if !is_tes_success(ter) => return ter,
                            Err(_) => return Ter::TEF_BAD_LEDGER,
                            _ => {}
                        }
                        if buy_offer.is_none() {
                            match ledger::nftoken_helpers::check_trustline_authorized(
                                view,
                                &tx_account,
                                &issue,
                            ) {
                                Ok(ter) if !is_tes_success(ter) => return ter,
                                Err(_) => return Ter::TEF_BAD_LEDGER,
                                _ => {}
                            }
                        }
                    }
                    match ledger::nftoken_helpers::check_trustline_deep_frozen(
                        view,
                        &so.get_account_id(sf("sfOwner")),
                        &issue,
                    ) {
                        Ok(ter) if !is_tes_success(ter) => return ter,
                        Err(_) => return Ter::TEF_BAD_LEDGER,
                        _ => {}
                    }
                }
            }

            let royalty_offer = buy_offer.as_ref().or(sell_offer.as_ref());
            if let Some(offer) = royalty_offer {
                let token_id = offer.get_field_h256(sf("sfNFTokenID"));
                let amount = offer.get_field_amount(sf("sfAmount"));
                let nft_issuer = protocol::get_nft_issuer(token_id);
                if protocol::get_nft_transfer_fee(token_id) != 0 && !amount.native() {
                    let issue = amount.issue();
                    if view
                        .rules()
                        .enabled(&protocol::feature_id("fixEnforceNFTokenTrustline"))
                        && (protocol::get_nft_flags(token_id) & protocol::FLAG_CREATE_TRUST_LINES)
                            == 0
                        && nft_issuer != issue.account
                    {
                        match view.read(protocol::line(nft_issuer, issue.account, issue.currency)) {
                            Ok(Some(_)) => {}
                            Ok(None) => return Ter::TEC_NO_LINE,
                            Err(_) => return Ter::TEF_BAD_LEDGER,
                        }
                    }
                    if view
                        .rules()
                        .enabled(&protocol::fix_enforce_nftoken_trustline_v2())
                    {
                        for check in [
                            ledger::nftoken_helpers::check_trustline_authorized(
                                view,
                                &nft_issuer,
                                &issue,
                            ),
                            ledger::nftoken_helpers::check_trustline_deep_frozen(
                                view,
                                &nft_issuer,
                                &issue,
                            ),
                        ] {
                            match check {
                                Ok(ter) if !is_tes_success(ter) => return ter,
                                Err(_) => return Ter::TEF_BAD_LEDGER,
                                _ => {}
                            }
                        }
                    }
                }
            }

            // rippled preclaim requires every directed offer in a brokered
            // acceptance to name the submitting broker, not the counterparty
            // offer owner. Direct acceptance keeps the same account check.
            if let Some(ref so) = sell_offer {
                if so.is_field_present(sf("sfDestination"))
                    && so.get_account_id(sf("sfDestination")) != tx_account
                {
                    return Ter::TEC_NO_PERMISSION;
                }
            }
            if let Some(ref bo) = buy_offer {
                if bo.is_field_present(sf("sfDestination"))
                    && bo.get_account_id(sf("sfDestination")) != tx_account
                {
                    return Ter::TEC_NO_PERMISSION;
                }
            }

            let delete_offer = |view: &mut V, offer: &Arc<STLedgerEntry>| {
                nft_accept_delete_result(ledger::nftoken_helpers::delete_token_offer(
                    view,
                    offer.clone(),
                ))
            };

            // Delete both offers first (reference does this before payment/transfer)
            if let Some(ref bo) = buy_offer {
                let result = delete_offer(view, bo);
                if result != Ter::TES_SUCCESS {
                    return result;
                }
            }
            if let Some(ref so) = sell_offer {
                let result = delete_offer(view, so);
                if result != Ter::TES_SUCCESS {
                    return result;
                }
            }

            // Determine buyer, seller, amount, nftokenID based on mode
            let (buyer, seller, nftoken_id, amount) =
                if let (Some(bo), Some(so)) = (&buy_offer, &sell_offer) {
                    // Broker mode: both offers present
                    let buyer = bo.get_account_id(sf("sfOwner"));
                    let seller = so.get_account_id(sf("sfOwner"));
                    let nftoken_id = so.get_field_h256(sf("sfNFTokenID"));
                    let amount = bo.get_field_amount(sf("sfAmount"));
                    (buyer, seller, nftoken_id, amount)
                } else if let Some(ref so) = sell_offer {
                    // Sell offer only: tx_account is buyer
                    let seller = so.get_account_id(sf("sfOwner"));
                    let nftoken_id = so.get_field_h256(sf("sfNFTokenID"));
                    let amount = so.get_field_amount(sf("sfAmount"));
                    (tx_account, seller, nftoken_id, amount)
                } else if let Some(ref bo) = buy_offer {
                    // Buy offer only: tx_account is seller
                    let buyer = bo.get_account_id(sf("sfOwner"));
                    let nftoken_id = bo.get_field_h256(sf("sfNFTokenID"));
                    let amount = bo.get_field_amount(sf("sfAmount"));
                    // Verify tx_account actually owns the NFT
                    let owns = matches!(
                        nft_find_token_and_page(view, &tx_account, nftoken_id),
                        Ok(Some(_))
                    );
                    if !owns {
                        return Ter::TEC_NO_PERMISSION;
                    }
                    (buyer, tx_account, nftoken_id, amount)
                } else {
                    return Ter::TEF_INTERNAL;
                };

            // Brokered acceptance pays the requested broker fee first, then
            // calculates the issuer transfer fee from the remainder, exactly
            // as NFTokenAcceptOffer::doApply does in rippled.
            let mut amount = amount;
            if buy_offer.is_some()
                && sell_offer.is_some()
                && sttx.is_field_present(sf("sfNFTokenBrokerFee"))
            {
                let broker_fee = sttx.get_field_amount(sf("sfNFTokenBrokerFee"));
                if broker_fee.signum() > 0 {
                    let pay_result = nft_accept_offer_pay(view, &buyer, &tx_account, &broker_fee);
                    if !is_tes_success(pay_result) {
                        return pay_result;
                    }
                    amount -= broker_fee;
                }
            }

            // Transfer fee handling: extract transfer fee from NFTokenID.
            // NFTokenID bytes 0-1 = flags, bytes 2-3 = transfer fee (basis points out of 50000).
            // Bytes 4-23 = issuer account (20 bytes).
            // Transfer fee only applies on secondary sales (seller != issuer).
            let id_bytes = nftoken_id.data();
            let transfer_fee_bps = ((id_bytes[2] as u16) << 8) | (id_bytes[3] as u16);
            // Extract issuer from NFTokenID bytes 4..24
            let mut issuer_bytes = [0u8; 20];
            issuer_bytes.copy_from_slice(&id_bytes[4..24]);
            let issuer_id = AccountID::from_array(issuer_bytes);

            if amount.signum() > 0 {
                if transfer_fee_bps != 0 && seller != issuer_id && buyer != issuer_id {
                    let cut = match nft_transfer_fee_cut(&amount, transfer_fee_bps) {
                        Ok(cut) => cut,
                        Err(ter) => return ter,
                    };
                    if cut.signum() != 0 {
                        let pay_result = nft_accept_offer_pay(view, &buyer, &issuer_id, &cut);
                        if !is_tes_success(pay_result) {
                            return pay_result;
                        }
                        amount -= cut;
                    }
                }
                if amount.signum() > 0 {
                    let pay_result = nft_accept_offer_pay(view, &buyer, &seller, &amount);
                    if !is_tes_success(pay_result) {
                        return pay_result;
                    }
                }
            }

            nft_transfer_token(view, &buyer, &seller, nftoken_id)
        }
        TxType::CLAWBACK => {
            let issuer = sttx.get_account_id(sf("sfAccount"));
            let amount = sttx.get_field_amount(sf("sfAmount"));
            let holder = if amount.holds_mpt_issue() {
                if !view.rules().enabled(&protocol::feature_id("MPTokensV1")) {
                    return Ter::TEM_DISABLED;
                }
                if !sttx.is_field_present(sf("sfHolder")) {
                    return Ter::TEM_MALFORMED;
                }
                let holder = sttx.get_account_id(sf("sfHolder"));
                if holder == issuer {
                    return Ter::TEM_MALFORMED;
                }
                if amount.signum() <= 0 || amount.mpt().value() > protocol::MAX_MP_TOKEN_AMOUNT {
                    return Ter::TEM_BAD_AMOUNT;
                }
                holder
            } else {
                if sttx.is_field_present(sf("sfHolder")) {
                    return Ter::TEM_MALFORMED;
                }
                if amount.native() || amount.signum() <= 0 {
                    return Ter::TEM_BAD_AMOUNT;
                }
                let holder = amount.issue().account;
                if holder == issuer {
                    return Ter::TEM_BAD_AMOUNT;
                }
                holder
            };

            let issuer_sle =
                match view.peek(protocol::account_keylet(Uint160::from_void(issuer.data()))) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TER_NO_ACCOUNT,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
            let holder_sle =
                match view.peek(protocol::account_keylet(Uint160::from_void(holder.data()))) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TER_NO_ACCOUNT,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
            let holder_is_pseudo = ["sfAMMID", "sfVaultID", "sfLoanBrokerID"]
                .iter()
                .any(|field| holder_sle.is_field_present(sf(field)));
            if view
                .rules()
                .enabled(&protocol::feature_id("SingleAssetVault"))
                && holder_is_pseudo
            {
                return Ter::TEC_PSEUDO_ACCOUNT;
            }
            if holder_sle.is_field_present(sf("sfAMMID")) {
                return Ter::TEC_AMM_ACCOUNT;
            }
            if amount.holds_mpt_issue() {
                let mpt_issue = match &amount.asset() {
                    protocol::Asset::MPTIssue(i) => *i,
                    _ => return Ter::TEF_INTERNAL,
                };
                let mptid = mpt_issue.mpt_id();
                // Preclaim: check lsfMPTCanClawback
                let issuance_keylet = protocol::mpt_issuance_keylet_from_mptid(mptid);
                let iss_sle = match view.peek(issuance_keylet) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TEC_OBJECT_NOT_FOUND,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                if !iss_sle.is_flag(protocol::lsfMPTCanClawback) {
                    return Ter::TEC_NO_PERMISSION;
                }
                if iss_sle.get_account_id(sf("sfIssuer")) != issuer {
                    return Ter::TEC_NO_PERMISSION;
                }
                let holder_keylet =
                    protocol::mptoken_keylet_from_mptid(mptid, Uint160::from_void(holder.data()));
                let token_sle = match view.peek(holder_keylet) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TEC_OBJECT_NOT_FOUND,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let balance = token_sle.get_field_u64(sf("sfMPTAmount"));
                if balance == 0 {
                    return Ter::TEC_INSUFFICIENT_FUNDS;
                }
                let clawback_amt = amount.mpt().value().unsigned_abs().min(balance);
                let clawback_amt = match i64::try_from(clawback_amt) {
                    Ok(amount) => amount,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let actual = STAmount::from_mpt_amount(
                    sf("sfAmount"),
                    MPTAmount::from_value(clawback_amt),
                    mpt_issue,
                );
                return ledger::ripple_state_helpers::account_send(view, &holder, &issuer, &actual);
            } else {
                // IOU clawback — debit specific amount from holder's trust line
                // Preclaim: check lsfAllowTrustLineClawback
                if !issuer_sle.is_flag(protocol::lsfAllowTrustLineClawback)
                    || issuer_sle.is_flag(protocol::lsfNoFreeze)
                {
                    return Ter::TEC_NO_PERMISSION;
                }
                let currency = amount.issue().currency;
                let line_keylet = protocol::line(issuer, holder, currency);
                match view.peek(line_keylet) {
                    Ok(Some(line)) => {
                        let b_high = holder > issuer;
                        let current_balance = line.get_field_amount(sf("sfBalance"));
                        if (current_balance.signum() > 0 && issuer < holder)
                            || (current_balance.signum() < 0 && issuer > holder)
                        {
                            return Ter::TEC_NO_PERMISSION;
                        }
                        // Determine holder's balance (positive from their perspective)
                        let mut holder_balance = if b_high {
                            let mut neg = current_balance.clone();
                            neg.negate();
                            neg
                        } else {
                            current_balance.clone()
                        };
                        holder_balance.set_issuer(issuer);
                        if holder_balance.signum() <= 0 {
                            return Ter::TEC_INSUFFICIENT_FUNDS;
                        }
                        // Clawback the minimum of requested and available
                        // This makes both amounts have the same issue (issuer's perspective).
                        let normalized_amount = {
                            let mut a = amount.clone();
                            a.set_issue(protocol::Issue {
                                account: issuer,
                                currency,
                            });
                            a
                        };
                        let clawback_actual = if normalized_amount > holder_balance {
                            holder_balance
                        } else {
                            normalized_amount
                        };
                        return ledger::ripple_state_helpers::account_send(
                            view,
                            &holder,
                            &issuer,
                            &clawback_actual,
                        );
                    }
                    Ok(None) => return Ter::TEC_NO_LINE,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                }
            }
        }

        // --- Tickets ---
        TxType::TICKET_CREATE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let count = sttx.get_field_u32(sf("sfTicketCount"));
            let mut sink = DispatcherTicketCreateSink {
                view,
                account,
                tx_sequence: sttx.get_field_u32(sf("sfSequence")),
                pre_fee_balance_drops,
                failure: None,
            };
            let result = run_ticket_create_do_apply(count, &mut sink);
            sink.failure.unwrap_or(result)
        }

        // --- DID ---
        TxType::DID_SET => {
            let did_preflight = tx::run_did_set_preflight(tx::DidSetPreflightFacts {
                uri_len: sttx
                    .is_field_present(sf("sfURI"))
                    .then(|| sttx.get_field_vl(sf("sfURI")).len()),
                did_document_len: sttx
                    .is_field_present(sf("sfDIDDocument"))
                    .then(|| sttx.get_field_vl(sf("sfDIDDocument")).len()),
                data_len: sttx
                    .is_field_present(sf("sfData"))
                    .then(|| sttx.get_field_vl(sf("sfData")).len()),
            });
            if did_preflight != Ter::TES_SUCCESS {
                return did_preflight;
            }
            let account = sttx.get_account_id(sf("sfAccount"));
            let did_keylet = protocol::did_keylet(Uint160::from_void(account.data()));
            let existing = match view.peek(did_keylet) {
                Ok(existing) => existing,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let is_new = existing.is_none();
            let mut sle = if let Some(e) = existing {
                STLedgerEntry::from_stobject(e.clone_as_object(), *e.key())
            } else {
                let mut new_sle = STLedgerEntry::new(did_keylet);
                new_sle.set_account_id(sf("sfAccount"), account);
                new_sle
            };
            // Match rippled DIDSet::doApply: a present empty VL removes the
            // field on update, while a new DID stores only nonempty fields.
            // Keep all three optional DID fields together so Data cannot be
            // silently dropped from the live dispatcher path.
            for field in [sf("sfDIDDocument"), sf("sfURI"), sf("sfData")] {
                if !sttx.is_field_present(field) {
                    continue;
                }

                let value = sttx.get_field_vl(field);
                if value.is_empty() {
                    if !is_new {
                        sle.make_field_absent(field);
                    }
                } else {
                    sle.set_stbase(protocol::STBlob::from_buffer(
                        field,
                        basics::buffer::Buffer::from(&value[..]),
                    ));
                }
            }
            if !is_new
                && !sle.is_field_present(sf("sfDIDDocument"))
                && !sle.is_field_present(sf("sfURI"))
                && !sle.is_field_present(sf("sfData"))
            {
                return Ter::TEC_EMPTY_DID;
            }
            if is_new {
                // Before fixEmptyDID, a transaction containing only an empty
                // optional field could create an empty DID. Preserve that
                // historical path, but reject it before reserve/directory
                // work once the amendment is enabled, as rippled does.
                if view.rules().enabled(&protocol::feature_id("fixEmptyDID"))
                    && !sle.is_field_present(sf("sfDIDDocument"))
                    && !sle.is_field_present(sf("sfURI"))
                    && !sle.is_field_present(sf("sfData"))
                {
                    return Ter::TEC_EMPTY_DID;
                }
                let account_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
                let acct = match view.peek(account_keylet) {
                    Ok(Some(acct)) => acct,
                    Ok(None) => return Ter::TEF_INTERNAL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let balance = acct.get_field_amount(sf("sfBalance")).xrp().drops();
                // DIDSet::doApply uses Sponsor-aware accountReserve with an
                // owner-count delta of one.  Raw OwnerCount is insufficient:
                // sponsored objects do not consume this account's reserve,
                // while accounts/objects sponsored by this account do.
                let Ok(reserve) =
                    i64::try_from(ledger::effective_account_reserve(view.fees(), &acct, 1, 0))
                else {
                    return Ter::TEF_BAD_LEDGER;
                };
                if balance < reserve {
                    return Ter::TEC_INSUFFICIENT_RESERVE;
                }
                let owner_dir = protocol::owner_dir_keylet(Uint160::from_void(account.data()));
                match ledger::dir_insert(
                    view,
                    &owner_dir,
                    did_keylet.key,
                    &describe_owner_dir(account),
                ) {
                    Ok(Some(page)) => sle.set_field_u64(sf("sfOwnerNode"), page),
                    Ok(None) => return Ter::TEC_DIR_FULL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                }
                if view.insert(Arc::new(sle)).is_err() {
                    return Ter::TEF_BAD_LEDGER;
                }
                if ledger::adjust_owner_count(view, &acct, 1).is_err() {
                    return Ter::TEF_BAD_LEDGER;
                }
            } else if view.update(Arc::new(sle)).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }
        TxType::DID_DELETE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let did_keylet = protocol::did_keylet(Uint160::from_void(account.data()));
            let did_sle = match view.peek(did_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TEC_NO_ENTRY,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            // Match rippled DIDDelete::deleteSLE: keep the root directory,
            // require owner-directory removal, then decrement the owner count
            // before erasing the DID object.
            let owner_node = did_sle.get_field_u64(sf("sfOwnerNode"));
            let owner_dir = owner_dir_keylet(Uint160::from_void(account.data()));
            if !matches!(
                ledger::dir_remove(view, &owner_dir, owner_node, *did_sle.key(), true),
                Ok(true)
            ) {
                return Ter::TEF_BAD_LEDGER;
            }
            let acct = match view.peek(protocol::account_keylet(Uint160::from_void(account.data())))
            {
                Ok(Some(acct)) => acct,
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if ledger::adjust_owner_count(view, &acct, -1).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            if view.erase(did_sle).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }

        // --- Oracle ---
        TxType::ORACLE_SET => {
            let preflight = run_oracle_set_sttx_preflight(sttx);
            if preflight != Ter::TES_SUCCESS {
                return preflight;
            }

            let account = sttx.get_account_id(sf("sfAccount"));
            let oracle_document_id = sttx.get_field_u32(sf("sfOracleDocumentID"));
            let mut sink = crate::state::transactor_oracle_bridge::ViewBackedOracleSetSink {
                view,
                account,
                oracle_document_id,
                failure: None,
            };
            let result = run_oracle_set_do_apply(
                OracleSetApplyFacts {
                    provider: sttx.get_field_vl(sf("sfProvider")).to_vec(),
                    asset_class: sttx.get_field_vl(sf("sfAssetClass")).to_vec(),
                    // Omission retains the stored URI; present values, including
                    // arbitrary VL bytes, replace it exactly.
                    uri: sttx
                        .is_field_present(sf("sfURI"))
                        .then(|| sttx.get_field_vl(sf("sfURI")).to_vec()),
                    last_update_time_secs: u64::from(sttx.get_field_u32(sf("sfLastUpdateTime"))),
                    oracle_document_id,
                    tx_series: oracle_set_series_from_stobject(sttx),
                },
                &mut sink,
            );
            sink.failure.unwrap_or(result)
        }
        TxType::ORACLE_DELETE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let oracle_doc_id = sttx.get_field_u32(sf("sfOracleDocumentID"));
            let oracle_keylet =
                protocol::oracle_keylet(Uint160::from_void(account.data()), oracle_doc_id);
            let oracle_sle = match view.peek(oracle_keylet) {
                Ok(Some(sle)) => sle,
                // OracleDelete::preclaim already proved this key exists.
                // Pinned doApply treats disappearance as corrupt state.
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let owner_node = oracle_sle.get_field_u64(sf("sfOwnerNode"));
            let owner_count =
                oracle_owner_count(oracle_sle.get_field_array(sf("sfPriceDataSeries")).len());
            let owner_dir = owner_dir_keylet(Uint160::from_void(account.data()));
            if !matches!(
                ledger::dir_remove(view, &owner_dir, owner_node, *oracle_sle.key(), true),
                Ok(true)
            ) {
                return Ter::TEF_BAD_LEDGER;
            }
            let account_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
            let account_sle = match view.peek(account_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if ledger::adjust_owner_count(view, &account_sle, -owner_count).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            if view.erase(oracle_sle).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }

        // --- MPToken ---
        TxType::MPTOKEN_ISSUANCE_CREATE => {
            let tx_flags = sttx.get_field_u32(sf("sfFlags"));
            // Amendment gates and transaction-local validation are semantic
            // preflight work. Pinned doApply enters create() directly.
            let account = sttx.get_account_id(sf("sfAccount"));
            let sequence = sttx.get_seq_value();
            let account_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
            let account_sle = match view.peek(account_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let sponsor_sle = match check_cash_reserve_sponsor(view, sttx) {
                Ok(sponsor) => sponsor,
                Err(ter) => return ter,
            };
            let has_reserve = match check_cash_has_object_reserve(
                view,
                &account_sle,
                pre_fee_balance_drops,
                sponsor_sle.as_ref(),
            ) {
                Ok(value) => value,
                Err(ter) => return ter,
            };
            if !has_reserve {
                return Ter::TEC_INSUFFICIENT_RESERVE;
            }
            let issuance_keylet =
                protocol::mpt_issuance_keylet(sequence, Uint160::from_void(account.data()));
            let mut sle = STLedgerEntry::new(issuance_keylet);
            sle.set_account_id(sf("sfIssuer"), account);
            sle.set_field_u32(sf("sfSequence"), sequence);
            sle.set_field_u64(sf("sfOutstandingAmount"), 0);
            if sttx.is_field_present(sf("sfMaximumAmount")) {
                sle.set_field_u64(
                    sf("sfMaximumAmount"),
                    sttx.get_field_u64(sf("sfMaximumAmount")),
                );
            }
            if sttx.is_field_present(sf("sfAssetScale")) {
                sle.set_field_u8(sf("sfAssetScale"), sttx.get_field_u8(sf("sfAssetScale")));
            }
            if sttx.is_field_present(sf("sfTransferFee")) {
                sle.set_field_u16(sf("sfTransferFee"), sttx.get_field_u16(sf("sfTransferFee")));
            }
            if sttx.is_field_present(sf("sfMPTokenMetadata")) {
                sle.set_stbase(protocol::STBlob::from_buffer(
                    sf("sfMPTokenMetadata"),
                    basics::buffer::Buffer::from(&sttx.get_field_vl(sf("sfMPTokenMetadata"))[..]),
                ));
            }
            if sttx.is_field_present(sf("sfDomainID")) {
                sle.set_field_h256(sf("sfDomainID"), sttx.get_field_h256(sf("sfDomainID")));
            }
            if sttx.is_field_present(sf("sfImmutableFlags")) {
                sle.set_field_u32(
                    sf("sfImmutableFlags"),
                    sttx.get_field_u32(sf("sfImmutableFlags")),
                );
            }
            if let Some(sponsor_sle) = sponsor_sle.as_ref() {
                sle.set_account_id(sf("sfSponsor"), sponsor_sle.get_account_id(sf("sfAccount")));
            }
            sle.set_field_u32(sf("sfFlags"), tx_flags & !protocol::tfUniversal);
            let owner_dir = protocol::owner_dir_keylet(Uint160::from_void(account.data()));
            let owner_node = match ledger::dir_insert(
                view,
                &owner_dir,
                issuance_keylet.key,
                &describe_owner_dir(account),
            ) {
                Ok(Some(page)) => page,
                Ok(None) => return Ter::TEC_DIR_FULL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            sle.set_field_u64(sf("sfOwnerNode"), owner_node);
            if view.insert(Arc::new(sle)).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            if ledger::increase_owner_count_for_object(view, &account_sle, sponsor_sle.as_ref())
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }
        TxType::MPTOKEN_ISSUANCE_DESTROY => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let mptid = sttx.get_field_h192(sf("sfMPTokenIssuanceID"));
            let issuance_keylet = protocol::mpt_issuance_keylet_from_mptid(mptid);
            let iss_sle = match view.peek(issuance_keylet) {
                Ok(Some(sle)) => sle,
                // Immutable preclaim already established this issuance.
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if iss_sle.get_account_id(sf("sfIssuer")) != account {
                return Ter::TEC_INTERNAL;
            }
            let owner_node = iss_sle.get_field_u64(sf("sfOwnerNode"));
            let owner_dir = owner_dir_keylet(Uint160::from_void(account.data()));
            if !matches!(
                ledger::dir_remove(view, &owner_dir, owner_node, *iss_sle.key(), false),
                Ok(true)
            ) {
                return Ter::TEF_BAD_LEDGER;
            }
            let acct = match view.peek(protocol::account_keylet(Uint160::from_void(account.data())))
            {
                Ok(Some(acct)) => acct,
                _ => return Ter::TEF_BAD_LEDGER,
            };
            if ledger::decrease_owner_count_for_object(view, &acct, &iss_sle, 1).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            if view.erase(iss_sle.clone()).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }
        TxType::MPTOKEN_ISSUANCE_SET => {
            let holder = sttx
                .is_field_present(sf("sfHolder"))
                .then(|| sttx.get_account_id(sf("sfHolder")));
            let immutable_flags = sttx
                .is_field_present(sf("sfImmutableFlags"))
                .then(|| sttx.get_field_u32(sf("sfImmutableFlags")));
            let mptid = sttx.get_field_h192(sf("sfMPTokenIssuanceID"));
            let target_keylet = if let Some(holder) = holder {
                protocol::mptoken_keylet_from_mptid(mptid, Uint160::from_void(holder.data()))
            } else {
                protocol::mpt_issuance_keylet_from_mptid(mptid)
            };
            // All policy and existence checks are immutable preclaim work.
            // Pinned MPTokenIssuanceSet::doApply selects exactly one target and
            // classifies its disappearance as tecINTERNAL.
            let target_sle = match view.peek(target_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            {
                let mut obj = target_sle.clone_as_object();
                let flags_in = obj.get_field_u32(sf("sfFlags"));
                let mut flags_out = flags_in;

                if (sttx.get_flags() & protocol::tfMPTLock) != 0 {
                    flags_out |= protocol::lsfMPTLocked;
                } else if (sttx.get_flags() & protocol::tfMPTUnlock) != 0 {
                    flags_out &= !protocol::lsfMPTLocked;
                }

                for (set_flag, ledger_flag) in [
                    (protocol::tfMPTSetCanLock, protocol::lsfMPTCanLock),
                    (protocol::tfMPTSetRequireAuth, protocol::lsfMPTRequireAuth),
                    (protocol::tfMPTSetCanEscrow, protocol::lsfMPTCanEscrow),
                    (protocol::tfMPTSetCanTrade, protocol::lsfMPTCanTrade),
                    (protocol::tfMPTSetCanTransfer, protocol::lsfMPTCanTransfer),
                    (protocol::tfMPTSetCanClawback, protocol::lsfMPTCanClawback),
                    (
                        protocol::tfMPTSetCanHoldConfidentialBalance,
                        protocol::lsfMPTCanHoldConfidentialBalance,
                    ),
                ] {
                    if (sttx.get_flags() & set_flag) != 0 {
                        flags_out |= ledger_flag;
                    }
                }

                if flags_in != flags_out {
                    obj.set_field_u32(sf("sfFlags"), flags_out);
                }
                if sttx.is_field_present(sf("sfTransferFee")) {
                    let transfer_fee = sttx.get_field_u16(sf("sfTransferFee"));
                    if transfer_fee == 0 {
                        obj.make_field_absent(sf("sfTransferFee"));
                    } else {
                        obj.set_field_u16(sf("sfTransferFee"), transfer_fee);
                    }
                }
                if sttx.is_field_present(sf("sfMPTokenMetadata")) {
                    let metadata = sttx.get_field_vl(sf("sfMPTokenMetadata"));
                    if metadata.is_empty() {
                        obj.make_field_absent(sf("sfMPTokenMetadata"));
                    } else {
                        obj.set_stbase(protocol::STBlob::from_buffer(
                            sf("sfMPTokenMetadata"),
                            basics::buffer::Buffer::from(&metadata[..]),
                        ));
                    }
                }
                if sttx.is_field_present(sf("sfDomainID")) {
                    let domain_id = sttx.get_field_h256(sf("sfDomainID"));
                    if domain_id.is_zero() {
                        if obj.is_field_present(sf("sfDomainID")) {
                            obj.make_field_absent(sf("sfDomainID"));
                        }
                    } else {
                        obj.set_field_h256(sf("sfDomainID"), domain_id);
                    }
                }
                if let Some(immutable_flags) = immutable_flags {
                    let current = obj.get_field_u32(sf("sfImmutableFlags"));
                    obj.set_field_u32(sf("sfImmutableFlags"), current | immutable_flags);
                }
                if sttx.is_field_present(sf("sfIssuerEncryptionKey")) {
                    obj.set_stbase(protocol::STBlob::from_buffer(
                        sf("sfIssuerEncryptionKey"),
                        basics::buffer::Buffer::from(
                            &sttx.get_field_vl(sf("sfIssuerEncryptionKey"))[..],
                        ),
                    ));
                }
                if sttx.is_field_present(sf("sfAuditorEncryptionKey")) {
                    obj.set_stbase(protocol::STBlob::from_buffer(
                        sf("sfAuditorEncryptionKey"),
                        basics::buffer::Buffer::from(
                            &sttx.get_field_vl(sf("sfAuditorEncryptionKey"))[..],
                        ),
                    ));
                }
                if view
                    .update(Arc::new(STLedgerEntry::from_stobject(
                        obj,
                        *target_sle.key(),
                    )))
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
            }
            Ter::TES_SUCCESS
        }
        TxType::MPTOKEN_AUTHORIZE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let holder = sttx
                .is_field_present(sf("sfHolder"))
                .then(|| sttx.get_account_id(sf("sfHolder")));
            let mptid = sttx.get_field_h192(sf("sfMPTokenIssuanceID"));
            let flags = sttx.get_field_u32(sf("sfFlags"));
            let unauthorize = (flags & protocol::tfMPTUnauthorize) != 0;

            let issuance_keylet = protocol::mpt_issuance_keylet_from_mptid(mptid);
            let acct = match view.peek(protocol::account_keylet(Uint160::from_void(account.data())))
            {
                Ok(Some(acct)) => acct,
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if let Some(holder) = holder {
                // Holder existence, pseudo-account status, require-auth, and
                // issuer permission are immutable preclaim decisions. Pinned
                // authorizeMPToken only defends its preclaim-proven apply
                // targets with internal codes.
                let issuance = match view.peek(issuance_keylet) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TEC_INTERNAL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let issuer = issuance.get_account_id(sf("sfIssuer"));
                if account != issuer {
                    return Ter::TEC_INTERNAL;
                }
                let holder_keylet =
                    protocol::mptoken_keylet_from_mptid(mptid, Uint160::from_void(holder.data()));
                let holder_token = match view.peek(holder_keylet) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TEC_INTERNAL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let mut obj = holder_token.clone_as_object();
                let mut token_flags = obj.get_field_u32(sf("sfFlags"));
                if unauthorize {
                    token_flags &= !protocol::lsfMPTAuthorized;
                } else {
                    token_flags |= protocol::lsfMPTAuthorized;
                }
                obj.set_field_u32(sf("sfFlags"), token_flags);
                if view
                    .update(Arc::new(STLedgerEntry::from_stobject(
                        obj,
                        *holder_token.key(),
                    )))
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
                return Ter::TES_SUCCESS;
            }

            let token_keylet =
                protocol::mptoken_keylet_from_mptid(mptid, Uint160::from_void(account.data()));
            if unauthorize {
                let token = match view.peek(token_keylet) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TEC_INTERNAL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let locked_amount = if token.is_field_present(sf("sfLockedAmount")) {
                    token.get_field_u64(sf("sfLockedAmount"))
                } else {
                    0
                };
                if token.get_field_u64(sf("sfMPTAmount")) != 0
                    || (view
                        .rules()
                        .enabled(&protocol::feature_id("fixCleanup3_1_3"))
                        && locked_amount != 0)
                {
                    return Ter::TEC_INTERNAL;
                }
                let owner_node = token.get_field_u64(sf("sfOwnerNode"));
                let owner_dir = protocol::owner_dir_keylet(Uint160::from_void(account.data()));
                match ledger::dir_remove(view, &owner_dir, owner_node, *token.key(), false) {
                    Ok(true) => {}
                    Ok(false) => return Ter::TEC_INTERNAL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                }
                if ledger::decrease_owner_count_for_object(view, &acct, &token, 1).is_err() {
                    return Ter::TEF_BAD_LEDGER;
                }
                if view.erase(token).is_err() {
                    return Ter::TEF_BAD_LEDGER;
                }
                return Ter::TES_SUCCESS;
            }
            let sponsor_sle = match check_cash_reserve_sponsor(view, sttx) {
                Ok(sponsor) => sponsor,
                Err(ter) => return ter,
            };
            if sponsor_sle.is_some() || acct.get_field_u32(sf("sfOwnerCount")) >= 2 {
                let has_reserve = match check_cash_has_object_reserve(
                    view,
                    &acct,
                    pre_fee_balance_drops,
                    sponsor_sle.as_ref(),
                ) {
                    Ok(value) => value,
                    Err(ter) => return ter,
                };
                if !has_reserve {
                    return Ter::TEC_INSUFFICIENT_RESERVE;
                }
            }
            // Defensive doApply validation occurs after reserve checking in
            // pinned authorizeMPToken. Preclaim already proved non-issuer and
            // target absence; violations here are internal inconsistencies.
            let issuance = match view.peek(issuance_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if issuance.get_account_id(sf("sfIssuer")) == account {
                return Ter::TEC_INTERNAL;
            }
            match view.peek(token_keylet) {
                Ok(Some(_)) => return Ter::TEC_INTERNAL,
                Ok(None) => {}
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
            let mut sle = STLedgerEntry::new(token_keylet);
            sle.set_account_id(sf("sfAccount"), account);
            sle.set_field_h192(sf("sfMPTokenIssuanceID"), mptid);
            sle.set_field_u64(sf("sfMPTAmount"), 0);
            sle.set_field_u32(sf("sfFlags"), 0);
            if let Some(sponsor_sle) = sponsor_sle.as_ref() {
                sle.set_account_id(sf("sfSponsor"), sponsor_sle.get_account_id(sf("sfAccount")));
            }
            let owner_dir = protocol::owner_dir_keylet(Uint160::from_void(account.data()));
            let page = match ledger::dir_insert(
                view,
                &owner_dir,
                token_keylet.key,
                &describe_owner_dir(account),
            ) {
                Ok(Some(page)) => page,
                Ok(None) => return Ter::TEC_DIR_FULL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            sle.set_field_u64(sf("sfOwnerNode"), page);
            if view.insert(Arc::new(sle)).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            if ledger::increase_owner_count_for_object(view, &acct, sponsor_sle.as_ref()).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }

        // --- Permissioned domains ---
        TxType::PERMISSIONED_DOMAIN_SET => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let tx_credentials = sttx
                .get_field_array(sf("sfAcceptedCredentials"))
                .iter()
                .map(|credential| PermissionedDomainCredential {
                    issuer: credential.get_account_id(sf("sfIssuer")),
                    credential_type: credential.get_field_vl(sf("sfCredentialType")),
                })
                .collect();
            let existing_domain_id = sttx
                .is_field_present(sf("sfDomainID"))
                .then(|| sttx.get_field_h256(sf("sfDomainID")));
            // Existence and ownership are immutable preclaim decisions.
            // Pinned doApply only treats a preclaim-proven update target that
            // has disappeared as tefINTERNAL through the apply sink.
            let domain_sequence = if view.rules().enabled(&protocol::fix_cleanup_3_1_3()) {
                sttx.get_seq_value()
            } else {
                sttx.get_field_u32(sf("sfSequence"))
            };
            let mut sink = ViewBackedPermissionedDomainSetSink::new(
                view,
                account,
                domain_sequence,
                existing_domain_id,
            );
            let result = run_permissioned_domain_set_do_apply(
                tx_credentials,
                existing_domain_id.is_some(),
                &mut sink,
            );
            sink.failure.unwrap_or(result)
        }
        TxType::PERMISSIONED_DOMAIN_DELETE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let domain_id = sttx.get_field_h256(sf("sfDomainID"));
            // PermissionedDomainDelete::preclaim has already established
            // existence and ownership.  doApply must not repeat policy checks.
            let mut sink = ViewBackedPermissionedDomainDeleteSink {
                view,
                account,
                domain_id,
                failure: None,
            };
            let result = run_permissioned_domain_delete_do_apply(&mut sink);
            sink.failure.unwrap_or(result)
        }

        // --- Credentials ---
        TxType::CREDENTIAL_CREATE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let subject = sttx.get_account_id(sf("sfSubject"));
            let cred_type = if sttx.is_field_present(sf("sfCredentialType")) {
                sttx.get_field_vl(sf("sfCredentialType"))
            } else {
                vec![]
            };
            let cred_keylet = protocol::credential_keylet(
                Uint160::from_void(subject.data()),
                Uint160::from_void(account.data()),
                &cred_type,
            );

            let issuer_sle =
                match view.peek(protocol::account_keylet(Uint160::from_void(account.data()))) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TEF_INTERNAL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
            // CredentialCreate::preclaim has already proved that the subject
            // exists, the key is absent, and (under fixCleanup3_3_0) the
            // subject is not a pseudo-account.  Pinned doApply does not repeat
            // those mutable-state policy checks.
            if sttx.is_field_present(sf("sfExpiration")) {
                let expiration = sttx.get_field_u32(sf("sfExpiration"));
                if view.header().parent_close_time > expiration {
                    return Ter::TEC_EXPIRED;
                }
            }
            let sponsor_sle = match check_cash_reserve_sponsor(view, sttx) {
                Ok(sponsor) => sponsor,
                Err(ter) => return ter,
            };
            let has_reserve = match check_cash_has_object_reserve(
                view,
                &issuer_sle,
                pre_fee_balance_drops,
                sponsor_sle.as_ref(),
            ) {
                Ok(has_reserve) => has_reserve,
                Err(ter) => return ter,
            };
            if !has_reserve {
                return Ter::TEC_INSUFFICIENT_RESERVE;
            }

            let mut sle = STLedgerEntry::new(cred_keylet);
            sle.set_account_id(sf("sfIssuer"), account);
            sle.set_account_id(sf("sfSubject"), subject);
            if sttx.is_field_present(sf("sfCredentialType")) {
                sle.set_stbase(protocol::STBlob::from_buffer(
                    sf("sfCredentialType"),
                    basics::buffer::Buffer::from(&sttx.get_field_vl(sf("sfCredentialType"))[..]),
                ));
            }
            if sttx.is_field_present(sf("sfExpiration")) {
                sle.set_field_u32(sf("sfExpiration"), sttx.get_field_u32(sf("sfExpiration")));
            }
            if sttx.is_field_present(sf("sfURI")) {
                sle.set_stbase(protocol::STBlob::from_buffer(
                    sf("sfURI"),
                    basics::buffer::Buffer::from(&sttx.get_field_vl(sf("sfURI"))[..]),
                ));
            }
            let issuer_dir = protocol::owner_dir_keylet(Uint160::from_void(account.data()));
            let issuer_page = match ledger::dir_insert(
                view,
                &issuer_dir,
                cred_keylet.key,
                &describe_owner_dir(account),
            ) {
                Ok(Some(page)) => page,
                Ok(None) => return Ter::TEC_DIR_FULL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            sle.set_field_u64(sf("sfIssuerNode"), issuer_page);
            if let Some(sponsor) = sponsor_sle.as_ref() {
                sle.set_account_id(sf("sfSponsor"), sponsor.get_account_id(sf("sfAccount")));
            }
            if ledger::increase_owner_count_for_object(view, &issuer_sle, sponsor_sle.as_ref())
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }

            if subject == account {
                sle.set_field_u32(sf("sfFlags"), protocol::lsfAccepted);
            } else {
                let subject_dir = protocol::owner_dir_keylet(Uint160::from_void(subject.data()));
                let subject_page = match ledger::dir_insert(
                    view,
                    &subject_dir,
                    cred_keylet.key,
                    &describe_owner_dir(subject),
                ) {
                    Ok(Some(page)) => page,
                    Ok(None) => return Ter::TEC_DIR_FULL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                sle.set_field_u64(sf("sfSubjectNode"), subject_page);
                // Note: subject OwnerCount is NOT incremented on create.
                // It's incremented on accept (ownership transfer from issuer to subject).
            }

            if view.insert(Arc::new(sle)).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }

            Ter::TES_SUCCESS
        }
        TxType::CREDENTIAL_ACCEPT => {
            let subject = sttx.get_account_id(sf("sfAccount"));
            let issuer = sttx.get_account_id(sf("sfIssuer"));
            let cred_type = if sttx.is_field_present(sf("sfCredentialType")) {
                sttx.get_field_vl(sf("sfCredentialType"))
            } else {
                vec![]
            };
            let cred_keylet = protocol::credential_keylet(
                Uint160::from_void(subject.data()),
                Uint160::from_void(issuer.data()),
                &cred_type,
            );

            let cred_sle = match view.peek(cred_keylet) {
                Ok(Some(sle)) => sle,
                // Existence was established in CredentialAccept::preclaim.
                Ok(None) => return Ter::TEF_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let subject_sle =
                match view.peek(protocol::account_keylet(Uint160::from_void(subject.data()))) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TEF_INTERNAL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
            let issuer_sle =
                match view.peek(protocol::account_keylet(Uint160::from_void(issuer.data()))) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TEF_INTERNAL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
            let sponsor_sle = match check_cash_reserve_sponsor(view, sttx) {
                Ok(sponsor) => sponsor,
                Err(ter) => return ter,
            };
            let has_reserve = match check_cash_has_object_reserve(
                view,
                &subject_sle,
                pre_fee_balance_drops,
                sponsor_sle.as_ref(),
            ) {
                Ok(has_reserve) => has_reserve,
                Err(ter) => return ter,
            };
            if !has_reserve {
                return Ter::TEC_INSUFFICIENT_RESERVE;
            }

            // CredentialAccept checks the acceptor's (possibly sponsored)
            // reserve before its expired-credential cleanup. This ordering is
            // observable when an expired credential is submitted by an
            // under-reserved account.
            if ledger::credential_helpers::check_expired(&cred_sle, view.header().parent_close_time)
            {
                let result = ledger::credential_helpers::delete_sle(view, cred_sle)
                    .unwrap_or(Ter::TEF_BAD_LEDGER);
                return if result == Ter::TES_SUCCESS {
                    Ter::TEC_EXPIRED
                } else {
                    result
                };
            }

            let mut obj = cred_sle.clone_as_object();
            obj.set_field_u32(sf("sfFlags"), protocol::lsfAccepted);
            obj.make_field_absent(sf("sfSponsor"));
            if let Some(sponsor) = sponsor_sle.as_ref() {
                obj.set_account_id(sf("sfSponsor"), sponsor.get_account_id(sf("sfAccount")));
            }
            if ledger::decrease_owner_count_for_object(view, &issuer_sle, &cred_sle, 1).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
            // The create sponsor and accept sponsor may be the same account.
            // Refresh after releasing the issuer-side reserve so the second
            // counter update does not apply to a stale pre-release snapshot.
            let refreshed_sponsor = if let Some(sponsor) = sponsor_sle.as_ref() {
                let sponsor_id = sponsor.get_account_id(sf("sfAccount"));
                match view.peek(protocol::account_keylet(Uint160::from_void(
                    sponsor_id.data(),
                ))) {
                    Ok(Some(sle)) => Some(sle),
                    _ => return Ter::TEF_BAD_LEDGER,
                }
            } else {
                None
            };
            let refreshed_subject =
                match view.peek(protocol::account_keylet(Uint160::from_void(subject.data()))) {
                    Ok(Some(sle)) => sle,
                    _ => return Ter::TEF_BAD_LEDGER,
                };
            if ledger::increase_owner_count_for_object(
                view,
                &refreshed_subject,
                refreshed_sponsor.as_ref(),
            )
            .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            if view
                .update(Arc::new(STLedgerEntry::from_stobject(obj, *cred_sle.key())))
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
            Ter::TES_SUCCESS
        }
        TxType::CREDENTIAL_DELETE => {
            let account = sttx.get_account_id(sf("sfAccount"));
            let subject = if sttx.is_field_present(sf("sfSubject")) {
                sttx.get_account_id(sf("sfSubject"))
            } else {
                account
            };
            let issuer = if sttx.is_field_present(sf("sfIssuer")) {
                sttx.get_account_id(sf("sfIssuer"))
            } else {
                account
            };
            let cred_type = if sttx.is_field_present(sf("sfCredentialType")) {
                sttx.get_field_vl(sf("sfCredentialType"))
            } else {
                vec![]
            };
            let cred_keylet = protocol::credential_keylet(
                Uint160::from_void(subject.data()),
                Uint160::from_void(issuer.data()),
                &cred_type,
            );
            let cred_sle = match view.peek(cred_keylet) {
                Ok(Some(sle)) => sle,
                // Existence was established in CredentialDelete::preclaim.
                Ok(None) => return Ter::TEF_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if account != subject
                && account != issuer
                && !ledger::credential_helpers::check_expired(
                    &cred_sle,
                    view.header().parent_close_time,
                )
            {
                return Ter::TEC_NO_PERMISSION;
            }
            ledger::credential_helpers::delete_sle(view, cred_sle).unwrap_or(Ter::TEF_BAD_LEDGER)
        }

        // --- AMM Clawback ---
        TxType::AMM_CLAWBACK => {
            let pre_fee_balance_drops = match require_pre_fee_balance(pre_fee_balance_drops) {
                Ok(balance) => balance,
                Err(ter) => return ter,
            };
            let prior_balance = XRPAmount::from_drops(pre_fee_balance_drops);
            let issuer = sttx.get_account_id(sf("sfAccount"));
            let holder = sttx.get_account_id(sf("sfHolder"));
            let asset1 = tx_amm_asset(sttx, sf("sfAsset"));
            let asset2 = tx_amm_asset(sttx, sf("sfAsset2"));
            let amount = optional_tx_amount(sttx, sf("sfAmount"));
            let mut mpt_gate_assets = vec![asset1, asset2];
            if let Some(amount) = &amount {
                mpt_gate_assets.push(amount.asset());
            }
            let mpt_gate = check_amm_mptokens_v2_gate(view, &mpt_gate_assets);
            if mpt_gate != Ter::TES_SUCCESS {
                return mpt_gate;
            }
            if !sttx.is_field_present(sf("sfAsset"))
                || !sttx.is_field_present(sf("sfAsset2"))
                || (asset1.native() && asset2.native() && sttx.is_field_present(sf("sfAmount")))
            {
                return legacy_amm_clawback_direct_dispatch(view, sttx);
            }
            if issuer == holder {
                return Ter::TEM_MALFORMED;
            }
            if asset1.native() || asset1.issuer() != issuer {
                return Ter::TEM_MALFORMED;
            }
            let claw_two_assets = sttx.get_flags() & protocol::AMM_CLAWBACK_TWO_ASSETS_FLAG != 0;
            if claw_two_assets && asset1.issuer() != asset2.issuer() {
                return Ter::TEM_INVALID_FLAG;
            }
            if let Some(amount) = &amount {
                if amount.asset() != asset1 {
                    return Ter::TEM_BAD_AMOUNT;
                }
                if amount.signum() <= 0 {
                    return Ter::TEM_BAD_AMOUNT;
                }
            }

            let issuer_sle =
                match view.peek(protocol::account_keylet(Uint160::from_void(issuer.data()))) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TER_NO_ACCOUNT,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
            match view.peek(protocol::account_keylet(Uint160::from_void(holder.data()))) {
                Ok(Some(_)) => {}
                Ok(None) => return Ter::TER_NO_ACCOUNT,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
            let amm_keylet = protocol::keylet::amm(asset1, asset2);
            let amm_sle = match view.peek(amm_keylet) {
                Ok(Some(sle)) => sle,
                Ok(None) => return Ter::TER_NO_AMM,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            if !view.rules().enabled(&protocol::feature_id("MPTokensV2"))
                && (!issuer_sle.is_flag(protocol::lsfAllowTrustLineClawback)
                    || issuer_sle.is_flag(protocol::lsfNoFreeze))
            {
                return Ter::TEC_NO_PERMISSION;
            }
            let asset1_allowed =
                match amm_clawback_asset_allowed(view, &issuer, &issuer_sle, asset1) {
                    Ok(allowed) => allowed,
                    Err(ter) => return ter,
                };
            if !asset1_allowed {
                return Ter::TEC_NO_PERMISSION;
            }
            if claw_two_assets {
                let asset2_allowed =
                    match amm_clawback_asset_allowed(view, &issuer, &issuer_sle, asset2) {
                        Ok(allowed) => allowed,
                        Err(ter) => return ter,
                    };
                if !asset2_allowed {
                    return Ter::TEC_NO_PERMISSION;
                }
            }

            let amm_account = amm_sle.get_account_id(sf("sfAccount"));
            let account_keylet = protocol::account_keylet(Uint160::from_void(amm_account.data()));
            match view.peek(account_keylet) {
                Ok(Some(_)) => {}
                Ok(None) => return Ter::TEC_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
            let mut lp_total = amm_sle.get_field_amount(sf("sfLPTokenBalance"));
            if lp_total.signum() == 0 {
                return Ter::TEC_AMM_EMPTY;
            }
            let fix_amm_clawback_rounding = view
                .rules()
                .enabled(&protocol::feature_id("fixAMMClawbackRounding"));
            let mut pool1 = None;
            let mut pool2 = None;
            let mut holder_lp = None;
            for read in amm_clawback_balance_read_plan(fix_amm_clawback_rounding) {
                match read {
                    AMMClawbackBalanceRead::PreAdjustHolder => {
                        let initial_holder_lp = match amm_lp_holds_in_view(view, &amm_sle, holder) {
                            Ok(Some(amount)) => amount,
                            Ok(None) => return Ter::TEC_AMM_BALANCE,
                            Err(_) => return Ter::TEF_BAD_LEDGER,
                        };
                        if initial_holder_lp.signum() == 0 {
                            return Ter::TEC_AMM_BALANCE;
                        }
                        let only_liquidity_provider =
                            ledger::is_only_liquidity_provider(view, lp_total.issue(), holder);
                        if !only_liquidity_provider.has_value() {
                            return *only_liquidity_provider.error();
                        }
                        let tolerance = match RuntimeNumber::try_from_external_parts(
                            1,
                            -3,
                            basics::number::get_mantissa_scale(),
                        ) {
                            Ok(tolerance) => tolerance,
                            Err(_) => return Ter::TEF_EXCEPTION,
                        };
                        if *only_liquidity_provider.value()
                            && !ledger::within_relative_distance_amount(
                                initial_holder_lp.clone(),
                                lp_total.clone(),
                                tolerance,
                            )
                        {
                            return Ter::TEC_AMM_INVALID_TOKENS;
                        }
                        if *only_liquidity_provider.value() {
                            lp_total = initial_holder_lp;
                        }
                    }
                    AMMClawbackBalanceRead::Pool => {
                        let first =
                            amm_holds_or_return!(view, &amm_account, asset1, sf("sfAmount"));
                        let second =
                            amm_holds_or_return!(view, &amm_account, asset2, sf("sfAmount2"));
                        if first.signum() <= 0 || second.signum() <= 0 {
                            return Ter::TEC_INTERNAL;
                        }
                        pool1 = Some(first);
                        pool2 = Some(second);
                    }
                    AMMClawbackBalanceRead::PostAdjustHolder => {
                        let balance = match amm_lp_holds_in_view(view, &amm_sle, holder) {
                            Ok(Some(amount)) => amount,
                            Ok(None) => return Ter::TEC_AMM_BALANCE,
                            Err(_) => return Ter::TEF_BAD_LEDGER,
                        };
                        if balance.signum() == 0 {
                            return Ter::TEC_AMM_BALANCE;
                        }
                        holder_lp = Some(balance);
                    }
                }
            }
            let (Some(pool1), Some(pool2), Some(holder_lp)) = (pool1, pool2, holder_lp) else {
                return Ter::TEF_INTERNAL;
            };

            let math = match amm_clawback_math(
                amount.as_ref(),
                &pool1,
                &pool2,
                &lp_total,
                &holder_lp,
                view.rules(),
            ) {
                Ok(math) => math,
                Err(ter) => return ter,
            };
            let lp_issue = lp_total.issue();
            let Some(amount1) = math.amount1.as_ref() else {
                return Ter::TEC_INTERNAL;
            };
            let Some(amount2) = math.amount2.as_ref() else {
                return Ter::TEC_INTERNAL;
            };

            let prepare = amm_prepare_withdraw_holding(
                view,
                sttx,
                &holder,
                amount1.asset(),
                prior_balance,
                Some(issuer),
            );
            if prepare != Ter::TES_SUCCESS {
                return prepare;
            }
            let res = amm_withdraw_asset(view, &amm_account, &holder, amount1);
            if res != Ter::TES_SUCCESS {
                return res;
            }
            let prepare = amm_prepare_withdraw_holding(
                view,
                sttx,
                &holder,
                amount2.asset(),
                prior_balance,
                Some(issuer),
            );
            if prepare != Ter::TES_SUCCESS {
                return prepare;
            }
            let res = amm_withdraw_asset(view, &amm_account, &holder, amount2);
            if res != Ter::TES_SUCCESS {
                return res;
            }
            let res = crate::state::amm_bid_apply::redeem_iou_pub(
                view,
                &holder,
                &math.lp_tokens,
                &lp_issue,
            );
            if res != Ter::TES_SUCCESS {
                return res;
            }
            if view
                .rules()
                .enabled(&protocol::feature_id("fixCleanup3_3_0"))
                && view.rules().enabled(&protocol::feature_id("fixAMMv1_3"))
            {
                let remaining1 = amm_holds_or_return!(view, &amm_account, asset1, sf("sfAmount"));
                let remaining2 = amm_holds_or_return!(view, &amm_account, asset2, sf("sfAmount2"));
                let precision = ledger::check_amm_precision_loss(
                    &remaining1,
                    &remaining2,
                    &math.new_lp_token_balance,
                );
                if precision != Ter::TES_SUCCESS {
                    return precision;
                }
            }
            // Delete AMM if LP balance reaches zero after full clawback.
            // Matches AMMWithdraw's deleteAMMAccountIfEmpty: clean up owner
            // directory entries, remove the AMM SLE, and erase the AMM account.
            // A fully deleted AMM is *not* updated first: rippled's DeletedNode
            // FinalFields retain the pre-clawback LP balance. Only the bounded
            // tecINCOMPLETE cleanup path preserves the object at zero balance.
            let mut update_balance = true;
            if math.new_lp_token_balance.signum() == 0 {
                let delete_result = delete_amm_account(view, &amm_sle);
                if delete_result != Ter::TES_SUCCESS && delete_result != Ter::TEC_INCOMPLETE {
                    return delete_result;
                }
                update_balance = delete_result == Ter::TEC_INCOMPLETE;
            }
            if update_balance {
                let mut obj = amm_sle.clone_as_object();
                obj.set_field_amount(sf("sfLPTokenBalance"), math.new_lp_token_balance.clone());
                if view
                    .update(Arc::new(STLedgerEntry::from_stobject(obj, *amm_sle.key())))
                    .is_err()
                {
                    return Ter::TEF_BAD_LEDGER;
                }
            }

            let res = amm_clawback_send_amount(view, &holder, &issuer, amount1);
            if res != Ter::TES_SUCCESS {
                return res;
            }
            if claw_two_assets {
                let res = amm_clawback_send_amount(view, &holder, &issuer, amount2);
                if res != Ter::TES_SUCCESS {
                    return res;
                }
            }

            Ter::TES_SUCCESS
        }

        // --- NFToken Modify ---
        TxType::NFTOKEN_MODIFY => {
            if !view.rules().enabled(&protocol::feature_id("DynamicNFT")) {
                return Ter::TEM_DISABLED;
            }
            if sttx.is_field_present(sf("sfNFTokenTaxon")) {
                return Ter::TEM_MALFORMED;
            }
            let account = sttx.get_account_id(sf("sfAccount"));
            let owner = if sttx.is_field_present(sf("sfOwner")) {
                sttx.get_account_id(sf("sfOwner"))
            } else {
                account
            };
            // preflight
            if sttx.is_field_present(sf("sfOwner")) && owner == account {
                return Ter::TEM_MALFORMED;
            }
            if sttx.is_field_present(sf("sfURI")) {
                let uri = sttx.get_field_vl(sf("sfURI"));
                if uri.is_empty() || uri.len() > protocol::MAX_TOKEN_URI_LENGTH {
                    return Ter::TEM_MALFORMED;
                }
            }
            let token_id = sttx.get_field_h256(sf("sfNFTokenID"));
            // preclaim: find token
            let page = match nft_find_token_and_page(view, &owner, token_id) {
                Ok(Some((_, page))) => page,
                Ok(None) => return Ter::TEC_NO_ENTRY,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            // check mutable flag
            let nft_flags = protocol::get_nft_flags(token_id);
            if (nft_flags & protocol::nft::FLAG_MUTABLE) == 0 {
                return Ter::TEC_NO_PERMISSION;
            }
            // verify issuer permissions
            let issuer = protocol::get_nft_issuer(token_id);
            if issuer != account {
                let issuer_keylet = protocol::account_keylet(Uint160::from_void(issuer.data()));
                let issuer_sle = match view.peek(issuer_keylet) {
                    Ok(Some(sle)) => sle,
                    Ok(None) => return Ter::TEC_INTERNAL,
                    Err(_) => return Ter::TEF_BAD_LEDGER,
                };
                let minter_matches = issuer_sle.is_field_present(sf("sfNFTokenMinter"))
                    && issuer_sle.get_account_id(sf("sfNFTokenMinter")) == account;
                if !minter_matches {
                    return Ter::TEC_NO_PERMISSION;
                }
            }
            // doApply: change URI on the token in the page
            let tokens = page.get_field_array(sf("sfNFTokens"));
            let mut new_tokens = protocol::STArray::new(sf("sfNFTokens"));
            for token in tokens.iter() {
                let tid = token.get_field_h256(sf("sfNFTokenID"));
                if tid == token_id {
                    let mut modified = token.clone();
                    if sttx.is_field_present(sf("sfURI")) {
                        let uri = sttx.get_field_vl(sf("sfURI"));
                        modified.set_field_vl(sf("sfURI"), &uri);
                    } else if modified.is_field_present(sf("sfURI")) {
                        modified.make_field_absent(sf("sfURI"));
                    }
                    new_tokens.push_back(modified);
                } else {
                    new_tokens.push_back(token.clone());
                }
            }
            let mut obj = page.clone_as_object();
            obj.set_field_array(sf("sfNFTokens"), new_tokens);
            view.update(Arc::new(STLedgerEntry::from_stobject(obj, *page.key())))
                .map_or(Ter::TEF_BAD_LEDGER, |_| Ter::TES_SUCCESS)
        }

        // --- AMMBid: full reference AMMBid::applyBid parity ---
        TxType::AMM_BID => {
            let asset1 = tx_amm_asset(sttx, sf("sfAsset"));
            let asset2 = tx_amm_asset(sttx, sf("sfAsset2"));
            let mpt_gate = check_amm_mptokens_v2_gate(view, &[asset1, asset2]);
            if mpt_gate != Ter::TES_SUCCESS {
                return mpt_gate;
            }
            crate::state::amm_bid_apply::apply_amm_bid(view, sttx)
        }

        // --- Change pseudo-transaction (reference the reference source) ---
        TxType::FEE => {
            let k = protocol::fee_settings_keylet();
            // Match Change::applyFee: a missing fee object is a typed
            // FeeSettings SLE, not a generic STObject. The latter serializes
            // without sfLedgerEntryType and cannot be decoded by the accepted
            // ledger's state-batch path.
            let existing = match view.peek(k) {
                Ok(existing) => existing,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let mut obj = existing.as_ref().map_or_else(
                || protocol::STLedgerEntry::new(k).clone_as_object(),
                |entry| entry.clone_as_object(),
            );
            // `Change::applyFee` selects the format from the ledger rules, not
            // from whichever fields happen to be present on the transaction.
            // The pseudo-transaction preflight has already enforced the exact
            // required/forbidden shape for this rule set.
            if view.rules().enabled(&protocol::feature_xrp_fees()) {
                obj.set_field_amount(
                    sf("sfBaseFeeDrops"),
                    sttx.get_field_amount(sf("sfBaseFeeDrops")),
                );
                obj.set_field_amount(
                    sf("sfReserveBaseDrops"),
                    sttx.get_field_amount(sf("sfReserveBaseDrops")),
                );
                obj.set_field_amount(
                    sf("sfReserveIncrementDrops"),
                    sttx.get_field_amount(sf("sfReserveIncrementDrops")),
                );
                // Exact `Change::applyFee` XRPFees transition: discard the
                // legacy representation after writing all three drops fields.
                obj.make_field_absent(sf("sfBaseFee"));
                obj.make_field_absent(sf("sfReferenceFeeUnits"));
                obj.make_field_absent(sf("sfReserveBase"));
                obj.make_field_absent(sf("sfReserveIncrement"));
            } else {
                obj.set_field_u64(sf("sfBaseFee"), sttx.get_field_u64(sf("sfBaseFee")));
                obj.set_field_u32(
                    sf("sfReferenceFeeUnits"),
                    sttx.get_field_u32(sf("sfReferenceFeeUnits")),
                );
                obj.set_field_u32(sf("sfReserveBase"), sttx.get_field_u32(sf("sfReserveBase")));
                obj.set_field_u32(
                    sf("sfReserveIncrement"),
                    sttx.get_field_u32(sf("sfReserveIncrement")),
                );
            }
            let sle = Arc::new(protocol::STLedgerEntry::from_stobject(obj, k.key));
            let result = if existing.is_some() {
                view.update(sle)
            } else {
                view.insert(sle)
            };
            if result.is_err() {
                Ter::TEF_BAD_LEDGER
            } else {
                Ter::TES_SUCCESS
            }
        }

        TxType::AMENDMENT => {
            let k = protocol::amendments_keylet();
            let existing = match view.peek(k) {
                Ok(existing) => existing,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let mut obj = if let Some(existing) = existing.as_ref() {
                existing.clone_as_object()
            } else {
                protocol::STLedgerEntry::from_type_and_key(LedgerEntryType::Amendments, k.key)
                    .clone_as_object()
            };
            let amendment = sttx.get_field_h256(sf("sfAmendment"));
            let flags = sttx.get_field_u32(sf("sfFlags"));
            let decoded = existing.as_deref().map(decoded_amendments_entry);
            let outcome = run_change_apply_amendment(
                &ChangeAmendmentFacts {
                    amendment,
                    got_majority: flags & protocol::ENABLE_AMENDMENT_GOT_MAJORITY_FLAG != 0,
                    lost_majority: flags & protocol::ENABLE_AMENDMENT_LOST_MAJORITY_FLAG != 0,
                    parent_close_time: view.parent_close_time().as_seconds(),
                    // The dispatcher has no network-ops handle; ApplicationRoot recomputes
                    // warning/blocking state from every validated ledger. Still feed the
                    // helper the exact registry fact so its outcome remains authoritative.
                    amendment_supported: protocol::registered_feature(&amendment)
                        .is_some_and(protocol::registered_feature_supported),
                },
                decoded.as_ref(),
            );
            if outcome.result != Ter::TES_SUCCESS {
                return outcome.result;
            }
            let Some(decoded) = outcome.amendments_entry else {
                return Ter::TEF_INTERNAL;
            };
            apply_decoded_amendments_entry(&mut obj, &decoded);
            let sle = Arc::new(protocol::STLedgerEntry::from_stobject(obj, k.key));
            let write = if existing.is_some() {
                view.update(sle)
            } else {
                view.insert(sle)
            };
            write.map_or(Ter::TEF_BAD_LEDGER, |_| Ter::TES_SUCCESS)
        }

        TxType::UNL_MODIFY => {
            let k = protocol::negative_unl_keylet();
            let existing = match view.peek(k) {
                Ok(existing) => existing,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let mut obj = if let Some(existing) = existing.as_ref() {
                existing.clone_as_object()
            } else {
                protocol::STLedgerEntry::from_type_and_key(LedgerEntryType::NegativeUnl, k.key)
                    .clone_as_object()
            };
            let validator = sttx
                .is_field_present(sf("sfUNLModifyValidator"))
                .then(|| sttx.get_field_vl(sf("sfUNLModifyValidator")));
            let decoded = existing.as_deref().map(decoded_negative_unl_entry);
            let outcome = run_change_apply_unl_modify(
                &ChangeUnlModifyFacts {
                    is_flag_ledger: protocol::is_flag_ledger(view.seq()),
                    unl_modify_disabling: sttx
                        .is_field_present(sf("sfUNLModifyDisabling"))
                        .then(|| sttx.get_field_u8(sf("sfUNLModifyDisabling"))),
                    ledger_sequence: sttx
                        .is_field_present(sf("sfLedgerSequence"))
                        .then(|| sttx.get_field_u32(sf("sfLedgerSequence"))),
                    current_ledger_sequence: view.seq(),
                    validator_public_key_type_known: validator
                        .as_deref()
                        .is_some_and(|key| protocol::PublicKey::from_slice(key).is_ok()),
                    validator_public_key: validator,
                },
                decoded.as_ref(),
            );
            if outcome.result != Ter::TES_SUCCESS {
                return outcome.result;
            }
            let Some(decoded) = outcome.negative_unl_entry else {
                return Ter::TEF_INTERNAL;
            };
            apply_decoded_negative_unl_entry(&mut obj, &decoded);
            let sle = Arc::new(protocol::STLedgerEntry::from_stobject(obj, k.key));
            let write = if existing.is_some() {
                view.update(sle)
            } else {
                view.insert(sle)
            };
            write.map_or(Ter::TEF_BAD_LEDGER, |_| Ter::TES_SUCCESS)
        }

        TxType::CONFIDENTIAL_MPT_CONVERT
        | TxType::CONFIDENTIAL_MPT_MERGE_INBOX
        | TxType::CONFIDENTIAL_MPT_CONVERT_BACK
        | TxType::CONFIDENTIAL_MPT_SEND
        | TxType::CONFIDENTIAL_MPT_CLAWBACK => crate::state::confidential_mpt::apply(view, sttx),

        _ => Ter::TEM_UNKNOWN,
    }
}

fn paychan_saturating_add<V: ledger::ReadView>(view: &V, lhs: u32, rhs: u32) -> u32 {
    if view
        .rules()
        .enabled(&protocol::feature_id("fixCleanup3_2_0"))
    {
        lhs.saturating_add(rhs)
    } else {
        lhs.wrapping_add(rhs)
    }
}

fn paychan_is_expired<V: ledger::ReadView>(view: &V, expiration: u32) -> bool {
    let close_time = view.header().parent_close_time;
    if view
        .rules()
        .enabled(&protocol::feature_id("fixCleanup3_2_0"))
    {
        close_time > expiration
    } else {
        close_time >= expiration
    }
}

fn close_channel<V: ledger::ApplyView>(
    view: &mut V,
    chan: &Arc<STLedgerEntry>,
    key: Uint256,
) -> Ter {
    let src = chan.get_account_id(sf("sfAccount"));

    // Remove from source owner directory
    let owner_node = chan.get_field_u64(sf("sfOwnerNode"));
    let src_dir = protocol::owner_dir_keylet(Uint160::from_void(src.data()));
    if !ledger::dir_remove(view, &src_dir, owner_node, key, true).unwrap_or(false) {
        return Ter::TEF_BAD_LEDGER;
    }

    // Remove from destination owner directory if present
    if chan.is_field_present(sf("sfDestinationNode")) {
        let dst = chan.get_account_id(sf("sfDestination"));
        let dst_node = chan.get_field_u64(sf("sfDestinationNode"));
        let dst_dir = protocol::owner_dir_keylet(Uint160::from_void(dst.data()));
        if !ledger::dir_remove(view, &dst_dir, dst_node, key, true).unwrap_or(false) {
            return Ter::TEF_BAD_LEDGER;
        }
    }

    // Return remaining funds to source (Amount - Balance)
    let chan_amount = chan.get_field_amount(sf("sfAmount")).xrp().drops();
    let chan_balance = chan.get_field_amount(sf("sfBalance")).xrp().drops();
    let Some(refund) = chan_amount.checked_sub(chan_balance) else {
        return Ter::TEF_BAD_LEDGER;
    };

    let src_keylet = protocol::account_keylet(Uint160::from_void(src.data()));
    let src_sle = match view.peek(src_keylet) {
        Ok(Some(src_sle)) => src_sle,
        Ok(None) => return Ter::TEF_INTERNAL,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    let src_bal = src_sle.get_field_amount(sf("sfBalance")).xrp().drops();
    let Some(updated_balance) = src_bal.checked_add(refund) else {
        return Ter::TEF_BAD_LEDGER;
    };
    let mut src_obj = src_sle.clone_as_object();
    src_obj.set_field_amount(
        sf("sfBalance"),
        STAmount::from_xrp_amount(XRPAmount::from_drops(updated_balance)),
    );
    if view
        .update(Arc::new(STLedgerEntry::from_stobject(
            src_obj,
            *src_sle.key(),
        )))
        .is_err()
    {
        return Ter::TEF_BAD_LEDGER;
    }
    let updated_src = match view.peek(src_keylet) {
        Ok(Some(src_sle)) => src_sle,
        _ => return Ter::TEF_BAD_LEDGER,
    };
    if ledger::decrease_owner_count_for_object(view, &updated_src, chan, 1).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }

    // Erase the channel
    if view.erase(Arc::clone(chan)).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }
    Ter::TES_SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn amm_clawback_balance_reads_follow_pinned_amendment_order() {
        assert_eq!(
            amm_clawback_balance_read_plan(false),
            &[
                AMMClawbackBalanceRead::Pool,
                AMMClawbackBalanceRead::PostAdjustHolder,
            ],
            "legacy applyGuts reads pool state before holder LP"
        );
        assert_eq!(
            amm_clawback_balance_read_plan(true),
            &[
                AMMClawbackBalanceRead::PreAdjustHolder,
                AMMClawbackBalanceRead::Pool,
                AMMClawbackBalanceRead::PostAdjustHolder,
            ],
            "fixAMMClawbackRounding adds the verification read but retains the post-pool read"
        );
    }

    #[test]
    fn lending_reserve_checks_never_use_a_synthetic_pre_fee_balance() {
        assert_eq!(require_pre_fee_balance(Some(123)), Ok(123));
        assert_eq!(require_pre_fee_balance(None), Err(Ter::TEF_BAD_LEDGER));
    }

    #[test]
    fn every_source_reserve_route_requires_the_shared_pre_fee_snapshot() {
        let expected = std::collections::BTreeSet::from([
            TxType::SIGNER_LIST_SET,
            TxType::XCHAIN_COMMIT,
            TxType::XCHAIN_ACCOUNT_CREATE_COMMIT,
            TxType::CHECK_CREATE,
            TxType::CHECK_CASH,
            TxType::CREDENTIAL_CREATE,
            TxType::CREDENTIAL_ACCEPT,
            TxType::DELEGATE_SET,
            TxType::AMM_CLAWBACK,
            TxType::AMM_WITHDRAW,
            TxType::PAYMENT,
            TxType::OFFER_CREATE,
            TxType::TRUST_SET,
            TxType::TICKET_CREATE,
            TxType::ESCROW_FINISH,
            TxType::ESCROW_CANCEL,
            TxType::LOAN_BROKER_SET,
            TxType::LOAN_BROKER_COVER_WITHDRAW,
            TxType::LOAN_SET,
            TxType::DEPOSIT_PREAUTH,
            TxType::PAYCHAN_CREATE,
            TxType::NFTOKEN_MINT,
            TxType::NFTOKEN_CREATE_OFFER,
            TxType::MPTOKEN_AUTHORIZE,
            TxType::MPTOKEN_ISSUANCE_CREATE,
            TxType::VAULT_CREATE,
            TxType::VAULT_DEPOSIT,
            TxType::VAULT_WITHDRAW,
            TxType::SPONSORSHIP_TRANSFER,
        ]);
        let actual = protocol::dispatchable_tx_types()
            .filter(|txn_type| requires_source_pre_fee_balance(*txn_type))
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(actual, expected);
    }

    #[test]
    fn amm_deposit_and_withdraw_math_panics_are_cleanup_3_4_gated() {
        assert_eq!(
            amm_math_panic_ter(&protocol::Rules::new([])),
            Ter::TEF_EXCEPTION
        );
        assert_eq!(
            amm_math_panic_ter(&protocol::Rules::new([protocol::feature_id(
                "fixCleanup3_4_0"
            )])),
            Ter::TEC_AMM_FAILED
        );
    }

    #[test]
    fn mpt_freeze_lookup_preserves_locked_and_storage_error_ters() {
        assert_eq!(frozen_mpt_result(Ok(false)), Ter::TES_SUCCESS);
        assert_eq!(frozen_mpt_result(Ok(true)), Ter::TEC_LOCKED);
        assert_eq!(
            frozen_mpt_result(Err(ledger::ViewError::Conversion(
                "injected MPT freeze SHAMap read failure".to_owned(),
            ))),
            Ter::TEF_BAD_LEDGER
        );
    }

    #[test]
    fn nft_accept_offer_delete_distinguishes_logical_and_storage_failures() {
        assert_eq!(nft_accept_delete_result(Ok(true)), Ter::TES_SUCCESS);
        assert_eq!(nft_accept_delete_result(Ok(false)), Ter::TEC_INTERNAL);
        assert_eq!(
            nft_accept_delete_result(Err(ledger::ViewError::Conversion(
                "injected NFTokenOffer directory write failure".to_owned(),
            ))),
            Ter::TEF_BAD_LEDGER
        );
    }

    #[test]
    fn account_set_disable_master_does_not_treat_signer_read_failure_as_absence() {
        assert_eq!(signer_list_exists_from_lookup(Ok(false)), Ok(false));
        assert_eq!(signer_list_exists_from_lookup(Ok(true)), Ok(true));
        assert_eq!(
            signer_list_exists_from_lookup(Err(ledger::ViewError::Conversion(
                "injected signer-list SHAMap read failure".to_owned(),
            ))),
            Err(Ter::TEF_BAD_LEDGER)
        );
    }

    #[test]
    fn offer_cancel_source_lookup_distinguishes_absence_from_storage_failure() {
        let account = AccountID::from_array([0x17; 20]);
        let present = Arc::new(STLedgerEntry::new(protocol::account_keylet(
            Uint160::from_void(account.data()),
        )));
        assert_eq!(
            required_source_account_from_lookup(Ok(Some(present))),
            Ok(())
        );
        assert_eq!(
            required_source_account_from_lookup(Ok(None)),
            Err(Ter::TEF_INTERNAL)
        );
        assert_eq!(
            required_source_account_from_lookup(Err(ledger::ViewError::Conversion(
                "injected OfferCancel source SHAMap read failure".to_owned(),
            ))),
            Err(Ter::TEF_BAD_LEDGER)
        );
    }

    #[test]
    fn delegate_reserve_balance_lookup_fails_closed_on_missing_and_read_error() {
        let account = AccountID::from_array([2_u8; 20]);
        let keylet = protocol::account_keylet(Uint160::from_void(account.data()));
        let mut present = STLedgerEntry::new(keylet);
        present.set_field_amount(
            sf("sfBalance"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(123)),
        );
        assert_eq!(
            delegate_reserve_balance_from_lookup(Ok(Some(Arc::new(present)))),
            Ok(123)
        );
        assert_eq!(
            delegate_reserve_balance_from_lookup(Ok(None)),
            Err(Ter::TEF_INTERNAL)
        );
        assert_eq!(
            delegate_reserve_balance_from_lookup(Err(ledger::ViewError::Conversion(
                "injected delegate account read failure".to_owned(),
            ))),
            Err(Ter::TEF_BAD_LEDGER)
        );
    }

    #[test]
    fn delegate_apply_failure_overrides_the_trait_shell_result() {
        assert_eq!(
            finish_delegate_apply(Ter::TES_SUCCESS, Some(Ter::TEF_BAD_LEDGER)),
            Ter::TEF_BAD_LEDGER
        );
        assert_eq!(
            finish_delegate_apply(Ter::TEC_DIR_FULL, Some(Ter::TEF_BAD_LEDGER)),
            Ter::TEF_BAD_LEDGER
        );
        assert_eq!(
            finish_delegate_apply(Ter::TES_SUCCESS, None),
            Ter::TES_SUCCESS
        );
    }

    fn iou_amount(issue: protocol::Issue, value: i64) -> STAmount {
        STAmount::from_iou_amount(
            protocol::sf_generic(),
            IOUAmount::from_parts(value, 0).expect("canonical IOU fixture"),
            issue,
        )
    }

    #[test]
    fn amm_clawback_zero_rounded_pool_leg_is_cleanup_3_4_gated() {
        let issuer = AccountID::from_array([0x31; 20]);
        let amm = AccountID::from_array([0x32; 20]);
        let usd = protocol::Issue::new(protocol::currency_from_string("USD"), issuer);
        let lp = protocol::Issue::new(protocol::currency_from_string("LPT"), amm);
        let pool1 = iou_amount(usd, 100);
        let pool2 = STAmount::from_xrp_amount(XRPAmount::from_drops(1));
        let lp_total = iou_amount(lp, 100);
        let holder_lp = lp_total.clone();
        let requested = iou_amount(usd, 10);

        let legacy = amm_clawback_math(
            Some(&requested),
            &pool1,
            &pool2,
            &lp_total,
            &holder_lp,
            protocol::Rules::new([protocol::feature_id("fixAMMClawbackRounding")]),
        )
        .expect("legacy behavior permits the asymmetric zero leg");
        assert_eq!(
            legacy.amount2.expect("second pool leg").signum(),
            0,
            "the fixture must exercise the exact rounded-to-zero branch"
        );

        assert_eq!(
            amm_clawback_math(
                Some(&requested),
                &pool1,
                &pool2,
                &lp_total,
                &holder_lp,
                protocol::Rules::new([
                    protocol::feature_id("fixAMMClawbackRounding"),
                    protocol::feature_id("fixCleanup3_4_0"),
                ]),
            ),
            Err(Ter::TEC_AMM_FAILED)
        );
    }
}
