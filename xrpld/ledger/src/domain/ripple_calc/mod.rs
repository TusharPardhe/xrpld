//! RippleCalc engine — port of reference `path::RippleCalc::rippleCalculate`.

mod builder;

#[allow(dead_code)]
mod selection;
mod step;
pub use step::OfferCrossing;
mod strand;

use crate::read_view::ViewError;
use crate::views::apply_view::ApplyView;
use basics::base_uint::{Uint160, Uint256};
use protocol::{
    AccountID, Amounts, Asset, Quality, STAmount, STLedgerEntry, STPathSet, Ter,
    get_field_by_symbol, is_tes_success,
};
use std::sync::Arc;

use self::strand::{build_explicit_strand, execute_direct_strand};

#[derive(Debug, Clone)]
pub struct RippleCalcInput {
    pub partial_payment_allowed: bool,
    pub default_paths_allowed: bool,
    pub limit_quality: bool,
    pub is_ledger_open: bool,
    pub domain_id: Option<Uint256>,
}

#[derive(Debug, Clone)]
pub struct RippleCalcOutput {
    pub result: Ter,
    pub actual_amount_in: STAmount,
    pub actual_amount_out: STAmount,
}

const QUALITY_ONE: u32 = 1_000_000_000;

fn sf(name: &str) -> &'static protocol::SField {
    get_field_by_symbol(name)
}

fn account_to_uint160(account: &AccountID) -> Uint160 {
    Uint160::from_void(account.data())
}

/// Handle XRP→XRP payments that go through rippleCalculate.
/// In reference, the flow engine builds a strand with XRP endpoint steps and
/// executes a direct transfer. We replicate that behavior here.
fn handle_xrp_to_xrp_flow<V: ApplyView>(
    view: &mut V,
    max_source_amount: &STAmount,
    dst_amount: &STAmount,
    dst_account: &AccountID,
    src_account: &AccountID,
    input: &RippleCalcInput,
) -> Result<RippleCalcOutput, ViewError> {
    // The amount to deliver is min(dst_amount, max_source_amount).
    let deliver = if dst_amount.xrp().drops() <= max_source_amount.xrp().drops() {
        dst_amount.clone()
    } else if input.partial_payment_allowed {
        max_source_amount.clone()
    } else {
        // Can't deliver full amount and partial not allowed
        return Ok(RippleCalcOutput {
            result: Ter::TEC_PATH_DRY,
            actual_amount_in: max_source_amount.zeroed(),
            actual_amount_out: dst_amount.zeroed(),
        });
    };

    let deliver_drops = deliver.xrp().drops();
    if deliver_drops <= 0 {
        return Ok(RippleCalcOutput {
            result: Ter::TEC_PATH_DRY,
            actual_amount_in: max_source_amount.zeroed(),
            actual_amount_out: dst_amount.zeroed(),
        });
    }

    // Check source has sufficient balance (after fee was already deducted)
    let src_keylet = protocol::account_keylet(account_to_uint160(src_account));
    let Some(src_sle) = view.peek(src_keylet)? else {
        return Ok(RippleCalcOutput {
            result: Ter::TER_NO_ACCOUNT,
            actual_amount_in: max_source_amount.zeroed(),
            actual_amount_out: dst_amount.zeroed(),
        });
    };
    let src_balance = src_sle.get_field_amount(sf("sfBalance")).xrp().drops();
    if src_balance < deliver_drops {
        if input.partial_payment_allowed && src_balance > 0 {
            // Partial: deliver what we can
            let actual_deliver = src_balance;
            // Transfer XRP
            let mut src_obj = src_sle.clone_as_object();
            src_obj.set_field_amount(
                sf("sfBalance"),
                STAmount::from_xrp_amount(protocol::XRPAmount::from_drops(
                    src_balance - actual_deliver,
                )),
            );
            view.update(Arc::new(protocol::STLedgerEntry::from_stobject(
                src_obj,
                *src_sle.key(),
            )))?;

            let dst_keylet = protocol::account_keylet(account_to_uint160(dst_account));
            if let Some(dst_sle) = view.peek(dst_keylet)? {
                let dst_balance = dst_sle.get_field_amount(sf("sfBalance")).xrp().drops();
                let mut dst_obj = dst_sle.clone_as_object();
                dst_obj.set_field_amount(
                    sf("sfBalance"),
                    STAmount::from_xrp_amount(protocol::XRPAmount::from_drops(
                        dst_balance + actual_deliver,
                    )),
                );
                view.update(Arc::new(protocol::STLedgerEntry::from_stobject(
                    dst_obj,
                    *dst_sle.key(),
                )))?;
            }

            return Ok(RippleCalcOutput {
                result: Ter::TES_SUCCESS,
                actual_amount_in: STAmount::from_xrp_amount(protocol::XRPAmount::from_drops(
                    actual_deliver,
                )),
                actual_amount_out: STAmount::from_xrp_amount(protocol::XRPAmount::from_drops(
                    actual_deliver,
                )),
            });
        }
        return Ok(RippleCalcOutput {
            result: Ter::TEC_PATH_DRY,
            actual_amount_in: max_source_amount.zeroed(),
            actual_amount_out: dst_amount.zeroed(),
        });
    }

    // Transfer XRP: debit source, credit destination
    let mut src_obj = src_sle.clone_as_object();
    src_obj.set_field_amount(
        sf("sfBalance"),
        STAmount::from_xrp_amount(protocol::XRPAmount::from_drops(src_balance - deliver_drops)),
    );
    view.update(Arc::new(protocol::STLedgerEntry::from_stobject(
        src_obj,
        *src_sle.key(),
    )))?;

    let dst_keylet = protocol::account_keylet(account_to_uint160(dst_account));
    if let Some(dst_sle) = view.peek(dst_keylet)? {
        let dst_balance = dst_sle.get_field_amount(sf("sfBalance")).xrp().drops();
        let mut dst_obj = dst_sle.clone_as_object();
        dst_obj.set_field_amount(
            sf("sfBalance"),
            STAmount::from_xrp_amount(protocol::XRPAmount::from_drops(dst_balance + deliver_drops)),
        );
        view.update(Arc::new(protocol::STLedgerEntry::from_stobject(
            dst_obj,
            *dst_sle.key(),
        )))?;
    }

    Ok(RippleCalcOutput {
        result: Ter::TES_SUCCESS,
        actual_amount_in: deliver.clone(),
        actual_amount_out: deliver,
    })
}

#[cfg(test)]
fn preserves_partial_flow_result(ter: Ter, actual_amount_out: &STAmount) -> bool {
    ter == Ter::TEC_PATH_PARTIAL && actual_amount_out.signum() > 0
}

pub fn ripple_calculate<V: ApplyView>(
    view: &mut V,
    max_source_amount: &STAmount,
    dst_amount: &STAmount,
    dst_account: &AccountID,
    src_account: &AccountID,
    paths: &STPathSet,
    input: &RippleCalcInput,
) -> Result<RippleCalcOutput, ViewError> {
    // steps. For parity, handle direct XRP→XRP transfers here before falling
    // through to the IOU flow engine.
    if dst_amount.native() && max_source_amount.native() {
        return handle_xrp_to_xrp_flow(
            view,
            max_source_amount,
            dst_amount,
            dst_account,
            src_account,
            input,
        );
    }

    // Debug: log what reaches the IOU flow engine
    static FLOW_LOG: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    let flow_c = FLOW_LOG.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    if flow_c < 30 {
        tracing::debug!(target: "ledger",            "[ripple_calc] src_native={} dst_native={} paths={} default_allowed={}",
            max_source_amount.native(),
            dst_amount.native(),
            paths.size(),
            input.default_paths_allowed,
        );
    }

    // Only apply the sandbox to the parent view on tesSUCCESS.
    // On failure, the sandbox is discarded (no state changes).
    let mut flow_sb = crate::FlowSandbox::new(view);
    let result = ripple_calculate_inner(
        &mut flow_sb,
        max_source_amount,
        dst_amount,
        dst_account,
        src_account,
        paths,
        input,
    )?;

    if is_tes_success(result.result) {
        flow_sb.apply()?;
    }

    Ok(result)
}

/// Inner flow engine logic that operates on the FlowSandbox.
/// All state changes are captured in the sandbox and only committed by the caller on success.
fn ripple_calculate_inner<V: ApplyView>(
    view: &mut V,
    max_source_amount: &STAmount,
    dst_amount: &STAmount,
    dst_account: &AccountID,
    src_account: &AccountID,
    paths: &STPathSet,
    input: &RippleCalcInput,
) -> Result<RippleCalcOutput, ViewError> {
    // This replaces the simplified try_default_path approach.
    let deliver_asset = dst_amount.asset();
    let send_max_asset = if max_source_amount.asset() != dst_amount.asset() {
        Some(max_source_amount.asset())
    } else {
        None
    };

    let (strand_ter, strands) =
        crate::domain::flow_engine::strand_builder::to_strands_checked_with_domain(
            view,
            src_account,
            dst_account,
            &deliver_asset,
            send_max_asset.as_ref(),
            paths,
            input.default_paths_allowed,
            false, // ownerPaysTransferFee = false for payments
            false, // offerCrossing = false for payments
            input.domain_id,
        );

    // `tfNoRippleDirect` with no explicit Paths makes Flow reject the
    // transaction as `temRIPPLE_EMPTY`. Do not fall through to the legacy
    // fallback, which has no paths to evaluate and incorrectly recasts that
    // malformed result as `tecPATH_PARTIAL`.
    if !is_tes_success(strand_ter) {
        return Ok(RippleCalcOutput {
            result: strand_ter,
            actual_amount_in: max_source_amount.zeroed(),
            actual_amount_out: dst_amount.zeroed(),
        });
    }

    if !strands.is_empty() {
        // Flow's aggregate value sandbox is applied only when execute_strands
        // succeeds; failed Payment flows retain no tentative transfers.
        let mut engine_sb = crate::FlowSandbox::new(view);
        let quality_threshold =
            (input.limit_quality && max_source_amount.signum() > 0).then(|| {
                Quality::from_amounts(&Amounts::new(max_source_amount.clone(), dst_amount.clone()))
            });
        let flow_result = crate::domain::flow_engine::strand_flow::execute_strands(
            &mut engine_sb,
            &strands,
            dst_amount,
            input.partial_payment_allowed,
            crate::domain::ripple_calc::OfferCrossing::No,
            Some(max_source_amount),
            src_account,
            dst_account,
            quality_threshold,
            None, // Payment ignores Flow's removable-offer collection.
        );

        static FLOW_RESULT_LOG: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
        if FLOW_RESULT_LOG.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < 30 {
            tracing::debug!(target: "ledger",                "[flow_engine] strands={} ter={:?} out_signum={} in_signum={} src_native={} dst_native={} default_allowed={}",
                strands.len(),
                flow_result.ter,
                flow_result.actual_out.signum(),
                flow_result.actual_in.signum(),
                max_source_amount.native(),
                dst_amount.native(),
                input.default_paths_allowed,
            );
        }

        engine_sb.apply()?;
        return Ok(RippleCalcOutput {
            result: flow_result.ter,
            actual_amount_in: flow_result.actual_in,
            actual_amount_out: flow_result.actual_out,
        });
    }

    Ok(RippleCalcOutput {
        result: Ter::TEC_PATH_DRY,
        actual_amount_in: max_source_amount.zeroed(),
        actual_amount_out: dst_amount.zeroed(),
    })
}

#[allow(dead_code)]
fn try_default_path<V: ApplyView>(
    view: &mut V,
    max_source_amount: &STAmount,
    dst_amount: &STAmount,
    dst_account: &AccountID,
    src_account: &AccountID,
    input: &RippleCalcInput,
) -> Result<Option<RippleCalcOutput>, ViewError> {
    // Exception: issuer is never frozen for their own tokens
    if !dst_amount.native() {
        let issue = dst_amount.issue();
        if *src_account != issue.account
            && *dst_account != issue.account
            && (crate::domain::ripple_state_helpers::try_is_frozen(view, src_account, &issue)?
                || crate::domain::ripple_state_helpers::try_is_frozen(view, dst_account, &issue)?)
        {
            return Ok(Some(RippleCalcOutput {
                result: Ter::TEC_PATH_DRY,
                actual_amount_in: max_source_amount.zeroed(),
                actual_amount_out: dst_amount.zeroed(),
            }));
        }
    }

    // XRP→IOU: cross DEX order book
    if max_source_amount.native() && !dst_amount.native() {
        return try_xrp_to_iou_default_path(
            view,
            max_source_amount,
            dst_amount,
            dst_account,
            src_account,
            input,
        );
    }
    // IOU→XRP: cross DEX order book
    if !max_source_amount.native() && dst_amount.native() {
        return try_iou_to_xrp_default_path(
            view,
            max_source_amount,
            dst_amount,
            dst_account,
            src_account,
            input,
        );
    }
    if dst_amount.native() || max_source_amount.native() {
        return Ok(None);
    }

    let issue = dst_amount.issue();
    let issuer = issue.account;
    let currency = issue.currency;

    // Case 1: sender IS issuer → direct to receiver
    // Case 2: receiver IS issuer → direct from sender
    // Case 3: neither is issuer → route through issuer (two hops)
    // Case 4: direct trust line exists → direct transfer

    let has_direct_line = view
        .peek(protocol::line(*src_account, *dst_account, currency))?
        .is_some();
    let src_is_issuer = *src_account == issuer;
    let dst_is_issuer = *dst_account == issuer;

    if !has_direct_line && !src_is_issuer && !dst_is_issuer {
        // so we don't need to pre-check for their existence.

        // Route through issuer
        let rate = {
            let issuer_keylet = protocol::account_keylet(account_to_uint160(&issuer));
            if let Some(issuer_sle) = view.read(issuer_keylet)? {
                let r = issuer_sle.get_field_u32(sf("sfTransferRate"));
                if r == 0 { QUALITY_ONE } else { r }
            } else {
                QUALITY_ONE
            }
        };

        let amount_to_deliver = dst_amount.clone();
        let amount_needed = if rate == QUALITY_ONE {
            amount_to_deliver.clone()
        } else {
            let rate_amount = STAmount::new_with_asset(
                sf("sfAmount"),
                dst_amount.asset(),
                rate as u64,
                -9,
                false,
            );
            amount_to_deliver.multiply(&rate_amount, dst_amount.asset())
        };

        if amount_needed > *max_source_amount {
            if input.partial_payment_allowed {
                let actual_in = max_source_amount.clone();
                let rate_amount = STAmount::new_with_asset(
                    sf("sfAmount"),
                    dst_amount.asset(),
                    rate as u64,
                    -9,
                    false,
                );
                let actual_out = actual_in.divide(&rate_amount, dst_amount.asset());
                // Two-hop: sender→issuer→receiver
                let transfer = apply_direct_iou_transfer(
                    view,
                    src_account,
                    dst_account,
                    &actual_out,
                    &issuer,
                    currency,
                );
                if transfer != Ter::TES_SUCCESS {
                    return Ok(Some(failed_ripple_calc_output(
                        transfer,
                        max_source_amount,
                        dst_amount,
                    )));
                }
                return Ok(Some(RippleCalcOutput {
                    result: Ter::TES_SUCCESS,
                    actual_amount_in: actual_in,
                    actual_amount_out: actual_out,
                }));
            }
            return Ok(None);
        }

        // Two-hop transfer through issuer
        let transfer = apply_direct_iou_transfer(
            view,
            src_account,
            dst_account,
            &amount_to_deliver,
            &issuer,
            currency,
        );
        if transfer != Ter::TES_SUCCESS {
            return Ok(Some(failed_ripple_calc_output(
                transfer,
                max_source_amount,
                dst_amount,
            )));
        }
        return Ok(Some(RippleCalcOutput {
            result: Ter::TES_SUCCESS,
            actual_amount_in: amount_needed,
            actual_amount_out: amount_to_deliver,
        }));
    }

    // Direct path (trust line exists, or one party is issuer)
    let rate = if src_is_issuer || dst_is_issuer {
        QUALITY_ONE
    } else {
        let issuer_keylet = protocol::account_keylet(account_to_uint160(&issuer));
        if let Some(issuer_sle) = view.read(issuer_keylet)? {
            let r = issuer_sle.get_field_u32(sf("sfTransferRate"));
            if r == 0 { QUALITY_ONE } else { r }
        } else {
            QUALITY_ONE
        }
    };

    let amount_to_deliver = dst_amount.clone();
    let amount_needed = if rate == QUALITY_ONE {
        amount_to_deliver.clone()
    } else {
        let rate_amount =
            STAmount::new_with_asset(sf("sfAmount"), dst_amount.asset(), rate as u64, -9, false);
        amount_to_deliver.multiply(&rate_amount, dst_amount.asset())
    };

    if amount_needed > *max_source_amount {
        if input.partial_payment_allowed {
            let actual_in = max_source_amount.clone();
            let rate_amount = STAmount::new_with_asset(
                sf("sfAmount"),
                dst_amount.asset(),
                rate as u64,
                -9,
                false,
            );
            let actual_out = actual_in.divide(&rate_amount, dst_amount.asset());
            let transfer = apply_direct_iou_transfer(
                view,
                src_account,
                dst_account,
                &actual_out,
                &issuer,
                currency,
            );
            if transfer != Ter::TES_SUCCESS {
                return Ok(Some(failed_ripple_calc_output(
                    transfer,
                    max_source_amount,
                    dst_amount,
                )));
            }
            return Ok(Some(RippleCalcOutput {
                result: Ter::TES_SUCCESS,
                actual_amount_in: actual_in,
                actual_amount_out: actual_out,
            }));
        }
        return Ok(None);
    }

    let transfer = apply_direct_iou_transfer(
        view,
        src_account,
        dst_account,
        &amount_to_deliver,
        &issuer,
        currency,
    );
    if transfer != Ter::TES_SUCCESS {
        return Ok(Some(failed_ripple_calc_output(
            transfer,
            max_source_amount,
            dst_amount,
        )));
    }
    Ok(Some(RippleCalcOutput {
        result: Ter::TES_SUCCESS,
        actual_amount_in: amount_needed,
        actual_amount_out: amount_to_deliver,
    }))
}

/// XRP→IOU default path: source sends XRP, crosses XRP/IOU order book, delivers IOU.
#[allow(dead_code)]
fn try_xrp_to_iou_default_path<V: ApplyView>(
    view: &mut V,
    max_source_amount: &STAmount,
    dst_amount: &STAmount,
    dst_account: &AccountID,
    src_account: &AccountID,
    _input: &RippleCalcInput,
) -> Result<Option<RippleCalcOutput>, ViewError> {
    let dst_issue = dst_amount.issue();
    // Book: XRP → destination IOU
    let book = book_step::Book {
        r#in: Asset::Issue(protocol::xrp_issue()),
        out: Asset::Issue(dst_issue),
        domain: None,
    };
    let result = book_step::execute_book_step(
        view,
        &book,
        max_source_amount,
        dst_amount,
        false,
        Some(src_account),
        None,
    );

    static XRP_IOU_LOG: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    if XRP_IOU_LOG.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < 10 {
        tracing::debug!(target: "ledger",            "[xrp_to_iou] book_result: ter={:?} in_signum={} out_signum={} offers_consumed={}",
            result.ter,
            result.amount_in.signum(),
            result.amount_out.signum(),
            result.offers_consumed
        );
    }

    if result.ter != Ter::TES_SUCCESS || result.amount_out.signum() <= 0 {
        return Ok(None);
    }

    // Debit XRP from source
    let src_keylet = protocol::account_keylet(account_to_uint160(src_account));
    if let Some(src_sle) = view.peek(src_keylet)? {
        let balance = src_sle.get_field_amount(sf("sfBalance")).xrp().drops();
        let debit = result.amount_in.xrp().drops();
        if debit > balance {
            return Ok(None);
        }
        let mut obj = src_sle.clone_as_object();
        obj.set_field_amount(
            sf("sfBalance"),
            STAmount::from_xrp_amount(protocol::XRPAmount::from_drops(balance - debit)),
        );
        view.update(Arc::new(STLedgerEntry::from_stobject(obj, *src_sle.key())))?;
    }

    // Credit IOU to destination (issuer→dst via trust line)
    let issuer = dst_issue.account;
    if *dst_account != issuer {
        let transfer = crate::domain::ripple_state_helpers::direct_send_no_fee_iou_pub(
            view,
            &issuer,
            dst_account,
            &result.amount_out,
        );
        if transfer != Ter::TES_SUCCESS {
            return Ok(Some(failed_ripple_calc_output(
                transfer,
                max_source_amount,
                dst_amount,
            )));
        }
    }

    Ok(Some(RippleCalcOutput {
        result: Ter::TES_SUCCESS,
        actual_amount_in: result.amount_in,
        actual_amount_out: result.amount_out,
    }))
}

/// IOU→XRP default path: source sends IOU, crosses IOU/XRP order book, delivers XRP.
#[allow(dead_code)]
fn try_iou_to_xrp_default_path<V: ApplyView>(
    view: &mut V,
    max_source_amount: &STAmount,
    dst_amount: &STAmount,
    dst_account: &AccountID,
    src_account: &AccountID,
    _input: &RippleCalcInput,
) -> Result<Option<RippleCalcOutput>, ViewError> {
    let src_issue = max_source_amount.issue();
    // Book: source IOU → XRP
    let book = book_step::Book {
        r#in: Asset::Issue(src_issue),
        out: Asset::Issue(protocol::xrp_issue()),
        domain: None,
    };
    let result = book_step::execute_book_step(
        view,
        &book,
        max_source_amount,
        dst_amount,
        false,
        Some(src_account),
        None,
    );

    static IOU_XRP_LOG: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    if IOU_XRP_LOG.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < 10 {
        tracing::debug!(target: "ledger",            "[iou_to_xrp] book_result: ter={:?} in_signum={} out_signum={} offers_consumed={}",
            result.ter,
            result.amount_in.signum(),
            result.amount_out.signum(),
            result.offers_consumed
        );
    }

    if result.ter != Ter::TES_SUCCESS || result.amount_out.signum() <= 0 {
        return Ok(None);
    }

    // Debit IOU from source (src→issuer via trust line)
    let issuer = src_issue.account;
    if *src_account != issuer {
        let transfer = crate::domain::ripple_state_helpers::direct_send_no_fee_iou_pub(
            view,
            src_account,
            &issuer,
            &result.amount_in,
        );
        if transfer != Ter::TES_SUCCESS {
            return Ok(Some(failed_ripple_calc_output(
                transfer,
                max_source_amount,
                dst_amount,
            )));
        }
    }

    // Credit XRP to destination
    let dst_keylet = protocol::account_keylet(account_to_uint160(dst_account));
    if let Some(dst_sle) = view.peek(dst_keylet)? {
        let balance = dst_sle.get_field_amount(sf("sfBalance")).xrp().drops();
        let credit = result.amount_out.xrp().drops();
        let mut obj = dst_sle.clone_as_object();
        obj.set_field_amount(
            sf("sfBalance"),
            STAmount::from_xrp_amount(protocol::XRPAmount::from_drops(balance + credit)),
        );
        view.update(Arc::new(STLedgerEntry::from_stobject(obj, *dst_sle.key())))?;
    }

    Ok(Some(RippleCalcOutput {
        result: Ter::TES_SUCCESS,
        actual_amount_in: result.amount_in,
        actual_amount_out: result.amount_out,
    }))
}

fn apply_direct_iou_transfer<V: ApplyView>(
    view: &mut V,
    sender: &AccountID,
    receiver: &AccountID,
    amount: &STAmount,
    issuer: &AccountID,
    _currency: protocol::Currency,
) -> Ter {
    if amount.signum() == 0 {
        return Ter::TES_SUCCESS;
    }
    // If sender or receiver is issuer → single direct transfer (no fee)
    // If neither is issuer → two-leg transfer through issuer (fee applied by caller)
    if *sender == *issuer || *receiver == *issuer || issuer.data().iter().all(|&b| b == 0) {
        // Direct: sender → receiver (one of them is issuer)
        return crate::domain::ripple_state_helpers::direct_send_no_fee_iou_pub(
            view, sender, receiver, amount,
        );
    } else {
        // 3rd party: issuer credits receiver, sender debits to issuer
        // The caller already computed the fee-adjusted amount for the sender side
        let receiver_transfer = crate::domain::ripple_state_helpers::direct_send_no_fee_iou_pub(
            view, issuer, receiver, amount,
        );
        if receiver_transfer != Ter::TES_SUCCESS {
            return receiver_transfer;
        }
        // Sender pays amount * rate to issuer (caller passes amount_to_deliver here,
        // but the actual debit from sender is amount_needed which includes fee)
        // Since try_default_path calls us with amount_to_deliver, we need to
        // compute the fee-adjusted amount for the sender→issuer leg
        let rate = match crate::domain::ripple_state_helpers::try_transfer_rate(view, issuer) {
            Ok(rate) => rate,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        let sender_amount = if rate == 1_000_000_000 {
            amount.clone()
        } else {
            let iou = amount.iou();
            let adjusted = crate::domain::mul_ratio::mul_ratio(
                iou,
                rate,
                crate::domain::mul_ratio::QUALITY_ONE,
                true,
            );
            STAmount::from_iou_amount(sf("sfAmount"), adjusted, amount.issue())
        };
        return crate::domain::ripple_state_helpers::direct_send_no_fee_iou_pub(
            view,
            sender,
            issuer,
            &sender_amount,
        );
    }
}

fn failed_ripple_calc_output(
    ter: Ter,
    max_source_amount: &STAmount,
    dst_amount: &STAmount,
) -> RippleCalcOutput {
    RippleCalcOutput {
        result: ter,
        actual_amount_in: max_source_amount.zeroed(),
        actual_amount_out: dst_amount.zeroed(),
    }
}

#[allow(dead_code)]
fn credit_trust_line<V: ApplyView>(
    view: &mut V,
    issuer: &AccountID,
    holder: &AccountID,
    amount: &STAmount,
    currency: protocol::Currency,
) -> Result<(), ViewError> {
    let line_keylet = protocol::line(*issuer, *holder, currency);
    if let Some(sle) = view.peek(line_keylet)? {
        let b_high = *holder > *issuer;
        let current_balance = sle.get_field_amount(sf("sfBalance"));
        let new_balance = if b_high {
            current_balance.clone() - amount.clone()
        } else {
            current_balance.clone() + amount.clone()
        };
        let mut obj = sle.clone_as_object();
        obj.set_field_amount(sf("sfBalance"), new_balance);
        view.update(Arc::new(STLedgerEntry::from_stobject(obj, *sle.key())))?;
    }
    Ok(())
}

#[allow(dead_code)]
fn try_explicit_path<V: ApplyView>(
    view: &mut V,
    max_source_amount: &STAmount,
    dst_amount: &STAmount,
    dst_account: &AccountID,
    src_account: &AccountID,
    path: &protocol::STPath,
    input: &RippleCalcInput,
) -> Result<Option<RippleCalcOutput>, ViewError> {
    let Some(strand) = build_explicit_strand(
        0,
        src_account,
        dst_account,
        max_source_amount,
        dst_amount,
        path,
    ) else {
        return Ok(None);
    };

    execute_direct_strand(
        view,
        &strand,
        max_source_amount,
        dst_amount,
        input.partial_payment_allowed,
    )
}
#[cfg(test)]
mod tests {
    use basics::{base_uint::Uint256, string_utilities::str_unhex};
    use protocol::{
        ApplyFlags, LedgerHeader, STAmount, STTx, SerialIter, Ter, XRPAmount, get_field_by_symbol,
    };
    use shamap::{
        item::SHAMapItem,
        mutation::MutableTree,
        sync::{SHAMapType, SyncState, SyncTree},
        tree_node::SHAMapNodeType,
    };
    use std::sync::Arc;

    use super::{RippleCalcInput, preserves_partial_flow_result, ripple_calculate};

    fn canonical_20453340_payment_view() -> (crate::ApplyViewImpl<crate::Ledger>, STTx) {
        let entries = [
            (
                "F6814EDE3FE7E0B5760D9C24C5E320467270F2D48357B7506A58F139E7623300",
                "110061220000000024013817CD25013817CF2D0000000155310CE7E99B26450F597D2F039A5726786E3364633F9642C2D9C75A7104BEBB44624000000005F5E0F181149FEB510FBD0FA510A4DF8545EBEC9E6B489DE63E",
            ),
            (
                "588CCD89EE8F7176AA0E796B6CB3AAE3F19D7DF539E3F9BEDDAFD23181A7DC75",
                "110061220000000024013817D125013817DB2D00000001552601FBB558FB41697E155829A4C32EB6DC851DAEBCC9F741B355613E15E0E049624000000005F5E0B58114A8BCBDD8E9BD995D962F4A2EEAEDAC0B9D93D7BA",
            ),
            (
                "F5A3371E1A0E2C39596C06330913154E3A5F078A412F712A1A8175D842709E29",
                "110061220080000024013817CC25013817D52D0000000155D180562EF98C0EE6C8C98959E991D6C4DA40159F447119D160018EA7E340009D624000000005F5E0D38114B2FAE10016981B1BBABE8DD63958DBFB4CDCB5AC",
            ),
            (
                "90D9474DA52FCA1188FFEEF0019DAFFB715F72271B5E9A1AB3CEDBAE2576DD35",
                "110072220011000025013817D3370000000000000000380000000000000000557A25F37A13EA479C8C7B4AF95CD45248A81FB19BDFD98CD8153615807541A46662D551C37937E080007573640000000000000000000000000000000000000000000000000000000000000000000000000166D5838D7EA4C6800075736400000000000000000000000000000000009FEB510FBD0FA510A4DF8545EBEC9E6B489DE63E6780000000000000007573640000000000000000000000000000000000B2FAE10016981B1BBABE8DD63958DBFB4CDCB5AC",
            ),
            (
                "24E247061AD981274F83DAF4CC2D1AF814532DF5C3CDED20B828F88180FA3E3D",
                "110072220093000025013817D937000000000000000038000000000000000055354ECEE39F6145578FBF29A638FD0F93249A68200E14AB2265D8DE5D7C6F21E66280000000000000007573640000000000000000000000000000000000000000000000000000000000000000000000000166D5838D7EA4C680007573640000000000000000000000000000000000A8BCBDD8E9BD995D962F4A2EEAEDAC0B9D93D7BA6780000000000000007573640000000000000000000000000000000000B2FAE10016981B1BBABE8DD63958DBFB4CDCB5AC",
            ),
        ];
        let mut tree = MutableTree::new(1);
        for (key, raw) in entries {
            tree.add_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(
                    Uint256::from_hex(key).expect("canonical ledger key"),
                    str_unhex(raw).expect("canonical ledger entry"),
                ),
            )
            .expect("unique canonical ledger entry");
        }
        let state = SyncTree::from_root_with_type(
            tree.root(),
            SHAMapType::State,
            false,
            20_453_340,
            SyncState::Immutable,
        );
        let txs = SyncTree::new_with_type(SHAMapType::Transaction, false, 20_453_340);
        let ledger = crate::Ledger::from_maps(
            LedgerHeader {
                seq: 20_453_340,
                close_time: 841_762_460,
                ..LedgerHeader::default()
            },
            state,
            txs,
        );
        let tx_raw = str_unhex("12000024013817CD61D551C37937E080007573640000000000000000000000000000000000B2FAE10016981B1BBABE8DD63958DBFB4CDCB5AC68400000000000000F7321ED7EC3E83B1D1967DFAAD276D02DF3D6176DF8A849EB755472AA98CA9888E9219E744064AF66FB90E79236367D3B494212D9B00C58F64520FBF133037E2CD072C3346AA20805A7796961415A4ABF3EF991851DF5763BA1049C1FD71BBB9FC3FC2F190C81149FEB510FBD0FA510A4DF8545EBEC9E6B489DE63E8314A8BCBDD8E9BD995D962F4A2EEAEDAC0B9D93D7BA").expect("canonical transaction");
        let tx = STTx::from_serial_iter(&mut SerialIter::new(&tx_raw));
        (
            crate::ApplyViewImpl::new(Arc::new(ledger), ApplyFlags::NONE),
            tx,
        )
    }

    #[test]
    fn preserves_nonzero_partial_flow_result_without_committing_its_sandbox() {
        let delivered = STAmount::from_xrp_amount(XRPAmount::from_drops(5));
        assert!(preserves_partial_flow_result(
            Ter::TEC_PATH_PARTIAL,
            &delivered
        ));
        assert!(!preserves_partial_flow_result(
            Ter::TEC_PATH_DRY,
            &delivered
        ));
        assert!(!preserves_partial_flow_result(
            Ter::TEC_PATH_PARTIAL,
            &delivered.zeroed()
        ));
    }

    #[test]
    fn canonical_holder_to_holder_iou_payment_is_not_path_dry() {
        let (mut view, tx) = canonical_20453340_payment_view();
        let amount = tx.get_field_amount(get_field_by_symbol("sfAmount"));
        let source = tx.get_account_id(get_field_by_symbol("sfAccount"));
        let destination = tx.get_account_id(get_field_by_symbol("sfDestination"));
        let result = ripple_calculate(
            &mut view,
            &amount,
            &amount,
            &destination,
            &source,
            &protocol::STPathSet::new(get_field_by_symbol("sfPaths")),
            &RippleCalcInput {
                partial_payment_allowed: false,
                default_paths_allowed: true,
                limit_quality: false,
                is_ledger_open: false,
                domain_id: None,
            },
        )
        .expect("canonical parent state is readable");
        assert_eq!(result.result, Ter::TES_SUCCESS);
        assert_eq!(result.actual_amount_in, amount);
        assert_eq!(result.actual_amount_out, amount);
    }
}

pub mod book_step;
pub mod direct_step;
pub mod xrp_endpoint_step;
