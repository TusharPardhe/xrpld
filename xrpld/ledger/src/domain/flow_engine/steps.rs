//! Step execution for the flow engine.
//!
//! A strand is evaluated backwards first and then, when a step limits the
//! request, forwards from that step.  `StepAmount` deliberately carries the
//! ledger asset with the numeric amount: a SendMax in USD must never be
//! compared with a requested XRP delivery.

use super::{AmmContext, SelfCrossCancellation, StepKind};
use crate::domain::ripple_state_helpers;
use crate::{ApplyView, ViewError};
use protocol::{
    AccountID, Asset, Issue, Quality, STAmount, Ter, XRPAmount, get_field_by_symbol as sf,
    xrp_account,
};
use std::{cell::Cell, rc::Rc};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AmountTag {
    ExactAsset(Asset),
    Currency(protocol::Currency),
}

/// A ledger amount tagged with the identity valid for this step. Book and
/// endpoint quantities retain an exact asset; direct trust-line quantities are
/// deliberately tagged by currency because an issuer representation changes as
/// value ripples across a line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StepAmount {
    amount: STAmount,
    tag: AmountTag,
}

impl StepAmount {
    pub fn new(amount: STAmount) -> Self {
        Self {
            tag: AmountTag::ExactAsset(amount.asset()),
            amount,
        }
    }

    fn with_currency(amount: STAmount, currency: protocol::Currency) -> Self {
        Self {
            amount,
            tag: AmountTag::Currency(currency),
        }
    }

    pub fn amount(&self) -> &STAmount {
        &self.amount
    }

    pub fn asset(&self) -> Asset {
        self.amount.asset()
    }

    pub fn is_zero(&self) -> bool {
        self.amount.signum() <= 0
    }

    /// `Some` only when both amounts have the same step-valid identity.
    pub fn greater_than(&self, other: &STAmount) -> Option<bool> {
        self.matches_amount(other).then(|| self.amount > *other)
    }

    fn matches_amount(&self, other: &STAmount) -> bool {
        match self.tag {
            AmountTag::ExactAsset(asset) => asset == other.asset(),
            AmountTag::Currency(currency) => {
                if protocol::is_xrp_currency(currency) {
                    other.native()
                } else {
                    !other.native() && other.issue().currency == currency
                }
            }
        }
    }

    pub(crate) fn equivalent(&self, other: &StepAmount) -> bool {
        let same_unit = match (self.tag, other.tag) {
            (AmountTag::ExactAsset(lhs), AmountTag::ExactAsset(rhs)) => lhs == rhs,
            (AmountTag::Currency(currency), _) | (_, AmountTag::Currency(currency)) => {
                self.matches_currency(currency) && other.matches_currency(currency)
            }
        };
        same_unit
            && self.amount.mantissa() == other.amount.mantissa()
            && self.amount.exponent() == other.amount.exponent()
            && self.amount.negative() == other.amount.negative()
    }

    fn matches_book_asset(&self, asset: Asset) -> bool {
        match self.tag {
            AmountTag::ExactAsset(actual) => actual == asset,
            AmountTag::Currency(currency) => match asset {
                Asset::Issue(issue) => !issue.native() && issue.currency == currency,
                Asset::MPTIssue(_) => false,
            },
        }
    }

    fn matches_currency(&self, currency: protocol::Currency) -> bool {
        self.amount.native() == protocol::is_xrp_currency(currency)
            && (self.amount.native() || self.amount.issue().currency == currency)
    }
}

/// Input/output pair returned by every `rev` and `fwd` call.
#[derive(Debug, Clone)]
pub struct StepAmounts {
    pub input: StepAmount,
    pub output: StepAmount,
    pub offers_used: u32,
    pub inactive: bool,
}

impl StepAmounts {
    fn new(input: STAmount, output: STAmount) -> Self {
        Self {
            input: StepAmount::new(input),
            output: StepAmount::new(output),
            offers_used: 0,
            inactive: false,
        }
    }

    fn direct(input: STAmount, output: STAmount, currency: protocol::Currency) -> Self {
        Self {
            input: StepAmount::with_currency(input, currency),
            output: StepAmount::with_currency(output, currency),
            offers_used: 0,
            inactive: false,
        }
    }

    fn book(input: STAmount, output: STAmount, offers_used: u32) -> Self {
        Self {
            input: StepAmount::new(input),
            output: StepAmount::new(output),
            offers_used,
            inactive: offers_used >= crate::domain::ripple_calc::book_step::MAX_OFFERS_TO_CONSUME,
        }
    }
}

/// Immutable execution context shared by a strand's concrete steps.
#[derive(Debug, Clone)]
pub struct StepContext<'a> {
    pub strand_src: &'a AccountID,
    pub strand_dst: &'a AccountID,
    pub strand_deliver: Asset,
    /// rippled uses DirectIOfferCrossingStep rather than DirectIPaymentStep
    /// for OfferCreate. Its final issuer-to-taker step ignores a missing
    /// trust-line limit and all trust-line quality fields.
    pub offer_crossing: bool,
    pub quality_threshold: Option<Quality>,
    /// Present only for direct/default OfferCreate crossings. It is separate
    /// from the flow sandbox so self-offer cancellations survive a dry flow.
    pub self_cross_cancellation: Option<SelfCrossCancellation>,
    pub amm_context: AmmContext,
    /// Sum of each BookStep's offers-used value for the current strand run.
    /// The runner resets this between the discarded reverse probe and replay.
    pub offer_usage: Rc<Cell<u32>>,
    /// Debt direction immediately before the currently executing step.
    pub previous_redeems: Rc<Cell<bool>>,
    /// `BookStep::checkMPTDEX` distinguishes an issuer-starting strand, a
    /// preceding BookStep, and a preceding endpoint/direct step.  Debt
    /// direction alone cannot recover that consensus-significant shape.
    pub has_previous_step: Rc<Cell<bool>>,
    pub previous_step_is_book: Rc<Cell<bool>>,
}

/// The Rust counterpart to rippled's `Step`.  Both directions mutate only the
/// sandbox supplied by the caller and return typed input/output quantities.
pub trait FlowStep {
    fn rev<V: ApplyView>(
        &self,
        view: &mut V,
        requested_out: &StepAmount,
        context: &StepContext<'_>,
    ) -> Result<StepAmounts, Ter>;

    fn fwd<V: ApplyView>(
        &self,
        view: &mut V,
        requested_in: &StepAmount,
        reverse_cache: &StepAmounts,
        context: &StepContext<'_>,
    ) -> Result<StepAmounts, Ter>;
}

impl FlowStep for StepKind {
    fn rev<V: ApplyView>(
        &self,
        view: &mut V,
        requested_out: &StepAmount,
        context: &StepContext<'_>,
    ) -> Result<StepAmounts, Ter> {
        match self {
            StepKind::Direct { src, dst, currency } => {
                if !requested_out.matches_currency(*currency) {
                    return Err(Ter::TEF_INTERNAL);
                }
                let (input, output) = execute_direct_fwd(
                    view,
                    src,
                    dst,
                    requested_out.amount(),
                    context.strand_dst,
                    context.offer_crossing,
                )?;
                Ok(StepAmounts::direct(input, output, *currency))
            }
            StepKind::XrpEndpoint { account, is_last } => {
                if !requested_out.amount().native() {
                    return Err(Ter::TEF_INTERNAL);
                }
                let (input, output) =
                    execute_xrp_endpoint_fwd(view, account, *is_last, requested_out.amount())?;
                Ok(StepAmounts::new(input, output))
            }
            StepKind::MptEndpoint {
                src,
                dst,
                issue,
                is_first,
                is_last,
                offer_crossing,
            } => {
                if requested_out.asset() != Asset::MPTIssue(*issue) {
                    return Err(Ter::TEF_INTERNAL);
                }
                let (input, output) = execute_mpt_endpoint(
                    view,
                    src,
                    dst,
                    issue,
                    requested_out.amount(),
                    *is_first,
                    *is_last,
                    *offer_crossing,
                    context.previous_redeems.get(),
                    context.strand_src,
                    context.strand_dst,
                    context.strand_deliver,
                    true,
                )?;
                Ok(StepAmounts::new(input, output))
            }
            StepKind::Book {
                book_in,
                book_out,
                domain,
                owner_pays_transfer_fee,
                remove_self_crossing,
            } => {
                let in_asset = *book_in;
                let out_asset = *book_out;
                if !requested_out.matches_book_asset(out_asset) {
                    return Err(Ter::TEF_INTERNAL);
                }
                let book = crate::domain::ripple_calc::book_step::Book {
                    r#in: in_asset,
                    out: out_asset,
                    domain: *domain,
                };
                // Reverse book execution asks for output and supplies an
                // effectively unbounded input.  The book consumes only the
                // input required to produce the requested output.
                let requested_out = normalize_amount_asset(requested_out.amount(), out_asset);
                let result = crate::domain::ripple_calc::book_step::execute_book_step_with_options(
                    view,
                    &book,
                    &unlimited_amount(in_asset),
                    &requested_out,
                    crate::domain::ripple_calc::book_step::BookStepOptions {
                        owner_pays_transfer_fee: *owner_pays_transfer_fee,
                        taker: Some(context.strand_src),
                        quality_threshold: context.quality_threshold,
                        remove_self_crossing: *remove_self_crossing,
                        self_cross_cancellation: context.self_cross_cancellation.clone(),
                        amm_context: Some(context.amm_context.clone()),
                        previous_redeems: context.previous_redeems.get(),
                        has_previous_step: context.has_previous_step.get(),
                        previous_step_is_book: context.previous_step_is_book.get(),
                        strand_dst: Some(context.strand_dst),
                        strand_deliver: Some(context.strand_deliver),
                        enforce_quality_threshold: *remove_self_crossing,
                    },
                );
                context.offer_usage.set(
                    context
                        .offer_usage
                        .get()
                        .saturating_add(result.offers_consumed),
                );
                if result.ter != Ter::TES_SUCCESS {
                    return Err(result.ter);
                }
                Ok(StepAmounts::book(
                    result.amount_in,
                    result.amount_out,
                    result.offers_consumed,
                ))
            }
        }
    }

    fn fwd<V: ApplyView>(
        &self,
        view: &mut V,
        requested_in: &StepAmount,
        reverse_cache: &StepAmounts,
        context: &StepContext<'_>,
    ) -> Result<StepAmounts, Ter> {
        match self {
            StepKind::Direct { src, dst, currency } => {
                if !requested_in.matches_currency(*currency) {
                    return Err(Ter::TEF_INTERNAL);
                }
                let (input, output) = execute_direct_fwd(
                    view,
                    src,
                    dst,
                    requested_in.amount(),
                    context.strand_dst,
                    context.offer_crossing,
                )?;
                Ok(StepAmounts::direct(input, output, *currency))
            }
            StepKind::XrpEndpoint { account, is_last } => {
                if !requested_in.amount().native() {
                    return Err(Ter::TEF_INTERNAL);
                }
                let (input, output) =
                    execute_xrp_endpoint_fwd(view, account, *is_last, requested_in.amount())?;
                Ok(StepAmounts::new(input, output))
            }
            StepKind::MptEndpoint {
                src,
                dst,
                issue,
                is_first,
                is_last,
                offer_crossing,
            } => {
                if requested_in.asset() != Asset::MPTIssue(*issue) {
                    return Err(Ter::TEF_INTERNAL);
                }
                let (input, output) = execute_mpt_endpoint(
                    view,
                    src,
                    dst,
                    issue,
                    requested_in.amount(),
                    *is_first,
                    *is_last,
                    *offer_crossing,
                    context.previous_redeems.get(),
                    context.strand_src,
                    context.strand_dst,
                    context.strand_deliver,
                    false,
                )?;
                Ok(StepAmounts::new(input, output))
            }
            StepKind::Book {
                book_in,
                book_out,
                domain,
                owner_pays_transfer_fee,
                remove_self_crossing,
            } => {
                let in_asset = *book_in;
                let out_asset = *book_out;
                if !requested_in.matches_book_asset(in_asset)
                    || !reverse_cache.output.matches_book_asset(out_asset)
                {
                    return Err(Ter::TEF_INTERNAL);
                }
                let book = crate::domain::ripple_calc::book_step::Book {
                    r#in: in_asset,
                    out: out_asset,
                    domain: *domain,
                };
                let requested_in = normalize_amount_asset(requested_in.amount(), in_asset);
                let reverse_out = normalize_amount_asset(reverse_cache.output.amount(), out_asset);
                let result = crate::domain::ripple_calc::book_step::execute_book_step_with_options(
                    view,
                    &book,
                    &requested_in,
                    &reverse_out,
                    crate::domain::ripple_calc::book_step::BookStepOptions {
                        owner_pays_transfer_fee: *owner_pays_transfer_fee,
                        taker: Some(context.strand_src),
                        quality_threshold: context.quality_threshold,
                        remove_self_crossing: *remove_self_crossing,
                        self_cross_cancellation: context.self_cross_cancellation.clone(),
                        amm_context: Some(context.amm_context.clone()),
                        previous_redeems: context.previous_redeems.get(),
                        has_previous_step: context.has_previous_step.get(),
                        previous_step_is_book: context.previous_step_is_book.get(),
                        strand_dst: Some(context.strand_dst),
                        strand_deliver: Some(context.strand_deliver),
                        enforce_quality_threshold: *remove_self_crossing,
                    },
                );
                context.offer_usage.set(
                    context
                        .offer_usage
                        .get()
                        .saturating_add(result.offers_consumed),
                );
                if result.ter != Ter::TES_SUCCESS {
                    return Err(result.ter);
                }
                Ok(StepAmounts::book(
                    result.amount_in,
                    result.amount_out,
                    result.offers_consumed,
                ))
            }
        }
    }
}

impl StepKind {
    /// Current theoretical quality used to order ActiveStrands.  The boolean
    /// carries rippled's previous-step DebtDirection (`true` = Redeems).
    pub(crate) fn quality_upper_bound<V: ApplyView>(
        &self,
        view: &mut V,
        previous_redeems: bool,
        context: &StepContext<'_>,
    ) -> Result<Option<(Quality, bool)>, ViewError> {
        match self {
            StepKind::XrpEndpoint { .. } => Ok(Some((quality_one(), false))),
            StepKind::MptEndpoint { src, issue, .. } => {
                let issuing = *src == issue.issuer();
                let rate = if issuing && previous_redeems {
                    crate::mptoken_helpers::transfer_rate_mpt(view, issue.mpt_id())?.value
                } else {
                    protocol::PARITY_RATE.value
                };
                let input = STAmount::from_mpt_amount(
                    sf("sfAmount"),
                    protocol::MPTAmount::from_value(i64::from(rate)),
                    *issue,
                );
                let output = STAmount::from_mpt_amount(
                    sf("sfAmount"),
                    protocol::MPTAmount::from_value(i64::from(protocol::PARITY_RATE.value)),
                    *issue,
                );
                Ok(Some((
                    Quality::from_amounts(&protocol::Amounts::new(input, output)),
                    !issuing,
                )))
            }
            StepKind::Direct { src, dst, currency } => {
                use crate::domain::ripple_calc::direct_step::{
                    DebtDirection, qualities_src_issues, qualities_src_redeems,
                };
                let (_, direction) = crate::domain::ripple_calc::direct_step::max_payment_flow(
                    view, src, dst, *currency,
                )?;
                let redeeming = direction == DebtDirection::Redeems;
                let (quality_out, quality_in) = if context.offer_crossing {
                    // DirectIOfferCrossingStep::quality deliberately ignores
                    // the trust line's QualityIn/QualityOut fields.
                    (protocol::QUALITY_ONE, protocol::QUALITY_ONE)
                } else if redeeming {
                    qualities_src_redeems(view, src, dst, *currency)?
                } else {
                    qualities_src_issues(view, src, dst, *currency, previous_redeems)?
                };
                let issue = Issue::new(*currency, *src);
                let input = STAmount::from_iou_amount(
                    sf("sfAmount"),
                    match protocol::IOUAmount::from_parts(i64::from(quality_out), 0) {
                        Ok(amount) => amount,
                        Err(_) => return Ok(None),
                    },
                    issue,
                );
                let output = STAmount::from_iou_amount(
                    sf("sfAmount"),
                    match protocol::IOUAmount::from_parts(i64::from(quality_in), 0) {
                        Ok(amount) => amount,
                        Err(_) => return Ok(None),
                    },
                    issue,
                );
                Ok(Some((
                    Quality::from_amounts(&protocol::Amounts::new(input, output)),
                    redeeming,
                )))
            }
            StepKind::Book {
                book_in,
                book_out,
                domain,
                owner_pays_transfer_fee,
                ..
            } => {
                let book = crate::domain::ripple_calc::book_step::Book {
                    r#in: *book_in,
                    out: *book_out,
                    domain: *domain,
                };
                crate::domain::ripple_calc::book_step::book_quality_upper_bound(
                    view,
                    &book,
                    context.quality_threshold,
                    &context.amm_context,
                    *owner_pays_transfer_fee,
                    previous_redeems,
                    context.strand_dst,
                    context.strand_deliver,
                )
                .map(|quality| quality.map(|quality| (quality, false)))
            }
        }
    }
}

fn quality_one() -> Quality {
    let one = STAmount::from_xrp_amount(XRPAmount::from_drops(1));
    Quality::from_amounts(&protocol::Amounts::new(one.clone(), one))
}

fn normalize_amount_asset(amount: &STAmount, asset: Asset) -> STAmount {
    if amount.asset() == asset {
        return amount.clone();
    }
    STAmount::new_with_asset(
        sf("sfAmount"),
        asset,
        amount.mantissa(),
        amount.exponent(),
        amount.negative(),
    )
}

fn unlimited_amount(asset: Asset) -> STAmount {
    if asset.native() {
        // The maximum valid XRPAmount is well above any practical ledger
        // balance and avoids a cross-asset sentinel.
        STAmount::from_xrp_amount(XRPAmount::from_drops(
            protocol::ST_AMOUNT_MAX_NATIVE_NETWORK as i64,
        ))
    } else if let Asset::MPTIssue(issue) = asset {
        STAmount::from_mpt_amount(
            sf("sfAmount"),
            protocol::MPTAmount::from_value(protocol::MAX_MP_TOKEN_AMOUNT),
            issue,
        )
    } else {
        STAmount::new_with_asset(sf("sfAmount"), asset, u64::MAX / 2, 0, false)
    }
}

/// Execute the issuer boundary used by MPT payment strands.  MPTs do not
/// ripple through arbitrary accounts: every endpoint is holder<->issuer and
/// holder-to-holder delivery is represented by two endpoint steps.  When the
/// second step follows a redeem, its input includes the issuance transfer fee
/// while its output is the amount credited to the destination.
#[allow(clippy::too_many_arguments)]
fn execute_mpt_endpoint<V: ApplyView>(
    view: &mut V,
    src: &AccountID,
    dst: &AccountID,
    issue: &protocol::MPTIssue,
    requested: &STAmount,
    is_first: bool,
    is_last: bool,
    offer_crossing: bool,
    previous_redeems: bool,
    strand_src: &AccountID,
    strand_dst: &AccountID,
    strand_deliver: Asset,
    reverse: bool,
) -> Result<(STAmount, STAmount), Ter> {
    let issuer = issue.issuer();
    if src == dst || ((*src != issuer) == (*dst != issuer)) {
        return Err(Ter::TEM_BAD_PATH);
    }
    if view
        .read(protocol::account_keylet(
            basics::base_uint::Uint160::from_void(src.data()),
        ))
        .map_err(|_| Ter::TEF_BAD_LEDGER)?
        .is_none()
    {
        return Err(Ter::TER_NO_ACCOUNT);
    }

    // A one-step pure issue/redeem is allowed through a global lock.  On a
    // multi-step path the source endpoint observes global+individual lock,
    // while the destination endpoint observes only its individual lock.
    if !(is_first && is_last) {
        let locked = if is_first {
            crate::mptoken_helpers::is_global_frozen_mpt(view, issue)
                .map_err(|_| Ter::TEF_BAD_LEDGER)?
                || crate::mptoken_helpers::is_individual_frozen_mpt(view, src, issue)
                    .map_err(|_| Ter::TEF_BAD_LEDGER)?
        } else {
            crate::mptoken_helpers::is_individual_frozen_mpt(view, dst, issue)
                .map_err(|_| Ter::TEF_BAD_LEDGER)?
        };
        if locked {
            return Err(Ter::TEC_LOCKED);
        }
    }

    if !offer_crossing
        && strand_deliver == Asset::MPTIssue(*issue)
        && *strand_src != issuer
        && *strand_dst != issuer
    {
        let transfer =
            crate::mptoken_helpers::can_transfer_mpt(view, issue, strand_src, strand_dst)
                .map_err(|_| Ter::TEF_BAD_LEDGER)?;
        if transfer != Ter::TES_SUCCESS {
            return Err(transfer);
        }
    }

    if offer_crossing && *dst != issuer {
        let key = protocol::mptoken_keylet_from_mptid(
            issue.mpt_id(),
            basics::base_uint::Uint160::from_void(dst.data()),
        );
        if view.read(key).map_err(|_| Ter::TEF_BAD_LEDGER)?.is_none() {
            let created = crate::mptoken_helpers::check_create_mpt(view, issue, dst)
                .map_err(|_| Ter::TEF_BAD_LEDGER)?;
            if created != Ter::TES_SUCCESS && created != Ter::TEC_DUPLICATE {
                return Err(created);
            }
        }
    }

    for account in [src, dst] {
        if *account != issuer {
            let auth = crate::mptoken_helpers::require_auth_mpt_with_type(
                view,
                issue,
                account,
                crate::mptoken_helpers::MPTAuthType::Strong,
            )
            .map_err(|_| Ter::TEF_BAD_LEDGER)?;
            if auth != Ter::TES_SUCCESS {
                return Err(auth);
            }
        }
    }

    let requested_value = requested.mpt().value().max(0);
    let issuing_with_fee = *src == issuer && previous_redeems;
    let rate = if issuing_with_fee {
        crate::mptoken_helpers::transfer_rate_mpt(view, issue.mpt_id())
            .map_err(|_| Ter::TEF_BAD_LEDGER)?
    } else {
        protocol::PARITY_RATE
    };

    let (mut input_value, mut output_value) = if reverse {
        let input = if issuing_with_fee {
            protocol::multiply_round(requested, rate, true)
                .mpt()
                .value()
        } else {
            requested_value
        };
        (input, requested_value)
    } else {
        let output = if issuing_with_fee {
            protocol::divide_round(requested, rate, false).mpt().value()
        } else {
            requested_value
        };
        (requested_value, output)
    };

    let issuance = view
        .read(protocol::mpt_issuance_keylet_from_mptid(issue.mpt_id()))
        .map_err(|_| Ter::TEF_BAD_LEDGER)?
        .ok_or(Ter::TEC_OBJECT_NOT_FOUND)?;
    let available = if *src == issuer {
        // During reverse evaluation a preceding holder -> issuer endpoint will
        // redeem supply before this endpoint issues it again.  rippled quotes
        // that non-initial issuer endpoint against MaximumAmount rather than
        // today's issuance headroom, preventing a maxed-out issuance from
        // incorrectly making holder -> issuer -> holder strands dry.
        if is_first {
            crate::mptoken_helpers::available_mpt_amount(&issuance)
        } else {
            crate::mptoken_helpers::max_mpt_amount(&issuance)
        }
    } else {
        view.read(protocol::mptoken_keylet_from_mptid(
            issue.mpt_id(),
            basics::base_uint::Uint160::from_void(src.data()),
        ))
        .map_err(|_| Ter::TEF_BAD_LEDGER)?
        .map_or(0, |token| token.get_field_u64(sf("sfMPTAmount")) as i64)
    };
    if output_value > available && *src == issuer {
        output_value = available.max(0);
        input_value = if issuing_with_fee {
            let limited = STAmount::from_mpt_amount(
                sf("sfAmount"),
                protocol::MPTAmount::from_value(output_value),
                *issue,
            );
            protocol::multiply_round(&limited, rate, true).mpt().value()
        } else {
            output_value
        };
    } else if input_value > available && *src != issuer {
        input_value = available.max(0);
        output_value = input_value;
    }
    if input_value <= 0 || output_value <= 0 {
        return Ok((requested.zeroed(), requested.zeroed()));
    }

    let input = STAmount::from_mpt_amount(
        sf("sfAmount"),
        protocol::MPTAmount::from_value(input_value),
        *issue,
    );
    let output = STAmount::from_mpt_amount(
        sf("sfAmount"),
        protocol::MPTAmount::from_value(output_value),
        *issue,
    );
    let sent = ripple_state_helpers::account_send(view, src, dst, &output);
    if sent != Ter::TES_SUCCESS {
        return Err(sent);
    }
    Ok((input, output))
}

/// Limits delivery to trust-line capacity.  It is used by both directions;
/// reverse execution requests an output and receives the asset-correct input
/// that would be consumed by forward execution.
fn execute_direct_fwd<V: ApplyView>(
    view: &mut V,
    src: &AccountID,
    dst: &AccountID,
    input: &STAmount,
    strand_dst: &AccountID,
    offer_crossing: bool,
) -> Result<(STAmount, STAmount), Ter> {
    if input.signum() <= 0 {
        return Ok((input.zeroed(), input.zeroed()));
    }

    if input.native() {
        let result = ripple_state_helpers::account_send(view, src, dst, input);
        if result != Ter::TES_SUCCESS {
            return Err(result);
        }
        return Ok((input.clone(), input.clone()));
    }

    let currency = input.issue().currency;
    let is_final_offer_crossing_step = offer_crossing && dst == strand_dst;
    let (max_flow, debt_dir) = if is_final_offer_crossing_step {
        // DirectIOfferCrossingStep::maxFlow returns the requested amount for
        // its last step. Offer crossing is allowed to exceed (or create) the
        // taker's trust line, unlike an ordinary Payment path.
        (
            input.iou(),
            crate::domain::ripple_calc::direct_step::DebtDirection::Issues,
        )
    } else {
        crate::domain::ripple_calc::direct_step::max_payment_flow(view, src, dst, currency)
            .map_err(|_| Ter::TEF_BAD_LEDGER)?
    };
    if max_flow.is_zero() || max_flow.signum() <= 0 {
        return Ok((input.zeroed(), input.zeroed()));
    }

    let input_iou = input.iou();
    let step_issue = Issue {
        currency,
        account: if debt_dir == crate::domain::ripple_calc::direct_step::DebtDirection::Redeems {
            *dst
        } else {
            *src
        },
    };
    // A holder returning an IOU to its issuer does not pay the issuer's
    // transfer rate. In rippled this is a one-step DirectStep whose
    // `qualitiesSrcRedeems` has no previous step and therefore returns
    // QUALITY_ONE. The Rust flow executor accounts for a multi-hop transfer
    // fee at the redemption boundary, so preserve that representation while
    // exempting the terminal issuer redemption.
    let rate = if offer_crossing {
        // DirectIOfferCrossingStep ignores trust-line QualityIn/QualityOut.
        crate::domain::mul_ratio::QUALITY_ONE
    } else if debt_dir == crate::domain::ripple_calc::direct_step::DebtDirection::Redeems
        && dst != strand_dst
    {
        ripple_state_helpers::try_transfer_rate(view, dst).map_err(|_| Ter::TEF_BAD_LEDGER)?
    } else {
        crate::domain::mul_ratio::QUALITY_ONE
    };
    let has_rate = rate > crate::domain::mul_ratio::QUALITY_ONE;
    let effective_max = if has_rate {
        crate::domain::mul_ratio::mul_ratio(
            max_flow,
            crate::domain::mul_ratio::QUALITY_ONE,
            rate,
            false,
        )
    } else {
        max_flow
    };
    let deliver_iou = input_iou.min(effective_max);
    let deliver = STAmount::from_iou_amount(sf("sfAmount"), deliver_iou, step_issue);
    if deliver.signum() <= 0 {
        return Ok((input.zeroed(), input.zeroed()));
    }
    let consumed = if has_rate {
        let adjusted_iou = crate::domain::mul_ratio::mul_ratio(
            deliver_iou,
            rate,
            crate::domain::mul_ratio::QUALITY_ONE,
            true,
        );
        STAmount::from_iou_amount(sf("sfAmount"), adjusted_iou, step_issue)
    } else {
        deliver.clone()
    };
    let result = ripple_state_helpers::account_send(view, src, dst, &consumed);
    if result != Ter::TES_SUCCESS {
        return Err(result);
    }
    Ok((consumed, deliver))
}

fn execute_xrp_endpoint_fwd<V: ApplyView>(
    view: &mut V,
    account: &AccountID,
    is_last: bool,
    input: &STAmount,
) -> Result<(STAmount, STAmount), Ter> {
    let drops = input.xrp().drops();
    if drops <= 0 {
        let zero = STAmount::from_xrp_amount(XRPAmount::from_drops(0));
        return Ok((zero.clone(), zero));
    }
    let actual_drops = if !is_last {
        drops.min(xrp_liquid(view, account).map_err(|_| Ter::TEF_BAD_LEDGER)?)
    } else {
        drops
    };
    if actual_drops <= 0 {
        let zero = STAmount::from_xrp_amount(XRPAmount::from_drops(0));
        return Ok((zero.clone(), zero));
    }
    let sender = if is_last { xrp_account() } else { *account };
    let receiver = if is_last { *account } else { xrp_account() };
    let ter = ripple_state_helpers::transfer_xrp(
        view,
        &sender,
        &receiver,
        XRPAmount::from_drops(actual_drops),
    );
    if ter != Ter::TES_SUCCESS {
        return Err(ter);
    }
    // XRPEndpointStep is typed as XRPAmount in rippled.  Its reverse pass may
    // carry OfferCreate's internal kMaxNative sentinel, which is intentionally
    // larger than the network-serializable STAmount limit.  Keep that probe
    // value raw; the limiting forward pass constrains it before commit.
    let amount = STAmount::new_native(actual_drops.unsigned_abs(), actual_drops < 0);
    Ok((amount.clone(), amount))
}

fn xrp_liquid<V: ApplyView>(view: &mut V, account: &AccountID) -> Result<i64, ViewError> {
    let acct_keylet =
        protocol::account_keylet(basics::base_uint::Uint160::from_void(account.data()));
    let Some(sle) = view.peek(acct_keylet)? else {
        return Ok(0);
    };
    let balance = view
        .balance_hook_iou(
            *account,
            xrp_account(),
            sle.get_field_amount(sf("sfBalance")),
        )
        .xrp()
        .drops();
    let reserve = if crate::is_pseudo_account(&sle) {
        0
    } else {
        let owner_count = view
            .owner_count_hook(*account, crate::OwnerCounts::from_sle(&sle))
            .count();
        crate::effective_account_reserve_with_owner_count(view.fees(), &sle, owner_count, 0, 0)
            as i64
    };
    Ok((balance - reserve).max(0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ApplyView, ApplyViewImpl, Ledger, RawView};
    use protocol::ApplyFlags;
    use std::sync::Arc;

    #[test]
    fn tagged_amount_rejects_cross_asset_send_max_comparison() {
        let issuer = AccountID::from_array([9; 20]);
        let usd = protocol::currency_from_string("USD");
        let required = StepAmount::new(STAmount::from_iou_amount(
            sf("sfAmount"),
            protocol::IOUAmount::from_parts(10, 0).expect("valid iou"),
            Issue::new(usd, issuer),
        ));
        let xrp_send_max = STAmount::from_xrp_amount(XRPAmount::from_drops(1_000_000));

        assert_eq!(required.greater_than(&xrp_send_max), None);
    }

    #[test]
    fn book_step_reaching_offer_cap_marks_strand_inactive() {
        let input = STAmount::from_xrp_amount(XRPAmount::from_drops(1));
        let output = STAmount::from_xrp_amount(XRPAmount::from_drops(1));
        assert!(!StepAmounts::book(input.clone(), output.clone(), 999).inactive);
        let capped = StepAmounts::book(input, output, 1000);
        assert!(capped.inactive);
        assert_eq!(capped.offers_used, 1000);
    }

    #[test]
    fn final_offer_crossing_direct_step_may_create_the_taker_trust_line() {
        let issuer = AccountID::from_array([0x31; 20]);
        let taker = AccountID::from_array([0x42; 20]);
        let currency = protocol::currency_from_string("USD");
        let mut base = Ledger::from_ledger_seq_and_close_time(1, 1, false);
        for account in [issuer, taker] {
            let keylet =
                protocol::account_keylet(basics::base_uint::Uint160::from_void(account.data()));
            let mut root = protocol::STLedgerEntry::new(keylet);
            root.set_field_amount(
                sf("sfBalance"),
                STAmount::from_xrp_amount(XRPAmount::from_drops(100_000_000)),
            );
            root.set_field_u32(sf("sfOwnerCount"), 0);
            root.set_field_u32(sf("sfSequence"), 1);
            base.raw_insert(Arc::new(root)).expect("seed account root");
        }
        let mut view = ApplyViewImpl::new(Arc::new(base), ApplyFlags::NONE);
        let requested = STAmount::from_iou_amount(
            sf("sfAmount"),
            protocol::IOUAmount::from_parts(1, 0).expect("valid amount"),
            Issue::new(currency, issuer),
        );

        let (input, output) =
            execute_direct_fwd(&mut view, &issuer, &taker, &requested, &taker, true)
                .expect("offer crossing direct step");

        assert_eq!(input, requested);
        assert_eq!(output, requested);
        assert!(
            view.peek(protocol::line(issuer, taker, currency))
                .expect("trust line lookup")
                .is_some(),
            "DirectIOfferCrossingStep must create the taker's absent line"
        );
    }
}
