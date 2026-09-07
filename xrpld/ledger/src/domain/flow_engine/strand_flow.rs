//! Reverse-then-forward strand execution.
//!
//! This follows rippled's `StrandFlow.h`: evaluate a candidate in reverse to
//! discover its asset-correct required input and first limiting step, discard
//! that probe sandbox, then replay the limiting suffix/prefix in a fresh
//! sandbox.  Only a successful chosen strand is applied to its parent view.

use super::steps::{FlowStep, StepAmount, StepAmounts, StepContext};
use super::{AmmContext, FlowResult, SelfCrossCancellation, Strand};
use crate::domain::ripple_calc::OfferCrossing;
use crate::{ApplyView, FlowSandbox, ViewError};
use protocol::{AccountID, Quality, STAmount, Ter};
use std::{cell::Cell, rc::Rc};

const MAX_TRIES: usize = 1000;
const MAX_OFFERS_TO_CONSIDER: u32 = 1500;

#[derive(Debug, Clone)]
struct ReverseProbe {
    cache: Vec<Option<StepAmounts>>,
    limiting_step: Option<usize>,
    // `true` is the special `maxIn` limiter at step zero.  The final run must
    // call fwd on step zero, rather than comparing it to a differently issued
    // deliver amount.
    limited_by_max_in: bool,
}

struct SingleStrandResult {
    amounts: Option<(STAmount, STAmount, bool)>,
    offers_used: u32,
}

/// Execute strands to deliver the requested amount.
pub fn execute_strands<V: ApplyView>(
    view: &mut V,
    strands: &[Strand],
    deliver: &STAmount,
    partial_payment: bool,
    offer_crossing: OfferCrossing,
    send_max: Option<&STAmount>,
    strand_src: &AccountID,
    strand_dst: &AccountID,
    quality_threshold: Option<Quality>,
    self_cross_cancellation: Option<SelfCrossCancellation>,
) -> FlowResult {
    let fill_or_kill_enabled = view.rules().enabled(&protocol::feature_id("fixFillOrKill"));
    if strands.is_empty() {
        return FlowResult {
            ter: Ter::TEC_PATH_DRY,
            actual_in: send_max
                .map(STAmount::zeroed)
                .unwrap_or_else(|| deliver.zeroed()),
            actual_out: deliver.zeroed(),
        };
    }

    // The aggregate flow is also transactional. Individual chosen strands
    // apply only to this sandbox; an overall PATH_PARTIAL/PATH_DRY drops all
    // of them exactly as rippled's finishFlow drops its returned sandbox.
    let mut aggregate = FlowSandbox::new(view);
    let mut remaining_out = deliver.clone();
    let mut remaining_in = send_max.cloned();
    let mut total_in = send_max
        .map(STAmount::zeroed)
        .unwrap_or_else(|| deliver.zeroed());
    let mut total_out = deliver.zeroed();
    // rippled deliberately retains every liquidity-pass amount in a
    // flat_multiset and re-sums from smallest to largest. Issued-currency
    // addition canonicalizes to finite precision, so accumulating in strand
    // processing order is not associative and can change consensus results.
    let mut saved_ins = Vec::with_capacity(MAX_TRIES);
    let mut saved_outs = Vec::with_capacity(MAX_TRIES);
    let mut active: Vec<bool> = vec![true; strands.len()];
    // Flow.cpp sets the initial AMM mode from all constructed strands before
    // StrandFlow performs its first quality estimate.
    let amm_context = AmmContext::new(*strand_src, strands.len() > 1);
    let mut offers_considered = 0u32;

    for attempt in 0..MAX_TRIES {
        if remaining_out.signum() <= 0 || remaining_in.as_ref().is_some_and(|v| v.signum() <= 0) {
            break;
        }
        // StrandFlow increments curTry before processing and fails when it
        // reaches MAX_TRIES, so the terminal attempt is never executed.
        if attempt + 1 >= MAX_TRIES {
            return FlowResult {
                ter: Ter::TEL_FAILED_PROCESSING,
                actual_in: total_in.zeroed(),
                actual_out: total_out.zeroed(),
            };
        }

        let active_indices: Vec<usize> = active
            .iter()
            .enumerate()
            .filter(|(index, enabled)| **enabled && !strands[*index].is_empty())
            .map(|(index, _)| index)
            .collect();
        // Match ActiveStrands::activateNext/StrandFlow: AMM offer generation
        // and quality estimation for this pass must observe the active-strand
        // mode, not the mode left behind by the preceding pass.
        amm_context.set_multi_path(active_indices.len() > 1);
        let ordering_context = StepContext {
            strand_src,
            strand_dst,
            strand_deliver: deliver.asset(),
            offer_crossing: offer_crossing != OfferCrossing::No,
            quality_threshold,
            self_cross_cancellation: self_cross_cancellation.clone(),
            amm_context: amm_context.clone(),
            offer_usage: Rc::new(Cell::new(0)),
            previous_redeems: Rc::new(Cell::new(false)),
            has_previous_step: Rc::new(Cell::new(false)),
            previous_step_is_book: Rc::new(Cell::new(false)),
        };
        let mut candidates = match activate_candidates(active_indices, |index| {
            strand_quality_upper_bound(&mut aggregate, &strands[index], &ordering_context).map(
                |quality| {
                    quality
                        .filter(|quality| quality_threshold.is_none_or(|limit| *quality >= limit))
                },
            )
        }) {
            Ok(candidates) => candidates,
            Err(_) => {
                return FlowResult {
                    ter: Ter::TEF_BAD_LEDGER,
                    actual_in: total_in.zeroed(),
                    actual_out: total_out.zeroed(),
                };
            }
        };
        // `sort_by` is stable: equal-quality strands retain path-set order.
        sort_candidates(&mut candidates);
        // `candidates` is the Rust ActiveStrands::cur_ after theoretical
        // quality/limit pruning. This is the value used by execution and by
        // the one-active-strand nonlinear limitOut calculation.
        amm_context.set_multi_path(candidates.len() > 1);

        let mut applied = false;
        let mut next_active = vec![false; strands.len()];
        for (candidate_position, (strand_index, _)) in candidates.iter().copied().enumerate() {
            let strand = &strands[strand_index];

            let (strand_out, adjusted_remaining_out) = if candidates.len() == 1 {
                let limited = match quality_threshold {
                    Some(limit) => match limit_single_strand_out(
                        &mut aggregate,
                        strand,
                        &remaining_out,
                        limit,
                        &ordering_context,
                    ) {
                        Ok(limited) => limited,
                        Err(_) => {
                            return FlowResult {
                                ter: Ter::TEF_BAD_LEDGER,
                                actual_in: total_in.zeroed(),
                                actual_out: total_out.zeroed(),
                            };
                        }
                    },
                    None => None,
                };
                limited.unwrap_or_else(|| (remaining_out.clone(), false))
            } else {
                (remaining_out.clone(), false)
            };

            // ActiveStrands deliberately avoids estimating/sorting when only
            // one strand is active. rippled still computes limitOut and then
            // performs this second OfferCreate qualityUpperBound check before
            // executing the candidate. Without it, a lone below-limit book
            // enters FlowOfferStream and can permanently prune expired or
            // unfunded offers that rippled never reaches.
            if offer_crossing != OfferCrossing::No
                && let Some(limit) = quality_threshold
            {
                let upper_bound =
                    match strand_quality_upper_bound(&mut aggregate, strand, &ordering_context) {
                        Ok(quality) => quality,
                        Err(_) => {
                            return FlowResult {
                                ter: Ter::TEF_BAD_LEDGER,
                                actual_in: total_in.zeroed(),
                                actual_out: total_out.zeroed(),
                            };
                        }
                    };
                if !offer_crossing_candidate_meets_limit(offer_crossing, Some(limit), upper_bound) {
                    continue;
                }
            }

            // Every candidate, including a dry probe, owns a child sandbox.
            // No mutation reaches `view` unless this candidate produced a
            // valid amount and was selected below.
            amm_context.clear();
            let result = match execute_single_strand(
                &mut aggregate,
                strand,
                remaining_in.as_ref(),
                &strand_out,
                strand_src,
                strand_dst,
                quality_threshold,
                offer_crossing != OfferCrossing::No,
                self_cross_cancellation.clone(),
                amm_context.clone(),
                adjusted_remaining_out,
            ) {
                Ok(result) => result,
                Err(ter) => {
                    return FlowResult {
                        ter,
                        actual_in: total_in.zeroed(),
                        actual_out: total_out.zeroed(),
                    };
                }
            };

            offers_considered = offers_considered.saturating_add(result.offers_used);
            let Some((amount_in, amount_out, inactive)) = result.amounts else {
                active[strand_index] = false;
                continue;
            };
            if amount_out.signum() <= 0 {
                active[strand_index] = false;
                continue;
            }

            insert_sorted(&mut saved_ins, amount_in);
            insert_sorted(&mut saved_outs, amount_out);
            total_in = sum_sorted(&saved_ins, &total_in);
            total_out = sum_sorted(&saved_outs, &total_out);
            remaining_out = deliver.clone() - total_out.clone();
            if let Some(send_max) = send_max {
                remaining_in = Some(send_max.clone() - total_in.clone());
            }
            if inactive {
                next_active[strand_index] = false;
            } else {
                next_active[strand_index] = true;
            }
            for (remaining_index, _) in candidates.iter().skip(candidate_position + 1) {
                next_active[*remaining_index] = true;
            }
            applied = true;
            amm_context.update();
            break;
        }

        active = next_active;

        if !applied || offers_considered >= MAX_OFFERS_TO_CONSIDER {
            break;
        }
    }

    let result = if let Some(ter) = incomplete_offer_crossing_result(
        &total_out,
        deliver,
        partial_payment,
        offer_crossing,
        remaining_in.as_ref(),
        fill_or_kill_enabled,
    ) {
        FlowResult {
            ter,
            actual_in: total_in,
            actual_out: total_out,
        }
    } else {
        FlowResult {
            ter: Ter::TES_SUCCESS,
            actual_in: total_in,
            actual_out: total_out,
        }
    };

    if result.ter == Ter::TES_SUCCESS && aggregate.apply().is_err() {
        return FlowResult {
            ter: Ter::TEF_INTERNAL,
            actual_in: deliver.zeroed(),
            actual_out: deliver.zeroed(),
        };
    }
    result
}

fn insert_sorted(amounts: &mut Vec<STAmount>, amount: STAmount) {
    let index = amounts.partition_point(|saved| saved <= &amount);
    amounts.insert(index, amount);
}

fn sum_sorted(amounts: &[STAmount], zero: &STAmount) -> STAmount {
    let Some((first, rest)) = amounts.split_first() else {
        return zero.zeroed();
    };
    rest.iter()
        .cloned()
        .fold(first.clone(), |sum, amount| sum + amount)
}

fn incomplete_offer_crossing_result(
    total_out: &STAmount,
    deliver: &STAmount,
    partial_payment: bool,
    offer_crossing: OfferCrossing,
    remaining_in: Option<&STAmount>,
    fill_or_kill_enabled: bool,
) -> Option<Ter> {
    if total_out != deliver {
        if total_out > deliver {
            return Some(Ter::TEF_EXCEPTION);
        }
        if !partial_payment {
            if offer_crossing == OfferCrossing::No
                || (fill_or_kill_enabled && offer_crossing != OfferCrossing::Sell)
            {
                return Some(Ter::TEC_PATH_PARTIAL);
            }
        } else if total_out.signum() == 0 {
            return Some(Ter::TEC_PATH_DRY);
        }
    }

    if offer_crossing != OfferCrossing::No
        && !partial_payment
        && (!fill_or_kill_enabled || offer_crossing == OfferCrossing::Sell)
    {
        return remaining_in
            .is_some_and(|amount| amount.signum() > 0)
            .then_some(Ter::TEC_PATH_PARTIAL);
    }
    None
}

/// Run one strand against two nested sandboxes: a discarded reverse probe and
/// a fresh final sandbox.  This reset is the Rust equivalent of rippled's
/// `sb.emplace(&baseView)` when a limiting step is discovered.
fn execute_single_strand<V: ApplyView>(
    parent: &mut V,
    strand: &Strand,
    max_in: Option<&STAmount>,
    requested_out: &STAmount,
    strand_src: &AccountID,
    strand_dst: &AccountID,
    quality_threshold: Option<Quality>,
    offer_crossing: bool,
    self_cross_cancellation: Option<SelfCrossCancellation>,
    amm_context: AmmContext,
    adjusted_remaining_out: bool,
) -> Result<SingleStrandResult, Ter> {
    let offer_usage = Rc::new(Cell::new(0));
    let preceding_redeems =
        preceding_debt_directions(parent, strand).map_err(|_| Ter::TEF_BAD_LEDGER)?;
    let context = StepContext {
        strand_src,
        strand_dst,
        strand_deliver: requested_out.asset(),
        offer_crossing,
        quality_threshold,
        self_cross_cancellation,
        amm_context,
        offer_usage: offer_usage.clone(),
        previous_redeems: Rc::new(Cell::new(false)),
        has_previous_step: Rc::new(Cell::new(false)),
        previous_step_is_book: Rc::new(Cell::new(false)),
    };

    let Some(probe) = ({
        let mut dry_sandbox = FlowSandbox::new(parent);
        reverse_probe(
            &mut dry_sandbox,
            strand,
            max_in,
            requested_out,
            &context,
            &preceding_redeems,
        )?
    }) else {
        return Ok(SingleStrandResult {
            amounts: None,
            offers_used: offer_usage.get(),
        });
    };
    // `dry_sandbox` was deliberately dropped without `apply`.

    offer_usage.set(0);
    let mut final_sandbox = FlowSandbox::new(parent);
    let Some(final_cache) = replay_probe(
        &mut final_sandbox,
        strand,
        max_in,
        requested_out,
        &context,
        &probe,
        &preceding_redeems,
    )?
    else {
        return Ok(SingleStrandResult {
            amounts: None,
            offers_used: offer_usage.get(),
        });
    };

    let Some(first) = final_cache.first().and_then(Option::as_ref) else {
        return Ok(SingleStrandResult {
            amounts: None,
            offers_used: offer_usage.get(),
        });
    };
    let Some(last) = final_cache.last().and_then(Option::as_ref) else {
        return Ok(SingleStrandResult {
            amounts: None,
            offers_used: offer_usage.get(),
        });
    };
    if first.input.is_zero() || last.output.is_zero() {
        return Ok(SingleStrandResult {
            amounts: None,
            offers_used: offer_usage.get(),
        });
    }

    let amount_in = first.input.amount().clone();
    let amount_out = last.output.amount().clone();
    if let Some(limit) = quality_threshold {
        let realized = Quality::from_amounts(&protocol::Amounts::new(
            amount_in.clone(),
            amount_out.clone(),
        ));
        if realized < limit
            && !(adjusted_remaining_out
                && crate::domain::amm_helpers::within_relative_distance_quality(
                    realized,
                    limit,
                    basics::number::NumberParts::from_i64_and_exponent(1, -7),
                ))
        {
            return Ok(SingleStrandResult {
                amounts: None,
                offers_used: offer_usage.get(),
            });
        }
    }

    let inactive = final_cache.iter().flatten().any(|amounts| amounts.inactive);
    // A successful strand alone is allowed to affect the accumulated parent.
    // This parent can itself be the transaction-level flow sandbox.
    if final_sandbox.apply().is_err() {
        return Err(Ter::TEF_INTERNAL);
    }
    Ok(SingleStrandResult {
        amounts: Some((amount_in, amount_out, inactive)),
        offers_used: offer_usage.get(),
    })
}

fn limit_single_strand_out<V: ApplyView>(
    view: &mut V,
    strand: &Strand,
    remaining_out: &STAmount,
    limit: Quality,
    context: &StepContext<'_>,
) -> Result<Option<(STAmount, bool)>, ViewError> {
    use protocol::{QualityFunction, QualityFunctionClobLikeTag};
    let mut combined: Option<QualityFunction> = None;
    let mut previous_redeems = false;
    for step in strand {
        let (qf, direction) = match step {
            super::StepKind::Book {
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
                let Some(function) = crate::domain::ripple_calc::book_step::book_quality_function(
                    view,
                    &book,
                    context.quality_threshold,
                    &context.amm_context,
                    *owner_pays_transfer_fee,
                    previous_redeems,
                    context.strand_dst,
                    context.strand_deliver,
                )?
                else {
                    return Ok(None);
                };
                (function, false)
            }
            _ => {
                let Some((quality, direction)) =
                    step.quality_upper_bound(view, previous_redeems, context)?
                else {
                    return Ok(None);
                };
                (
                    QualityFunction::from_quality(quality, QualityFunctionClobLikeTag),
                    direction,
                )
            }
        };
        if let Some(current) = &mut combined {
            current.combine(&qf);
        } else {
            combined = Some(qf);
        }
        previous_redeems = direction;
    }
    let Some(qf) = combined else {
        return Ok(None);
    };
    if qf.is_const() {
        return Ok(None);
    }
    let Some(continuous) = qf.out_from_avg_q(limit) else {
        return Ok(None);
    };
    let out = protocol::to_amount_from_number::<STAmount>(
        remaining_out.asset(),
        continuous,
        basics::number::RoundingMode::ToNearest,
    )
    .ok();
    let Some(mut out) = out else {
        return Ok(None);
    };
    if view.rules().enabled(&protocol::feature_id("MPTokensV2"))
        && (remaining_out.native() || matches!(remaining_out.asset(), protocol::Asset::MPTIssue(_)))
        && crate::domain::amm_helpers::stamount_as_number(&out) > continuous
        && !qf.satisfies_avg_q(limit, crate::domain::amm_helpers::stamount_as_number(&out))
    {
        let adjusted = protocol::to_amount_from_number::<STAmount>(
            remaining_out.asset(),
            continuous,
            basics::number::RoundingMode::Downward,
        )
        .ok();
        let Some(adjusted) = adjusted else {
            return Ok(None);
        };
        out = adjusted;
    }
    if crate::domain::amm_helpers::within_relative_distance_amount(
        out.clone(),
        remaining_out.clone(),
        basics::number::NumberParts::from_i64_and_exponent(1, -9),
    ) {
        return Ok(None);
    }
    Ok((out < *remaining_out).then_some((out, true)))
}

fn preceding_debt_directions<V: ApplyView>(
    view: &mut V,
    strand: &Strand,
) -> Result<Vec<bool>, ViewError> {
    use crate::domain::ripple_calc::direct_step::{DebtDirection, max_payment_flow};
    let mut result = Vec::with_capacity(strand.len());
    let mut previous_redeems = false;
    for step in strand {
        result.push(previous_redeems);
        previous_redeems = match step {
            super::StepKind::Direct { src, dst, currency } => {
                max_payment_flow(view, src, dst, *currency)?.1 == DebtDirection::Redeems
            }
            super::StepKind::MptEndpoint { src, issue, .. } => *src != issue.issuer(),
            super::StepKind::Book { .. } | super::StepKind::XrpEndpoint { .. } => false,
        };
    }
    Ok(result)
}

fn strand_quality_upper_bound<V: ApplyView>(
    view: &mut V,
    strand: &Strand,
    context: &StepContext<'_>,
) -> Result<Option<Quality>, ViewError> {
    let mut quality = {
        let one = STAmount::from_xrp_amount(protocol::XRPAmount::from_drops(1));
        Quality::from_amounts(&protocol::Amounts::new(one.clone(), one))
    };
    let mut previous_redeems = false;
    for step in strand {
        let Some((step_quality, direction)) =
            step.quality_upper_bound(view, previous_redeems, context)?
        else {
            return Ok(None);
        };
        quality = protocol::composed_quality(quality, step_quality);
        previous_redeems = direction;
    }
    Ok(Some(quality))
}

fn sort_candidates(candidates: &mut [(usize, Quality)]) {
    candidates.sort_by(|lhs, rhs| rhs.1.cmp(&lhs.1));
}

fn quality_estimation_required(active_count: usize) -> bool {
    active_count > 1
}

fn offer_crossing_candidate_meets_limit(
    offer_crossing: OfferCrossing,
    limit: Option<Quality>,
    upper_bound: Option<Quality>,
) -> bool {
    offer_crossing == OfferCrossing::No
        || limit.is_none()
        || upper_bound.is_some_and(|quality| quality >= limit.expect("limit checked above"))
}

fn activate_candidates(
    active_indices: Vec<usize>,
    mut estimate: impl FnMut(usize) -> Result<Option<Quality>, ViewError>,
) -> Result<Vec<(usize, Quality)>, ViewError> {
    if !quality_estimation_required(active_indices.len()) {
        return Ok(active_indices
            .into_iter()
            .map(|index| (index, Quality::default()))
            .collect());
    }
    let mut candidates = Vec::with_capacity(active_indices.len());
    for index in active_indices {
        if let Some(quality) = estimate(index)? {
            candidates.push((index, quality));
        }
    }
    Ok(candidates)
}

/// Reverse through the strand to discover exact per-step required inputs.
/// Any liquidity or max-input limit records the first limiting step.
fn reverse_probe<V: ApplyView>(
    sandbox: &mut V,
    strand: &Strand,
    max_in: Option<&STAmount>,
    requested_out: &STAmount,
    context: &StepContext<'_>,
    preceding_redeems: &[bool],
) -> Result<Option<ReverseProbe>, Ter> {
    let mut cache = vec![None; strand.len()];
    let mut step_out = StepAmount::new(requested_out.clone());
    let mut limiting_step = None;
    let mut limited_by_max_in = false;

    for index in (0..strand.len()).rev() {
        set_preceding_step_context(context, strand, index, preceding_redeems);
        let amounts = strand[index].rev(sandbox, &step_out, context)?;
        if amounts.output.is_zero() {
            return Ok(None);
        }

        let output_limited = !amounts.output.equivalent(&step_out);

        // rippled tests the first step's SendMax before treating that same
        // step's short output as a liquidity limit. The input is tagged, so a
        // malformed strand cannot turn this into a USD-vs-XRP comparison.
        // Keep replacing a downstream limiter when an earlier step also
        // limits. rippled resets its sandbox and re-executes at every such
        // step while walking backwards, so the final (lowest-index) limiter
        // is the point from which the forward suffix must be replayed.
        if index == 0 {
            if let Some(max_in) = max_in {
                match amounts.input.greater_than(max_in) {
                    Some(true) => {
                        limiting_step = Some(0);
                        limited_by_max_in = true;
                    }
                    Some(false) if output_limited => {
                        limiting_step = Some(index);
                    }
                    Some(false) => {}
                    None => return Ok(None),
                }
            } else if output_limited {
                limiting_step = Some(index);
            }
        } else if output_limited {
            limiting_step = Some(index);
        }

        cache[index] = Some(amounts.clone());
        step_out = amounts.input;
    }

    Ok(Some(ReverseProbe {
        cache,
        limiting_step,
        limited_by_max_in,
    }))
}

/// Replay the amount plan in the fresh sandbox.  This is the exact shape of
/// rippled's post-reset execution: re-run the limiting step, reverse before
/// it, then forward after it.  With no limiter, a complete reverse pass is
/// replayed and its sandbox becomes the result.
fn replay_probe<V: ApplyView>(
    sandbox: &mut V,
    strand: &Strand,
    max_in: Option<&STAmount>,
    requested_out: &STAmount,
    context: &StepContext<'_>,
    probe: &ReverseProbe,
    preceding_redeems: &[bool],
) -> Result<Option<Vec<Option<StepAmounts>>>, Ter> {
    let mut cache = vec![None; strand.len()];

    let limiting = probe.limiting_step.unwrap_or(strand.len());
    if probe.limited_by_max_in {
        let Some(max_in) = max_in else {
            return Ok(None);
        };
        let Some(expected) = probe.cache[0].as_ref() else {
            return Ok(None);
        };
        set_preceding_step_context(context, strand, 0, preceding_redeems);
        let actual = strand[0].fwd(sandbox, &StepAmount::new(max_in.clone()), expected, context)?;
        if actual.output.is_zero() || !actual.input.equivalent(&StepAmount::new(max_in.clone())) {
            return Ok(None);
        }
        cache[0] = Some(actual);
    } else {
        // If the initial reverse pass found a liquidity limit, its reduced
        // output is what must be re-executed after resetting the sandbox.
        let mut step_out = if limiting < strand.len() {
            let Some(amounts) = probe.cache[limiting].as_ref() else {
                return Ok(None);
            };
            amounts.output.clone()
        } else {
            StepAmount::new(requested_out.clone())
        };
        let reverse_start = if limiting < strand.len() {
            limiting
        } else {
            strand.len() - 1
        };

        for index in (0..=reverse_start).rev() {
            set_preceding_step_context(context, strand, index, preceding_redeems);
            let actual = strand[index].rev(sandbox, &step_out, context)?;
            if actual.output.is_zero() || !actual.output.equivalent(&step_out) {
                return Ok(None);
            }
            step_out = actual.input.clone();
            cache[index] = Some(actual);
        }
    }

    let forward_start = if probe.limited_by_max_in {
        1
    } else {
        limiting + 1
    };
    let mut step_in = if probe.limited_by_max_in {
        let Some(amounts) = cache[0].as_ref() else {
            return Ok(None);
        };
        amounts.output.clone()
    } else if limiting < strand.len() {
        let Some(amounts) = cache[limiting].as_ref() else {
            return Ok(None);
        };
        amounts.output.clone()
    } else {
        // No limiting step means the reversed execution already processed all
        // steps.  There is no forward suffix to replay.
        return Ok(Some(cache));
    };

    for index in forward_start..strand.len() {
        set_preceding_step_context(context, strand, index, preceding_redeems);
        let Some(expected) = probe.cache[index].as_ref() else {
            return Ok(None);
        };
        let actual = strand[index].fwd(sandbox, &step_in, expected, context)?;
        if actual.output.is_zero() || !actual.input.equivalent(&step_in) {
            return Ok(None);
        }
        step_in = actual.output.clone();
        cache[index] = Some(actual);
    }

    Ok(Some(cache))
}

fn set_preceding_step_context(
    context: &StepContext<'_>,
    strand: &Strand,
    index: usize,
    preceding_redeems: &[bool],
) {
    context.previous_redeems.set(preceding_redeems[index]);
    context.has_previous_step.set(index != 0);
    context.previous_step_is_book.set(
        index
            .checked_sub(1)
            .and_then(|previous| strand.get(previous))
            .is_some_and(|step| matches!(step, super::StepKind::Book { .. })),
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol::{Issue, XRPAmount, get_field_by_symbol};

    fn sf(name: &str) -> &'static protocol::SField {
        get_field_by_symbol(name)
    }

    #[test]
    fn reverse_send_max_uses_first_step_asset_not_deliver_asset() {
        let issuer = AccountID::from_array([7; 20]);
        let usd = protocol::currency_from_string("USD");
        let required_usd = StepAmount::new(STAmount::from_iou_amount(
            sf("sfAmount"),
            protocol::IOUAmount::from_parts(12, 0).expect("valid iou"),
            Issue::new(usd, issuer),
        ));
        let send_max_usd = STAmount::from_iou_amount(
            sf("sfAmount"),
            protocol::IOUAmount::from_parts(10, 0).expect("valid iou"),
            Issue::new(usd, issuer),
        );
        let deliver_xrp = STAmount::from_xrp_amount(XRPAmount::from_drops(1));

        assert_eq!(required_usd.greater_than(&send_max_usd), Some(true));
        // A USD requirement cannot be numerically compared with an XRP
        // delivery limit; the tagged amount rejects that operation.
        assert_eq!(required_usd.greater_than(&deliver_xrp), None);
    }

    fn quality(input: i64, output: i64) -> Quality {
        Quality::from_amounts(&protocol::Amounts::new(
            STAmount::from_xrp_amount(XRPAmount::from_drops(input)),
            STAmount::from_xrp_amount(XRPAmount::from_drops(output)),
        ))
    }

    #[test]
    fn active_strands_are_stably_sorted_best_quality_first() {
        let equal = quality(2, 3);
        let best = quality(1, 2);
        let mut candidates = vec![(7, equal), (4, best), (2, equal)];
        sort_candidates(&mut candidates);
        assert_eq!(
            candidates.iter().map(|entry| entry.0).collect::<Vec<_>>(),
            vec![4, 7, 2]
        );
    }

    #[test]
    fn resource_caps_match_rippled_flow() {
        assert_eq!(MAX_TRIES, 1000);
        assert_eq!(MAX_OFFERS_TO_CONSIDER, 1500);
    }

    fn iou(mantissa: i64, exponent: i32) -> STAmount {
        let issuer = AccountID::from_array([0x42; 20]);
        STAmount::from_iou_amount(
            sf("sfAmount"),
            protocol::IOUAmount::from_parts(mantissa, exponent).expect("canonical IOU amount"),
            Issue::new(protocol::currency_from_string("USD"), issuer),
        )
    }

    #[test]
    fn sorted_pass_accumulation_preserves_iou_dust() {
        let large = iou(1_000_000_000_000_000, -15);
        let dust = iou(6_000_000_000_000_000, -31);

        // Processing-order accumulation rounds each dust pass separately.
        let processing_order = large.clone() + dust.clone() + dust.clone();

        // rippled's flat_multiset adds both dust passes before the large pass.
        let mut passes = Vec::new();
        insert_sorted(&mut passes, large.clone());
        insert_sorted(&mut passes, dust.clone());
        insert_sorted(&mut passes, dust);
        let canonical = sum_sorted(&passes, &large.zeroed());

        assert_eq!(processing_order, iou(1_000_000_000_000_002, -15));
        assert_eq!(canonical, iou(1_000_000_000_000_001, -15));
    }

    #[test]
    fn sorted_pass_totals_are_independent_of_liquidity_order() {
        let amounts = [
            iou(1_000_000_000_000_000, -15),
            iou(6_000_000_000_000_000, -31),
            iou(6_000_000_000_000_000, -31),
        ];
        let mut forward = Vec::new();
        let mut reverse = Vec::new();
        for amount in amounts.iter().cloned() {
            insert_sorted(&mut forward, amount);
        }
        for amount in amounts.iter().rev().cloned() {
            insert_sorted(&mut reverse, amount);
        }

        assert_eq!(forward, reverse);
        assert_eq!(
            sum_sorted(&forward, &amounts[0].zeroed()),
            sum_sorted(&reverse, &amounts[0].zeroed())
        );
    }

    #[test]
    fn sell_fill_or_kill_completes_when_all_input_is_consumed() {
        let delivered = STAmount::from_xrp_amount(XRPAmount::from_drops(50));
        let unlimited = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
        let zero_in = STAmount::from_xrp_amount(XRPAmount::new());
        let remaining_in = STAmount::from_xrp_amount(XRPAmount::from_drops(1));

        assert_eq!(
            incomplete_offer_crossing_result(
                &delivered,
                &unlimited,
                false,
                OfferCrossing::Sell,
                Some(&zero_in),
                true,
            ),
            None
        );
        assert_eq!(
            incomplete_offer_crossing_result(
                &delivered,
                &unlimited,
                false,
                OfferCrossing::Sell,
                Some(&remaining_in),
                true,
            ),
            Some(Ter::TEC_PATH_PARTIAL)
        );
    }

    #[test]
    fn buy_fill_or_kill_switches_from_input_to_output_completion_at_amendment() {
        let delivered = STAmount::from_xrp_amount(XRPAmount::from_drops(50));
        let requested = STAmount::from_xrp_amount(XRPAmount::from_drops(100));
        let zero_in = STAmount::from_xrp_amount(XRPAmount::new());

        assert_eq!(
            incomplete_offer_crossing_result(
                &delivered,
                &requested,
                false,
                OfferCrossing::Yes,
                Some(&zero_in),
                false,
            ),
            None
        );
        assert_eq!(
            incomplete_offer_crossing_result(
                &delivered,
                &requested,
                false,
                OfferCrossing::Yes,
                Some(&zero_in),
                true,
            ),
            Some(Ter::TEC_PATH_PARTIAL)
        );
    }

    #[test]
    fn amm_context_quality_mode_tracks_active_strands_before_estimation() {
        let context = AmmContext::new(AccountID::from_array([0x31; 20]), true);
        assert!(context.multi_path());

        let active = [2usize, 5usize];
        context.set_multi_path(active.len() > 1);
        let candidates = activate_candidates(active.to_vec(), |_| {
            assert!(context.multi_path());
            Ok(Some(quality(1, 1)))
        })
        .expect("quality estimation succeeds");
        assert_eq!(candidates.len(), 2);

        // A later pass with one surviving strand flips the mode before that
        // pass's quality callback, matching rippled's per-pass update.
        context.set_multi_path(false);
        let candidates = activate_candidates(vec![5], |_| {
            assert!(!context.multi_path());
            Ok(Some(quality(1, 1)))
        })
        .expect("quality estimation succeeds");
        assert_eq!(candidates.len(), 1);
    }

    #[test]
    fn single_active_strand_bypasses_quality_estimation_before_cleanup() {
        assert!(!quality_estimation_required(1));
        assert!(quality_estimation_required(2));
        let candidates = activate_candidates(vec![7], |_| {
            panic!("single-strand activation must not estimate/prune before cleanup")
        })
        .expect("single-strand activation bypasses estimation");
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].0, 7);
    }

    #[test]
    fn single_offer_crossing_strand_still_requires_the_execution_quality_gate() {
        let limit = quality(1, 1);
        let worse = quality(2, 1);
        let equal = limit;

        // ActiveStrands intentionally bypasses estimation for one strand, but
        // rippled StrandFlow checks the bound again before opening the stream.
        let candidates = activate_candidates(vec![7], |_| {
            panic!("single-strand activation must still bypass sorting estimation")
        })
        .expect("single candidate remains active until the execution gate");
        assert_eq!(candidates.len(), 1);
        assert!(!offer_crossing_candidate_meets_limit(
            OfferCrossing::Yes,
            Some(limit),
            Some(worse),
        ));
        assert!(!offer_crossing_candidate_meets_limit(
            OfferCrossing::Yes,
            Some(limit),
            None,
        ));
        assert!(offer_crossing_candidate_meets_limit(
            OfferCrossing::Yes,
            Some(limit),
            Some(equal),
        ));
        assert!(offer_crossing_candidate_meets_limit(
            OfferCrossing::No,
            Some(limit),
            Some(worse),
        ));
    }

    #[test]
    fn quality_estimation_distinguishes_absent_liquidity_from_storage_failure() {
        let absent = activate_candidates(vec![1, 2], |_| Ok(None))
            .expect("absent liquidity is not a storage error");
        assert!(absent.is_empty());

        let failure = activate_candidates(vec![1, 2], |_| {
            Err(ViewError::Conversion("fault-injected quality read".into()))
        });
        assert!(matches!(failure, Err(ViewError::Conversion(_))));
    }
}
