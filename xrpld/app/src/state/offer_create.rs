//! Full OfferCreate transactor — reference the reference implementation parity.
//!
//! Handles:
//! - Offer cancellation (sfOfferSequence)
//! - Expiration check
//! - Tick size rounding
//! - DEX crossing via flow engine (flowCross)
//! - Residual offer placement with book directory
//! - FillOrKill / ImmediateOrCancel
//! - Reserve check before placement
//! - Sell flag (accept more than specified)
//! - Owner count adjustment

use basics::math::base_uint::Uint160;
use protocol::{
    AccountID, Amounts, Asset, Quality, STAmount, STLedgerEntry, STTx, Ter, get_field_by_symbol,
    is_tes_success,
};
use std::sync::Arc;

fn sf(name: &str) -> &'static protocol::SField {
    get_field_by_symbol(name)
}

/// Runs the canonical immutable OfferCreate preclaim implementation.
///
/// Authority: `rippled/src/libxrpl/tx/transactors/dex/OfferCreate.cpp`,
/// `OfferCreate::preclaim` (global freeze, accountFunds, acceptance, and
/// canTrade) is invoked by `src/libxrpl/tx/applySteps.cpp::invokePreclaim`
/// before `Transactor::apply` consumes the sequence or fee.  The shared Rust
/// DEX ReadView helper mirrors that phase and is used both by the normal
/// application shell and by direct dispatcher callers.
pub(crate) fn preclaim_offer_create<V: ledger::ReadView>(
    view: &V,
    sttx: &STTx,
    flags: protocol::ApplyFlags,
) -> Ter {
    tx::run_dex_read_view_preclaim_with_flags(view, sttx, protocol::TxType::OFFER_CREATE, flags)
        // This helper owns OfferCreate, so None would be a local dispatch
        // violation rather than a transaction result.
        .unwrap_or(Ter::TEF_INTERNAL)
}

/// Mirrors preclaim for direct state-dispatch callers, which intentionally do
/// not run the common account sequence-consumption preamble. Sequence-based
/// transactions use their sequence as a non-lowering logical floor; ticket
/// transactions must use the AccountRoot sequence exactly, as rippled does.
fn preclaim_offer_create_for_direct_dispatch<V: ledger::ReadView>(
    view: &V,
    sttx: &STTx,
    flags: protocol::ApplyFlags,
) -> Ter {
    tx::run_offer_create_direct_dispatch_preclaim(view, sttx, flags)
}

const TF_PASSIVE: u32 = 0x0001_0000;
const TF_IMMEDIATE_OR_CANCEL: u32 = 0x0002_0000;
const TF_FILL_OR_KILL: u32 = 0x0004_0000;
const TF_SELL: u32 = 0x0008_0000;

/// Full reference OfferCreate::doApply parity.
pub fn do_offer_create<V: ledger::ApplyView>(
    view: &mut V,
    sttx: &STTx,
    pre_fee_balance_drops: Option<i64>,
) -> Ter {
    let account = sttx.get_account_id(sf("sfAccount"));
    let tx_flags = sttx.get_field_u32(sf("sfFlags"));
    let mut taker_pays = sttx.get_field_amount(sf("sfTakerPays"));
    let mut taker_gets = sttx.get_field_amount(sf("sfTakerGets"));

    // (XRP-for-XRP or same IOU issuer+currency)
    if taker_pays.native() && taker_gets.native() {
        return Ter::TEM_BAD_OFFER;
    }
    if !taker_pays.native() && !taker_gets.native() && taker_pays.asset() == taker_gets.asset() {
        return Ter::TEM_BAD_OFFER;
    }

    if taker_pays.signum() <= 0 || taker_gets.signum() <= 0 {
        return Ter::TEM_BAD_OFFER;
    }

    let is_passive = (tx_flags & TF_PASSIVE) != 0;
    let is_ioc = (tx_flags & TF_IMMEDIATE_OR_CANCEL) != 0;
    let is_fok = (tx_flags & TF_FILL_OR_KILL) != 0;
    let is_sell = (tx_flags & TF_SELL) != 0;
    let is_hybrid = (tx_flags & protocol::tfHybrid) != 0;
    let domain_id = sttx
        .is_field_present(sf("sfDomainID"))
        .then(|| sttx.get_field_h256(sf("sfDomainID")));

    if is_hybrid && domain_id.is_none() {
        return Ter::TEM_INVALID_FLAG;
    }
    if domain_id.is_some()
        && !view
            .rules()
            .enabled(&protocol::feature_id("PermissionedDEX"))
    {
        return Ter::TEM_DISABLED;
    }

    // Normal application uses the same helper in the pre-fee apply shell.
    // Direct state-dispatch callers have no preceding applySteps lifecycle,
    // so run the exact ReadView preclaim here.  Do not run it again after the
    // fee preamble: rippled's preclaim sees the pre-fee XRP balance, while
    // flowCross performs its separate post-fee funding check.
    if pre_fee_balance_drops.is_none() {
        let preclaim =
            preclaim_offer_create_for_direct_dispatch(view, sttx, protocol::ApplyFlags::NONE);
        if preclaim != Ter::TES_SUCCESS {
            return preclaim;
        }
    }

    // Get offer sequence (for the new offer's key)
    let offer_sequence = sttx.get_seq_value();

    let mut result = Ter::TES_SUCCESS;

    // --- Cancel existing offer if OfferSequence present ---
    if sttx.is_field_present(sf("sfOfferSequence")) {
        let cancel_seq = sttx.get_field_u32(sf("sfOfferSequence"));
        let trace_offer_sequence = std::env::var("XRPL_TRACE_OFFER_SEQUENCE")
            .map(|value| value == "1")
            .unwrap_or(false);
        if trace_offer_sequence {
            eprintln!(
                "TRACE offer_sequence: account={:?} tx_seq={} cancel_seq={}",
                account, offer_sequence, cancel_seq
            );
        }
        let cancel_keylet = protocol::offer_keylet(Uint160::from_void(account.data()), cancel_seq);
        // ApplyView::peek is the canonical overlay-aware lookup and already
        // resolves the parent view. A second `read` after Ok(None) bypasses the
        // transaction overlay and can revive an entry erased earlier in the
        // same sandbox; pinned psbCancel performs one `peek` only.
        let old_offer = match view.peek(cancel_keylet) {
            Ok(Some(offer)) => Some(offer),
            Ok(None) => None,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        if let Some(old_offer) = old_offer {
            if trace_offer_sequence {
                eprintln!(
                    "TRACE offer_sequence: found offer_key={} owner_node={} book_node={} book_dir={}",
                    old_offer.key(),
                    old_offer.get_field_u64(sf("sfOwnerNode")),
                    old_offer.get_field_u64(sf("sfBookNode")),
                    old_offer.get_field_h256(sf("sfBookDirectory"))
                );
            }
            result = offer_delete(view, &account, old_offer);
            if trace_offer_sequence {
                eprintln!("TRACE offer_sequence: offer_delete_result={:?}", result);
            }
        } else if trace_offer_sequence {
            eprintln!("TRACE offer_sequence: cancelled offer absent");
        }
    }

    // --- Expiration check ---
    if sttx.is_field_present(sf("sfExpiration")) {
        let expiration = sttx.get_field_u32(sf("sfExpiration"));
        let close_time = view.header().close_time;
        if close_time >= expiration {
            return Ter::TEC_EXPIRED;
        }
    }

    if !is_tes_success(result) {
        return result;
    }

    // --- Tick size rounding ---
    // reference: round offer to tick size of the issuer accounts
    let tick_size = match get_tick_size(view, &taker_pays, &taker_gets) {
        Ok(tick_size) => tick_size,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    if tick_size < 16 {
        // reference: auto const rate = Quality{saTakerGets, saTakerPays}.round(uTickSize).rate();
        // Quality is stored as (exponent << 56) | mantissa = getRate(taker_gets, taker_pays)
        let quality = match get_rate(&taker_gets, &taker_pays) {
            Ok(quality) => quality,
            Err(ter) => return ter,
        };
        let rounded_quality = round_quality(quality, tick_size);
        // Convert rounded quality back to a rate STAmount for multiply/divide
        let rate_amount = quality_to_rate_amount(rounded_quality);

        if is_sell && !matches!(taker_pays.asset(), Asset::MPTIssue(_)) {
            // reference: saTakerPays = multiply(saTakerGets, rate, saTakerPays.asset())
            taker_pays = match amount_or_exception(
                taker_gets.try_multiply(&rate_amount, taker_pays.asset()),
            ) {
                Ok(amount) => amount,
                Err(ter) => return ter,
            };
        } else if !is_sell && !matches!(taker_gets.asset(), Asset::MPTIssue(_)) {
            // rippled invokes divide here; its zero-rate exception is mapped by
            // doApply to tefEXCEPTION. Preserve that result without emitting a
            // Rust unwind from the consensus strand.
            if rate_amount.signum() == 0 {
                return Ter::TEF_EXCEPTION;
            }
            // reference: saTakerGets = divide(saTakerPays, rate, saTakerGets.asset())
            taker_gets = match amount_or_exception(
                taker_pays.try_divide(&rate_amount, taker_gets.asset()),
            ) {
                Ok(amount) => amount,
                Err(ter) => return ter,
            };
        }
        if taker_pays.signum() <= 0 || taker_gets.signum() <= 0 {
            return Ter::TES_SUCCESS; // Rounded to zero
        }
    }

    // It does NOT prevent crossing. FOK+Passive and IOC+Passive proceed to crossing
    // and apply FOK/IOC rules after. Only kill early if passive AND no crossing is
    // possible at all (i.e., the offer would not cross any existing offers).
    // We do NOT early-kill here — let the crossing loop run and apply FOK/IOC after.

    // --- DEX crossing via flow engine (reference flowCross calls flow()) ---
    // For passive offers, reference increments threshold so only strictly better offers are crossed.
    // reference: Quality threshold{takerAmount.out, sendMax} in
    // OfferCreate::flowCross (OfferCreate.cpp), where takerAmount.in =
    // TakerGets, takerAmount.out = TakerPays, and sendMax defaults to
    // takerAmount.in (TakerGets, absent a gateway transfer rate). That
    // reduces to getRate(TakerPays, TakerGets) = TakerGets / TakerPays --
    // the SAME quality formula book_step.rs uses for each candidate offer
    // (`Quality::from_amounts(&Amounts::new(offer_taker_gets,
    // offer_taker_pays))`). Amounts::new takes (in, out) positionally, so
    // this must be (taker_gets, taker_pays) here too, not (taker_pays,
    // taker_gets) -- the previous ordering computed the reciprocal
    // (TakerPays / TakerGets), comparing against candidate offer qualities
    // on the wrong scale and letting through offers that should have been
    // rejected as worse than this offer's own quality.
    // OfferCreate::flowCross includes the input issuer's transfer rate in
    // sendMax *before* deriving the crossing threshold.  This is consensus
    // significant for AMM liquidity: using the unadjusted TakerGets admits
    // pools whose effective quality (including the gateway fee) is worse than
    // the offer's limit.
    // rippled checks funding before transfer-rate lookup or path construction.
    // This is the only crossing failure which flowCross propagates directly;
    // failures returned by flow itself leave the offer unchanged and are
    // placed.
    let (in_start_balance, disallow_unfunded) =
        match crossing_account_funds(view, &account, &taker_gets) {
            Ok(value) => value,
            Err(ter) => return ter,
        };
    if disallow_unfunded && in_start_balance.signum() <= 0 {
        return Ter::TEC_UNFUNDED_OFFER;
    }

    let gateway_rate = match taker_gets.asset() {
        protocol::Asset::Issue(issue) if !issue.native() && account != issue.issuer() => {
            match ledger::ripple_state_helpers::try_transfer_rate(view, &issue.issuer()) {
                Ok(rate) => rate,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            }
        }
        _ => 1_000_000_000u32,
    };
    let send_max = gateway_adjusted_send_max(&taker_gets, gateway_rate);
    let mut quality_threshold =
        Quality::from_amounts(&Amounts::new(send_max.clone(), taker_pays.clone()));
    if is_passive {
        // offers do not cross. Quality::increment preserves stored XRPL
        // quality ordering instead of approximating with floating point.
        quality_threshold.increment();
    }
    let effective_send_max = if send_max > in_start_balance {
        in_start_balance
    } else {
        send_max.clone()
    };

    let mut crossed = false;
    let (remaining_gets, remaining_pays) = {
        // Cross as a payment from the offer creator back to themselves.
        // rippled's takerAmount.in is TakerGets (what the creator supplies)
        // and takerAmount.out is TakerPays (what the creator receives).
        let deliver_asset = taker_pays.asset();
        let send_max_asset = taker_gets.asset();

        let mut cross_paths = protocol::STPathSet::new(sf("sfPaths"));
        if !taker_gets.native() && !taker_pays.native() {
            let mut xrp_path = protocol::STPath::new();
            // rippled: path.emplaceBack(std::nullopt, xrpCurrency(),
            //                          std::nullopt)
            // XRP is explicitly present as the path asset.  `inferred(...,
            // force_asset=false)` instead encodes TypeNone for XRP, which is
            // not the synthetic bridge constructed by OfferCreate::flowCross.
            xrp_path.push_back(protocol::STPathElement::raw(
                protocol::STPathElement::TYPE_CURRENCY,
                protocol::AccountID::zero(),
                protocol::xrp_currency(),
                protocol::AccountID::zero(),
            ));
            cross_paths.push_back(xrp_path);
        }

        // Build typed Issue/MPT strands for crossing (rippled toStrands with
        // offerCrossing=true).  Keeping the exact Asset here is consensus
        // critical: treating an MPT as XRP selects a different book key.
        let (strands_ter, strands) =
            ledger::flow_engine::strand_builder::to_strands_checked_with_domain(
                view,
                &account,
                &account, // src == dst for offer crossing
                &deliver_asset,
                Some(&send_max_asset),
                &cross_paths,
                true, // default paths allowed
                true, // owner pays transfer fee
                true, // offer crossing
                domain_id,
            );
        // OfferCreate::flowCross intentionally treats a failed flow as a dry
        // crossing: the original offer is still valid and is placed unchanged.
        // This includes failures while constructing strands (for example
        // terNO_RIPPLE and temBAD_PATH_LOOP). Propagating this internal TER
        // omits a canonical OfferCreate from the ledger.
        if !is_tes_success(strands_ter) {
            (taker_gets.clone(), taker_pays.clone())
        } else {
            let self_cross_cancellations = ledger::flow_engine::SelfCrossCancellation::default();
            let cross_deliver = if is_sell {
                sell_cross_deliver_limit(&taker_pays)
            } else {
                taker_pays.clone()
            };

            // Execute strands
            // reference: flow(deliver=takerAmount.out, sendMax=takerAmount.in)
            let flow_result = ledger::flow_engine::strand_flow::execute_strands(
                view,
                &strands,
                &cross_deliver,
                (tx_flags & TF_FILL_OR_KILL) == 0,
                if is_sell {
                    ledger::ripple_calc::OfferCrossing::Sell
                } else {
                    ledger::ripple_calc::OfferCrossing::Yes
                },
                Some(&effective_send_max),
                &account,
                &account,
                Some(quality_threshold),
                Some(self_cross_cancellations.clone()),
            );

            let cancellation_result = self_cross_cancellations.apply_to(view);
            if cancellation_result != Ter::TES_SUCCESS {
                return cancellation_result;
            }

            if !is_tes_success(flow_result.ter) {
                (taker_gets.clone(), taker_pays.clone())
            } else {
                let actual_in = flow_result.actual_in;
                let actual_out = flow_result.actual_out;

                if actual_in.signum() > 0 || actual_out.signum() > 0 {
                    crossed = true;
                }

                // Compute the residual offer using rippled's flow result convention:
                // actual_in is TakerGets consumed and actual_out is TakerPays delivered.
                // A dry flow leaves the offer unchanged. Besides matching rippled's
                // post-cross result, this avoids converting an otherwise unused
                // encoded rate back into an amount.
                let (post_cross_balance, _) =
                    match crossing_account_funds(view, &account, &taker_gets) {
                        Ok(value) => value,
                        Err(ter) => return ter,
                    };
                let (rem_gets, rem_pays) = if disallow_unfunded && post_cross_balance.signum() <= 0
                {
                    (taker_gets.zeroed(), taker_pays.zeroed())
                } else if actual_in.signum() <= 0 && actual_out.signum() <= 0 {
                    (taker_gets.clone(), taker_pays.clone())
                } else if is_sell {
                    // tfSell reduces the input side, TakerGets.
                    let non_gateway_in = if gateway_rate != 1_000_000_000 {
                        let rate = STAmount::new_with_asset(
                            sf("sfAmount"),
                            protocol::no_issue(),
                            gateway_rate as u64,
                            -9,
                            false,
                        );
                        match amount_or_exception(actual_in.try_divide(&rate, taker_gets.asset())) {
                            Ok(amount) => amount,
                            Err(ter) => return ter,
                        }
                    } else {
                        actual_in
                    };
                    let mut rem_gets = taker_gets.clone() - non_gateway_in;
                    if rem_gets.signum() < 0 {
                        rem_gets.clear();
                    }
                    let rem_pays = if rem_gets.signum() <= 0 {
                        taker_pays.zeroed()
                    } else {
                        // C++: divRoundStrict(afterCross.in,
                        // Quality{takerAmount.out, takerAmount.in}.rate(), out, false)
                        let rate = Quality::from_amounts(&Amounts::new(
                            taker_gets.clone(),
                            taker_pays.clone(),
                        ))
                        .rate();
                        protocol::div_round_strict(&rem_gets, &rate, taker_pays.asset(), false)
                    };
                    (rem_gets, rem_pays)
                } else {
                    // Non-sell reduces the output side, TakerPays, then recomputes
                    // TakerGets at the original offer quality.
                    let mut rem_pays = taker_pays.clone() - actual_out;
                    if rem_pays.signum() < 0 {
                        rem_pays.clear();
                    }
                    let rem_gets = if rem_pays.signum() <= 0 {
                        taker_gets.zeroed()
                    } else {
                        // C++: mulRound(afterCross.out,
                        // Quality{takerAmount.out, takerAmount.in}.rate(), in, true)
                        let rate = Quality::from_amounts(&Amounts::new(
                            taker_gets.clone(),
                            taker_pays.clone(),
                        ))
                        .rate();
                        rem_pays.mul_round(&rate, taker_gets.asset(), true)
                    };
                    (rem_gets, rem_pays)
                };
                (rem_gets, rem_pays)
            }
        }
    };

    // --- Fully crossed check ---
    if remaining_gets.signum() <= 0 || remaining_pays.signum() <= 0 {
        return Ter::TES_SUCCESS; // Fully crossed
    }

    // --- FillOrKill check ---
    if is_fok {
        return Ter::TEC_KILLED;
    }

    // --- ImmediateOrCancel check ---
    if is_ioc {
        if !crossed {
            return Ter::TEC_KILLED;
        }
        return Ter::TES_SUCCESS;
    }

    // --- Reserve check before placing ---
    let acct_keylet = protocol::account_keylet(Uint160::from_void(account.data()));
    let acct_sle = match view.peek(acct_keylet) {
        Ok(Some(sle)) => sle,
        Ok(None) => return Ter::TEF_INTERNAL,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    let reserve = ledger::effective_account_reserve(view.fees(), &acct_sle, 1, 0);
    let balance = pre_fee_balance_drops
        .unwrap_or_else(|| acct_sle.get_field_amount(sf("sfBalance")).xrp().drops());
    if balance < reserve as i64 {
        if !crossed {
            return Ter::TEC_INSUF_RESERVE_OFFER;
        }
        // If crossed, allow it (reference behavior)
        return Ter::TES_SUCCESS;
    }

    // --- Place the remaining offer ---
    let offer_keylet = protocol::offer_keylet(Uint160::from_void(account.data()), offer_sequence);

    // Add to owner directory. reference the reference source: owner directory uses dirInsert,
    // while the book directory below uses dirAppend.
    let owner_dir = protocol::owner_dir_keylet(Uint160::from_void(account.data()));
    let owner_node = match ledger::dir_insert(view, &owner_dir, offer_keylet.key, &|sle| {
        // describeOwnerDir(accountID_) in rippled.  The descriptor runs when
        // the directory root is first created and is part of the ledger hash.
        sle.set_account_id(sf("sfOwner"), account);
    }) {
        Ok(Some(page)) => page,
        other => {
            static DIR_FULL_LOG: std::sync::atomic::AtomicU32 =
                std::sync::atomic::AtomicU32::new(0);
            if DIR_FULL_LOG.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < 20 {
                tracing::debug!(target: "tx",
                    "[offer_debug] DIR_FULL owner_dir: dir_key={:02x}{:02x}{:02x}{:02x} result={:?} crossed={} remaining_gets_signum={} remaining_pays_signum={}",
                    owner_dir.key.data()[0],
                    owner_dir.key.data()[1],
                    owner_dir.key.data()[2],
                    owner_dir.key.data()[3],
                    other.as_ref().map(|_| "ok").unwrap_or("err"),
                    crossed,
                    remaining_gets.signum(),
                    remaining_pays.signum()
                );
            }
            return Ter::TEC_DIR_FULL;
        }
    };

    // Adjust owner count
    if ledger::adjust_owner_count(view, &acct_sle, 1).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }

    // Add to book directory
    let book = protocol::Book {
        r#in: taker_pays.asset(),
        out: taker_gets.asset(),
        domain: domain_id,
    };
    let book_base = protocol::book_keylet(book);
    let rate = match get_rate(&taker_gets, &taker_pays) {
        Ok(rate) => rate,
        Err(ter) => return ter,
    };
    let quality_dir = protocol::quality_keylet(book_base, rate);

    let book_node = match ledger::dir_append(view, &quality_dir, offer_keylet.key, &|sle| {
        set_book_directory_fields(sle, &taker_pays, &taker_gets, rate, domain_id);
    }) {
        Ok(Some(page)) => page,
        other => {
            static BOOK_DIR_FULL_LOG: std::sync::atomic::AtomicU32 =
                std::sync::atomic::AtomicU32::new(0);
            if BOOK_DIR_FULL_LOG.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < 20 {
                tracing::debug!(target: "tx",
                    "[offer_debug] DIR_FULL book_dir: dir_key={:02x}{:02x}{:02x}{:02x} result={:?} crossed={} remaining_gets_signum={} remaining_pays_signum={}",
                    quality_dir.key.data()[0],
                    quality_dir.key.data()[1],
                    quality_dir.key.data()[2],
                    quality_dir.key.data()[3],
                    other.as_ref().map(|_| "ok").unwrap_or("err"),
                    crossed,
                    remaining_gets.signum(),
                    remaining_pays.signum()
                );
            }
            return Ter::TEC_DIR_FULL;
        }
    };

    // Create the offer SLE
    let mut offer_obj = protocol::STObject::new(sf("sfLedgerEntry"));
    offer_obj.set_field_u16(sf("sfLedgerEntryType"), 0x006F); // ltOFFER
    offer_obj.set_account_id(sf("sfAccount"), account);
    offer_obj.set_field_u32(sf("sfSequence"), offer_sequence);
    offer_obj.set_field_h256(sf("sfBookDirectory"), quality_dir.key);
    offer_obj.set_field_amount(sf("sfTakerPays"), remaining_pays);
    offer_obj.set_field_amount(sf("sfTakerGets"), remaining_gets);
    offer_obj.set_field_u64(sf("sfOwnerNode"), owner_node);
    offer_obj.set_field_u64(sf("sfBookNode"), book_node);
    if let Some(domain_id) = domain_id {
        offer_obj.set_field_h256(sf("sfDomainID"), domain_id);
    }

    if sttx.is_field_present(sf("sfExpiration")) {
        offer_obj.set_field_u32(sf("sfExpiration"), sttx.get_field_u32(sf("sfExpiration")));
    }

    let mut offer_flags = 0u32;
    if is_passive {
        offer_flags |= 0x0001_0000; // lsfPassive
    }
    if is_sell {
        offer_flags |= 0x0002_0000; // lsfSell
    }
    if is_hybrid {
        offer_flags |= protocol::lsfHybrid;
    }
    offer_obj.set_field_u32(sf("sfFlags"), offer_flags);

    if is_hybrid {
        let open_rate = if view
            .rules()
            .enabled(&protocol::feature_id(protocol::FIX_CLEANUP_3_2_0_NAME))
        {
            rate
        } else {
            match get_rate(
                &offer_obj.get_field_amount(sf("sfTakerGets")),
                &offer_obj.get_field_amount(sf("sfTakerPays")),
            ) {
                Ok(rate) => rate,
                Err(ter) => return ter,
            }
        };
        let open_book = protocol::Book {
            r#in: taker_pays.asset(),
            out: taker_gets.asset(),
            domain: None,
        };
        let open_quality_dir =
            protocol::quality_keylet(protocol::book_keylet(open_book), open_rate);
        let open_book_node =
            match ledger::dir_append(view, &open_quality_dir, offer_keylet.key, &|sle| {
                // The legacy open-book key may use post-crossing quality, but
                // Record the original placement rate in metadata.
                set_book_directory_fields(sle, &taker_pays, &taker_gets, rate, None);
            }) {
                Ok(Some(page)) => page,
                _ => return Ter::TEC_DIR_FULL,
            };

        let mut additional_books = protocol::STArray::new(sf("sfAdditionalBooks"));
        let mut book_info = protocol::STObject::make_inner_object(sf("sfBook"));
        book_info.set_field_h256(sf("sfBookDirectory"), open_quality_dir.key);
        book_info.set_field_u64(sf("sfBookNode"), open_book_node);
        additional_books.push_back(book_info);
        offer_obj.set_field_array(sf("sfAdditionalBooks"), additional_books);
    }

    let offer_sle = STLedgerEntry::from_stobject(offer_obj, offer_keylet.key);
    if view.insert(Arc::new(offer_sle)).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }

    Ter::TES_SUCCESS
}

fn set_book_directory_fields(
    sle: &mut protocol::STObject,
    taker_pays: &STAmount,
    taker_gets: &STAmount,
    rate: u64,
    domain_id: Option<protocol::Domain>,
) {
    match taker_pays.asset() {
        protocol::Asset::Issue(issue) if !issue.native() => {
            sle.set_field_h160(
                sf("sfTakerPaysCurrency"),
                Uint160::from_void(issue.currency.data()),
            );
            sle.set_field_h160(
                sf("sfTakerPaysIssuer"),
                Uint160::from_void(issue.account.data()),
            );
        }
        protocol::Asset::Issue(_) => {
            // rippled stores explicit all-zero currency and issuer fields for
            // the XRP side of a BookDirectory. Leaving them absent changes
            // the serialized directory SLE even though JSON displays the
            // same conceptual book.
            sle.set_field_h160(sf("sfTakerPaysCurrency"), Uint160::zero());
            sle.set_field_h160(sf("sfTakerPaysIssuer"), Uint160::zero());
        }
        protocol::Asset::MPTIssue(issue) => {
            sle.set_field_h192(sf("sfTakerPaysMPT"), issue.mpt_id());
        }
    }
    match taker_gets.asset() {
        protocol::Asset::Issue(issue) if !issue.native() => {
            sle.set_field_h160(
                sf("sfTakerGetsCurrency"),
                Uint160::from_void(issue.currency.data()),
            );
            sle.set_field_h160(
                sf("sfTakerGetsIssuer"),
                Uint160::from_void(issue.account.data()),
            );
        }
        protocol::Asset::Issue(_) => {
            sle.set_field_h160(sf("sfTakerGetsCurrency"), Uint160::zero());
            sle.set_field_h160(sf("sfTakerGetsIssuer"), Uint160::zero());
        }
        protocol::Asset::MPTIssue(issue) => {
            sle.set_field_h192(sf("sfTakerGetsMPT"), issue.mpt_id());
        }
    }
    sle.set_field_u64(sf("sfExchangeRate"), rate);
    if let Some(domain_id) = domain_id {
        sle.set_field_h256(sf("sfDomainID"), domain_id);
    }
}

/// Delete an offer — remove from owner dir, book dir, and erase SLE.
pub fn offer_delete_pub<V: ledger::ApplyView>(
    view: &mut V,
    account: &AccountID,
    offer_sle: Arc<STLedgerEntry>,
) -> Ter {
    offer_delete(view, account, offer_sle)
}

fn offer_delete<V: ledger::ApplyView>(
    view: &mut V,
    account: &AccountID,
    offer_sle: Arc<STLedgerEntry>,
) -> Ter {
    let _ = account;
    ledger::offer_helpers::offer_delete(view, offer_sle).unwrap_or(Ter::TEF_BAD_LEDGER)
}

fn amount_or_exception(
    result: Result<STAmount, protocol::st_amount::AmountError>,
) -> Result<STAmount, Ter> {
    result.map_err(|error| {
        tracing::debug!(target: "tx", %error, "OfferCreate amount calculation rejected");
        Ter::TEF_EXCEPTION
    })
}

/// Returns the exchange rate encoded as u64: top 8 bits = exponent+100, lower 56 bits = mantissa.
/// reference: getRate(offerOut=taker_gets, offerIn=taker_pays) = divide(taker_pays, taker_gets) encoded.
fn get_rate(taker_gets: &STAmount, taker_pays: &STAmount) -> Result<u64, Ter> {
    if taker_gets.signum() <= 0 {
        return Ok(0);
    }
    // STAmount r = divide(offerIn, offerOut, noIssue())
    let no_issue = protocol::no_issue();
    let r = taker_pays
        .try_divide(taker_gets, no_issue)
        .map_err(|_| Ter::TEF_EXCEPTION)?;
    if r.signum() <= 0 {
        return Ok(0);
    }
    // reference: (r.exponent() + 100) << 56 | r.mantissa()
    let exp = r.exponent() + 100;
    if !(0..=255).contains(&exp) {
        return Ok(0);
    }
    Ok(((exp as u64) << 56) | r.mantissa())
}

/// Get tick size from issuer accounts.
fn get_tick_size<V: ledger::ApplyView>(
    view: &V,
    taker_pays: &STAmount,
    taker_gets: &STAmount,
) -> Result<u8, ledger::ViewError> {
    let mut tick_size: u8 = 16; // Quality::kMaxTickSize

    // Check pays issuer
    if let protocol::Asset::Issue(issue) = taker_pays.asset()
        && !issue.native()
    {
        let issuer = issue.account;
        let issuer_keylet = protocol::account_keylet(Uint160::from_void(issuer.data()));
        if let Some(sle) = view.read(issuer_keylet)? {
            if sle.is_field_present(sf("sfTickSize")) {
                let ts = sle.get_field_u8(sf("sfTickSize"));
                if ts < tick_size {
                    tick_size = ts;
                }
            }
        }
    }

    // Check gets issuer
    if let protocol::Asset::Issue(issue) = taker_gets.asset()
        && !issue.native()
    {
        let issuer = issue.account;
        let issuer_keylet = protocol::account_keylet(Uint160::from_void(issuer.data()));
        if let Some(sle) = view.read(issuer_keylet)? {
            if sle.is_field_present(sf("sfTickSize")) {
                let ts = sle.get_field_u8(sf("sfTickSize"));
                if ts < tick_size {
                    tick_size = ts;
                }
            }
        }
    }

    Ok(tick_size)
}

/// Quality is encoded as (exponent << 56) | mantissa.
/// Rounding is UP (adds kMOD[digits]-1 before truncating).
fn round_quality(quality: u64, digits: u8) -> u64 {
    if quality == 0 || digits >= 16 {
        return quality;
    }
    static K_MOD: [u64; 17] = [
        10000000000000000, // 0
        1000000000000000,  // 1
        100000000000000,   // 2
        10000000000000,    // 3
        1000000000000,     // 4
        100000000000,      // 5
        10000000000,       // 6
        1000000000,        // 7
        100000000,         // 8
        10000000,          // 9
        1000000,           // 10
        100000,            // 11
        10000,             // 12
        1000,              // 13
        100,               // 14
        10,                // 15
        1,                 // 16
    ];
    let exponent = quality >> 56;
    let mut mantissa = quality & 0x00ffffffffffffff;
    let modulus = K_MOD[digits as usize];
    mantissa += modulus - 1;
    mantissa -= mantissa % modulus;
    (exponent << 56) | mantissa
}

/// Convert a quality (encoded u64) back to an STAmount rate for multiply/divide.
///
/// `Quality::rate()` is an arithmetic rate, not an XRP amount. It must use
/// `no_issue()`'s non-native sentinel: `Issue::default()` is XRP and therefore
/// canonicalizes fractional IOU/IOU rates as integral drops. This delegates to
/// the shared Rust analogue of rippled `Quality::rate()` / `amountFromQuality`:
/// `OfferCreate.cpp:685,694,699` applies it directly to divide or multiply.
fn quality_to_rate_amount(quality: u64) -> STAmount {
    protocol::amount_from_quality(quality)
}

/// Expand the offer input limit by the issuer transfer fee exactly as
/// `OfferCreate::flowCross` does before constructing its quality threshold.
fn gateway_adjusted_send_max(taker_gets: &STAmount, gateway_rate: u32) -> STAmount {
    if gateway_rate == 1_000_000_000 || taker_gets.native() {
        return taker_gets.clone();
    }

    let rate = STAmount::new_with_asset(
        sf("sfAmount"),
        protocol::no_issue(),
        gateway_rate as u64,
        -9,
        false,
    );
    taker_gets.mul_round(&rate, taker_gets.asset(), true)
}

/// `tfSell` lets flow deliver as much output as the input can buy.  rippled
/// uses deliberately bounded maxima so transfer-rate multiplication remains
/// representable.
fn sell_cross_deliver_limit(taker_pays: &STAmount) -> STAmount {
    match taker_pays.asset() {
        // rippled intentionally uses its internal native maximum here, not
        // the lower network-legal maximum.  Since this exceeds all possible
        // XRP liquidity, reverse Flow must discover a limiting step and the
        // forward pass can never commit this probe-only sentinel.
        protocol::Asset::Issue(issue) if issue.native() => {
            STAmount::new_native(protocol::ST_AMOUNT_MAX_NATIVE, false)
        }
        protocol::Asset::Issue(issue) => STAmount::new_with_asset(
            sf("sfAmount"),
            issue,
            protocol::ST_AMOUNT_MAX_MANTISSA / 2,
            protocol::ST_AMOUNT_MAX_OFFSET,
            false,
        ),
        protocol::Asset::MPTIssue(issue) => STAmount::from_mpt_amount(
            sf("sfAmount"),
            protocol::MPTAmount::from_value(protocol::MAX_MP_TOKEN_AMOUNT / 2),
            issue,
        ),
    }
}

/// Post-fee funding lookup used by OfferCreate::flowCross.  The boolean is
/// false only for an MPT issuer, which rippled permits to trade without a
/// pre-existing holder balance.
fn crossing_account_funds<V: ledger::ApplyView>(
    view: &mut V,
    account: &AccountID,
    amount: &STAmount,
) -> Result<(STAmount, bool), Ter> {
    match amount.asset() {
        protocol::Asset::Issue(issue) if issue.native() => {
            let liquid = ledger::apply_view::xrp_liquid(view, account, 0)
                .map_err(|_| Ter::TEF_BAD_LEDGER)?;
            Ok((STAmount::from_xrp_amount(liquid), true))
        }
        protocol::Asset::Issue(issue) if issue.issuer() == *account => Ok((amount.clone(), true)),
        protocol::Asset::Issue(issue) => {
            let issuer_key = protocol::account_keylet(Uint160::from_void(issue.issuer().data()));
            let issuer = view.read(issuer_key).map_err(|_| Ter::TEF_BAD_LEDGER)?;
            let line_key = protocol::line(*account, issue.issuer(), issue.currency);
            let line = view.read(line_key).map_err(|_| Ter::TEF_BAD_LEDGER)?;

            let globally_frozen = issuer
                .as_ref()
                .is_some_and(|sle| sle.is_flag(protocol::lsfGlobalFreeze));
            // A holder's own freeze bit does not freeze its funds. Only the
            // issuer-side bit does (RippleStateHelpers::isFrozen parity).
            let issuer_frozen = line.as_ref().is_some_and(|line| {
                line.is_flag(if issue.issuer() > *account {
                    protocol::lsfHighFreeze
                } else {
                    protocol::lsfLowFreeze
                })
            });
            let deep_frozen = line.as_ref().is_some_and(|line| {
                line.is_flag(protocol::lsfLowDeepFreeze)
                    || line.is_flag(protocol::lsfHighDeepFreeze)
            });
            if globally_frozen || issuer_frozen || deep_frozen {
                return Ok((amount.zeroed(), true));
            }
            Ok((
                ledger::ripple_state_helpers::try_account_holds(
                    view,
                    account,
                    &issue.issuer(),
                    issue.currency,
                )
                .map_err(|_| Ter::TEF_BAD_LEDGER)?,
                true,
            ))
        }
        protocol::Asset::MPTIssue(issue) => {
            let issuance_key = protocol::mpt_issuance_keylet_from_mptid(issue.mpt_id());
            let Some(issuance) = view.read(issuance_key).map_err(|_| Ter::TEF_BAD_LEDGER)? else {
                return Ok((amount.zeroed(), true));
            };
            let issuer = issuance.get_account_id(sf("sfIssuer"));
            if issuer == *account {
                let available = ledger::mptoken_helpers::available_mpt_amount(&issuance);
                return Ok((
                    STAmount::from_mpt_amount(
                        sf("sfAmount"),
                        protocol::MPTAmount::from_value(available),
                        issue,
                    ),
                    false,
                ));
            }
            if ledger::mptoken_helpers::is_frozen_mpt(view, account, &issue)
                .map_err(|_| Ter::TEF_BAD_LEDGER)?
                || ledger::mptoken_helpers::require_auth_mpt_with_type(
                    view,
                    &issue,
                    account,
                    ledger::mptoken_helpers::MPTAuthType::Strong,
                )
                .map_err(|_| Ter::TEF_BAD_LEDGER)?
                    != Ter::TES_SUCCESS
            {
                return Ok((amount.zeroed(), true));
            }
            let token_key = protocol::mptoken_keylet_from_mptid(
                issue.mpt_id(),
                Uint160::from_void(account.data()),
            );
            let Some(token) = view.read(token_key).map_err(|_| Ter::TEF_BAD_LEDGER)? else {
                return Ok((amount.zeroed(), true));
            };
            Ok((
                STAmount::from_mpt_amount(
                    sf("sfAmount"),
                    protocol::MPTAmount::from_value(token.get_field_u64(sf("sfMPTAmount")) as i64),
                    issue,
                ),
                true,
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol::{StBase, XRPAmount};

    #[test]
    fn offer_create_amount_error_maps_to_tef_exception_without_unwinding() {
        assert_eq!(
            amount_or_exception(Err(protocol::st_amount::AmountError::NativeOutOfRange)),
            Err(Ter::TEF_EXCEPTION)
        );
    }

    #[test]
    fn quality_to_rate_amount_underflow_is_zero() {
        let zero_rate = quality_to_rate_amount(0);
        assert_eq!(zero_rate.signum(), 0);
        // Encoded quality exponent 0 decodes to STAmount exponent -100,
        // below the representable IOU range and therefore canonicalizes to zero.
        let rate = quality_to_rate_amount(1_000_000_000_000_000);
        assert_eq!(rate.signum(), 0);
    }

    #[test]
    fn gateway_transfer_rate_is_included_in_offer_cross_send_max_and_threshold() {
        // Ledger 20,109,795 transaction A0DA77... uses a 1.005 transfer-rate
        // UAH issuer.  The fee-adjusted threshold rejects the AMM that the
        // unadjusted threshold incorrectly crossed.
        let issue = protocol::Issue::new(
            protocol::currency_from_string("UAH"),
            protocol::AccountID::from_array([0x44; 20]),
        );
        let taker_gets = STAmount::from_iou_amount(
            sf("sfTakerGets"),
            protocol::IOUAmount::from_parts(5_000_000_000_000_000, -13)
                .expect("500 UAH is canonical"),
            issue,
        );
        let taker_pays = STAmount::from_xrp_amount(XRPAmount::from_drops(7_721_222));

        let send_max = gateway_adjusted_send_max(&taker_gets, 1_005_000_000);
        assert_eq!(send_max.text(), "502.5");

        let adjusted = Quality::from_amounts(&Amounts::new(send_max, taker_pays.clone()));
        let unadjusted = Quality::from_amounts(&Amounts::new(taker_gets, taker_pays));
        assert_ne!(adjusted, unadjusted);
    }

    #[test]
    fn sell_crossing_uses_asset_specific_bounded_maximum_delivery() {
        let xrp = STAmount::from_xrp_amount(XRPAmount::from_drops(1));
        assert_eq!(
            sell_cross_deliver_limit(&xrp).xrp().drops(),
            protocol::ST_AMOUNT_MAX_NATIVE as i64
        );
        assert!(!sell_cross_deliver_limit(&xrp).is_legal_net());

        let issue = protocol::Issue::new(
            protocol::currency_from_string("USD"),
            protocol::AccountID::from_array([0x66; 20]),
        );
        let iou = STAmount::new_with_asset(sf("sfAmount"), issue, 1, 0, false);
        let iou_limit = sell_cross_deliver_limit(&iou);
        assert_eq!(iou_limit.mantissa(), protocol::ST_AMOUNT_MAX_MANTISSA / 2);
        assert_eq!(iou_limit.exponent(), protocol::ST_AMOUNT_MAX_OFFSET);

        let mpt_issue = protocol::MPTIssue::new(protocol::MPTID::from_array([0x77; 24]));
        let mpt = STAmount::from_mpt_amount(
            sf("sfAmount"),
            protocol::MPTAmount::from_value(1),
            mpt_issue,
        );
        assert_eq!(
            sell_cross_deliver_limit(&mpt).mpt().value(),
            protocol::MAX_MP_TOKEN_AMOUNT / 2
        );
    }

    #[test]
    fn residual_rounding_matches_flow_cross_operations() {
        let issue = protocol::Issue::new(
            protocol::currency_from_string("USD"),
            protocol::AccountID::from_array([0x88; 20]),
        );
        let original_in =
            STAmount::new_with_asset(sf("sfAmount"), issue, 5_000_000_000_000_000, -13, false);
        let original_out = STAmount::from_xrp_amount(XRPAmount::from_drops(7_721_222));
        let rate =
            Quality::from_amounts(&Amounts::new(original_in.clone(), original_out.clone())).rate();

        let remaining_out = STAmount::from_xrp_amount(XRPAmount::from_drops(7_000_000));
        let remaining_in = remaining_out.mul_round(&rate, original_in.asset(), true);
        let reconstructed_out =
            protocol::div_round_strict(&remaining_in, &rate, original_out.asset(), false);
        assert!(remaining_in.signum() > 0);
        assert!(reconstructed_out <= remaining_out);
    }

    #[test]
    fn canonical_3e8efc65_tick_size_rate_remains_non_native() {
        // Canonical OfferCreate 3E8EFC…730D0B in ledger 106132761:
        // BRRL 255395 -> RLUSD 50000, with the BRRL issuer TickSize=5.
        let brrl = protocol::Issue::new(
            protocol::currency_from_string("BRRL"),
            protocol::AccountID::from_array([0xB7; 20]),
        );
        let rlusd = protocol::Issue::new(
            protocol::currency_from_string("RLUSD"),
            protocol::AccountID::from_array([0xE5; 20]),
        );
        let taker_gets = STAmount::from_iou_amount(
            sf("sfTakerGets"),
            protocol::IOUAmount::from_parts(255_395, 0).expect("canonical BRRL"),
            brrl,
        );
        let taker_pays = STAmount::from_iou_amount(
            sf("sfTakerPays"),
            protocol::IOUAmount::from_parts(50_000, 0).expect("canonical RLUSD"),
            rlusd,
        );

        let quality = round_quality(
            get_rate(&taker_gets, &taker_pays).expect("canonical quality"),
            5,
        );
        let rate = quality_to_rate_amount(quality);
        assert!(
            !rate.native(),
            "Quality::rate must use the no-issue arithmetic sentinel"
        );
        let rounded_gets = taker_pays
            .try_divide(&rate, taker_gets.asset())
            .expect("non-native tick-rounded rate must be representable");

        assert_eq!(rounded_gets.text(), "255388.7016038411");
        assert_eq!(quality, 0x5406_f49b_d58a_9000);
    }

    #[test]
    fn open_book_directory_metadata_can_keep_original_exchange_rate() {
        let issuer = protocol::AccountID::from_array([0x55; 20]);
        let currency = protocol::currency_from_string("USD");
        let taker_pays = STAmount::from_iou_amount(
            sf("sfTakerPays"),
            protocol::IOUAmount::from_parts(100, 0).expect("valid iou"),
            protocol::Issue::new(currency, issuer),
        );
        let taker_gets = STAmount::from_xrp_amount(XRPAmount::from_drops(250));
        let mut dir = protocol::STObject::new(sf("sfLedgerEntry"));

        set_book_directory_fields(&mut dir, &taker_pays, &taker_gets, 42, None);

        assert_eq!(dir.get_field_u64(sf("sfExchangeRate")), 42);
        assert!(!dir.is_field_present(sf("sfDomainID")));
        assert!(dir.is_field_present(sf("sfTakerPaysCurrency")));
        assert!(dir.is_field_present(sf("sfTakerPaysIssuer")));
    }
}
