//! Success-path regressions for generic OfferCreate book consumption.
//!
//! Source parity: rippled `src/libxrpl/tx/paths/BookStep.cpp::limitStepIn`
//! operates on generic `TIn`/`TOut` amounts. It must not assume that a
//! limited book input is native XRP.

use super::*;

fn iou_amount(value: i64, issue: protocol::Issue) -> STAmount {
    STAmount::from_iou_amount(
        sf("sfAmount"),
        protocol::IOUAmount::from_parts(value, 0).expect("positive canonical IOU amount"),
        issue,
    )
}

#[test]
fn brrl_to_rlusd_limited_input_is_a_generic_iou_book_fill() {
    // Values are the canonical 2FA0… OfferCreate's BRRL/RLUSD shape. A
    // smaller remaining BRRL input takes the BookStep `limitStepIn` branch.
    let brrl = protocol::Issue::new(
        protocol::currency_from_string("BRRL"),
        AccountID::from_array([0xB1; 20]),
    );
    let rlusd = protocol::Issue::new(
        protocol::currency_from_string("RLUSD"),
        AccountID::from_array([0xC2; 20]),
    );
    let remaining_brrl = iou_amount(1_000, brrl);
    let available_rlusd = iou_amount(50_000, rlusd);
    let offer_in = iou_amount(255_960, brrl);
    let offer_quality =
        Quality::from_amounts(&Amounts::new(offer_in.clone(), available_rlusd.clone()));

    let consumed = compute_offer_consumption(
        &remaining_brrl,
        &available_rlusd,
        &offer_in,
        &available_rlusd,
        offer_quality,
        &available_rlusd,
        QUALITY_ONE,
        QUALITY_ONE,
        true,
    );

    assert_eq!(consumed.step_in, remaining_brrl);
    assert_eq!(consumed.step_in.asset(), Asset::Issue(brrl));
    assert_eq!(consumed.offer_in.asset(), Asset::Issue(brrl));
    assert_eq!(consumed.step_out.asset(), Asset::Issue(rlusd));
    assert_eq!(consumed.offer_out.asset(), Asset::Issue(rlusd));
    assert!(consumed.step_out.signum() > 0);
}
