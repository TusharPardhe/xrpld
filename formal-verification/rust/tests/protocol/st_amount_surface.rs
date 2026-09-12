use basics::number::{
    MantissaScale, RoundingMode, get_rounding_mode, set_mantissa_scale, set_rounding_mode,
};
use protocol::{
    IOUAmount, Issue, MPTAmount, MPTIssue, STAmount, can_add, can_subtract, currency_from_string,
    make_mpt_id, no_issue, parse_base58_account_id, round_to_exponent, sf_generic,
};

fn account(value: &str) -> protocol::AccountID {
    parse_base58_account_id(value).expect("valid account")
}

fn iou(mantissa: u64, exponent: i32, negative: bool) -> STAmount {
    STAmount::new_with_asset(sf_generic(), no_issue(), mantissa, exponent, negative)
}

#[test]
fn stamount_can_add_ports_integral_iou_and_comparability_cases() {
    set_mantissa_scale(MantissaScale::Large330);
    let max = STAmount::new_native(i64::MAX as u64, false);
    let min = STAmount::new_native((i64::MAX as u64) + 1, true);
    let one = STAmount::new_native(1, false);
    let negative_one = STAmount::new_native(1, true);

    assert!(!can_add(&max, &one, RoundingMode::ToNearest));
    assert!(!can_add(&min, &negative_one, RoundingMode::ToNearest));
    assert!(can_add(
        &STAmount::new_native(0, false),
        &one,
        RoundingMode::ToNearest
    ));
    assert!(can_add(
        &one,
        &STAmount::new_native(0, false),
        RoundingMode::ToNearest
    ));
    assert!(can_add(
        &STAmount::new_native(1_000, false),
        &STAmount::new_native(2_000, false),
        RoundingMode::ToNearest
    ));

    let equal = iou(5_000_000_000_000_000, 0, false);
    let distant = iou(1_000_000_000_000_000, -96, false);
    let huge = iou(9_999_999_999_999_999, 80, false);
    for mode in [
        RoundingMode::ToNearest,
        RoundingMode::TowardsZero,
        RoundingMode::Downward,
        RoundingMode::Upward,
    ] {
        assert!(can_add(&equal, &equal, mode), "{mode:?}");
        assert!(!can_add(&huge, &distant, mode), "{mode:?}");
    }

    assert!(!can_add(&one, &equal, RoundingMode::ToNearest));
    let usd = Issue::new(
        currency_from_string("USD"),
        account("rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh"),
    );
    let eur = Issue::new(
        currency_from_string("EUR"),
        account("rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh"),
    );
    let usd_amount =
        STAmount::from_iou_amount(sf_generic(), IOUAmount::from_parts(500, 0).unwrap(), usd);
    let eur_amount =
        STAmount::from_iou_amount(sf_generic(), IOUAmount::from_parts(500, 0).unwrap(), eur);
    assert!(!can_add(&usd_amount, &eur_amount, RoundingMode::ToNearest));
}

#[test]
fn stamount_can_subtract_ports_balance_and_mpt_identity_cases() {
    let hundred = STAmount::new_native(100, false);
    let two_hundred = STAmount::new_native(200, false);
    let negative_hundred = STAmount::new_native(100, true);
    assert!(!can_subtract(&hundred, &two_hundred));
    assert!(can_subtract(&two_hundred, &hundred));
    assert!(can_subtract(&hundred, &negative_hundred));
    assert!(can_subtract(&hundred, &STAmount::new_native(0, false)));

    let iou_min = iou(1_000_000_000_000_000, 0, false);
    let iou_max = iou(9_999_999_999_999_999, 80, false);
    assert!(can_subtract(&iou_min, &iou_max));
    assert!(!can_subtract(&hundred, &iou_min));

    let owner = account("rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh");
    let first = MPTIssue::new(make_mpt_id(1, owner));
    let second = MPTIssue::new(make_mpt_id(2, owner));
    let max = STAmount::from_mpt_amount(sf_generic(), MPTAmount::from_value(i64::MAX), first);
    let negative_one = STAmount::from_mpt_amount(sf_generic(), MPTAmount::from_value(-1), first);
    assert!(!can_subtract(&max, &negative_one));
    assert!(!can_subtract(
        &STAmount::from_mpt_amount(sf_generic(), MPTAmount::from_value(100), first),
        &STAmount::from_mpt_amount(sf_generic(), MPTAmount::from_value(100), second),
    ));
}

#[test]
fn stamount_round_to_exponent_ports_known_noops_and_all_directed_modes() {
    set_mantissa_scale(MantissaScale::Large330);
    let integral = STAmount::new_native(1_000, false);
    let zero = iou(0, -100, false);
    let at_scale = iou(5_000_000_000_000_000, -5, false);
    assert_eq!(
        round_to_exponent(&integral, 0, RoundingMode::ToNearest).unwrap(),
        integral
    );
    assert_eq!(
        round_to_exponent(&zero, 0, RoundingMode::ToNearest).unwrap(),
        zero
    );
    assert_eq!(
        round_to_exponent(&at_scale, -5, RoundingMode::ToNearest).unwrap(),
        at_scale
    );
    assert_eq!(
        round_to_exponent(&at_scale, -6, RoundingMode::ToNearest).unwrap(),
        at_scale
    );

    let positive = iou(1_234_567_890_123_456, -10, false);
    let negative = iou(1_234_567_890_123_456, -10, true);
    for (mode, positive_mantissa, negative_mantissa) in [
        (
            RoundingMode::ToNearest,
            1_234_567_890_100_000,
            1_234_567_890_100_000,
        ),
        (
            RoundingMode::TowardsZero,
            1_234_567_890_100_000,
            1_234_567_890_100_000,
        ),
        (
            RoundingMode::Downward,
            1_234_567_890_100_000,
            1_234_567_890_200_000,
        ),
        (
            RoundingMode::Upward,
            1_234_567_890_200_000,
            1_234_567_890_100_000,
        ),
    ] {
        let rounded_positive = round_to_exponent(&positive, -5, mode).unwrap();
        let rounded_negative = round_to_exponent(&negative, -5, mode).unwrap();
        assert_eq!(
            (
                rounded_positive.mantissa(),
                rounded_positive.exponent(),
                rounded_positive.negative()
            ),
            (positive_mantissa, -10, false),
            "{mode:?}"
        );
        assert_eq!(
            (
                rounded_negative.mantissa(),
                rounded_negative.exponent(),
                rounded_negative.negative()
            ),
            (negative_mantissa, -10, true),
            "{mode:?}"
        );
    }
}

#[test]
fn stamount_explicit_mode_operations_restore_the_callers_rounding_mode() {
    set_rounding_mode(RoundingMode::TowardsZero);
    let value = iou(1_234_567_890_123_456, -10, false);
    assert!(can_add(&value, &value, RoundingMode::Upward));
    assert_eq!(get_rounding_mode(), RoundingMode::TowardsZero);
    round_to_exponent(&value, -5, RoundingMode::Downward).unwrap();
    assert_eq!(get_rounding_mode(), RoundingMode::TowardsZero);
    set_rounding_mode(RoundingMode::ToNearest);
}
