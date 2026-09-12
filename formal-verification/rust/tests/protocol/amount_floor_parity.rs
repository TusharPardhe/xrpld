use basics::number::{
    MantissaScale, NumberArithmeticError, NumberMantissaScaleGuard, NumberParts,
    NumberRoundModeGuard, RoundingMode,
};
use protocol::{
    DROPS_PER_XRP, IOU_ZERO_EXPONENT, IOUAmount, JsonValue, MAX_MP_TOKEN_AMOUNT, MPTAmount,
    NumberJsonInput, NumberPartsError, XRPAmount, iou_amount, mpt_amount,
    normalized_parts_from_string, number_from_json_input, xrp_amount,
};

#[test]
fn xrp_amount_matches_core_drop_contract() {
    let mut amount = XRPAmount::from(5);
    amount += XRPAmount::from(7);
    amount -= XRPAmount::from(2);
    amount += 3;
    amount -= 1;
    amount *= 2;

    assert_eq!(amount, XRPAmount::from(24));
    assert_eq!((-amount).drops(), -24);
    assert_eq!(amount.signum(), 1);
    assert_eq!(XRPAmount::from(0).signum(), 0);
    assert_eq!(XRPAmount::from(-1).signum(), -1);
    assert!(bool::from(amount));
    assert!(!bool::from(XRPAmount::default()));
    assert_eq!(DROPS_PER_XRP.drops(), 1_000_000);
    assert_eq!(XRPAmount::min_positive_amount().drops(), 1);
    assert_eq!(XRPAmount::from(1_500_000).decimal_xrp(), 1.5);
}

#[test]
fn xrp_amount_number_conversion_rounds() {
    let _scale = NumberMantissaScaleGuard::new(MantissaScale::Large);
    let _rounding = NumberRoundModeGuard::new(RoundingMode::ToNearest);

    let one_point_five =
        NumberParts::try_from_external_parts(15, -1, MantissaScale::Large).expect("number");
    let minus_one_point_five =
        NumberParts::try_from_external_parts(-15, -1, MantissaScale::Large).expect("number");

    assert_eq!(
        XRPAmount::try_from(one_point_five).expect("rounded"),
        XRPAmount::from(2)
    );
    assert_eq!(
        XRPAmount::try_from(minus_one_point_five).expect("rounded"),
        XRPAmount::from(-2)
    );
    assert_eq!(
        NumberParts::from(XRPAmount::from(25))
            .try_to_i64()
            .expect("i64"),
        25
    );
}

#[test]
fn xrp_amount_clips_and_converts_bounds() {
    assert_eq!(XRPAmount::from(7).drops_as::<u32>(), Some(7));
    assert_eq!(XRPAmount::from(-1).drops_as::<u32>(), None);
    assert_eq!(
        XRPAmount::from(i64::from(i32::MAX) + 1).json_clipped(),
        JsonValue::Signed(i64::from(i32::MAX))
    );
    assert_eq!(
        XRPAmount::from(i64::from(i32::MIN) - 1).json_clipped(),
        JsonValue::Signed(i64::from(i32::MIN))
    );
}

#[test]
fn xrp_amount_mul_ratio_matches_rounding_rules() {
    assert_eq!(
        xrp_amount::mul_ratio(XRPAmount::from(10), 3, 4, false).expect("ratio"),
        XRPAmount::from(7)
    );
    assert_eq!(
        xrp_amount::mul_ratio(XRPAmount::from(10), 3, 4, true).expect("ratio"),
        XRPAmount::from(8)
    );
    assert_eq!(
        xrp_amount::mul_ratio(XRPAmount::from(-10), 3, 4, false).expect("ratio"),
        XRPAmount::from(-8)
    );
    assert_eq!(
        xrp_amount::mul_ratio(XRPAmount::from(-10), 3, 4, true).expect("ratio"),
        XRPAmount::from(-7)
    );
    assert_eq!(
        xrp_amount::mul_ratio(XRPAmount::from(1), 1, 0, false),
        Err(NumberArithmeticError::DivideByZero)
    );
    assert_eq!(
        xrp_amount::mul_ratio(XRPAmount::from(i64::MAX), 2, 1, false),
        Err(NumberArithmeticError::Overflow)
    );
}

#[test]
fn mpt_amount_matches_core_value_contract() {
    let mut amount = MPTAmount::from(5);
    amount += MPTAmount::from(7);
    amount -= MPTAmount::from(2);

    assert_eq!(amount, MPTAmount::from(10));
    assert_eq!((-amount).value(), -10);
    assert_eq!(amount.signum(), 1);
    assert_eq!(MPTAmount::from(0).signum(), 0);
    assert_eq!(MPTAmount::from(-1).signum(), -1);
    assert!(bool::from(amount));
    assert!(!bool::from(MPTAmount::default()));
    assert_eq!(MPTAmount::min_positive_amount().value(), 1);
    assert_eq!(MAX_MP_TOKEN_AMOUNT, 0x7FFF_FFFF_FFFF_FFFF);
}

#[test]
fn mpt_amount_number_conversion_and_mul_ratio_match_cpp() {
    let _scale = NumberMantissaScaleGuard::new(MantissaScale::Large);
    let _rounding = NumberRoundModeGuard::new(RoundingMode::ToNearest);

    let value = NumberParts::try_from_external_parts(25, 0, MantissaScale::Large).expect("number");
    assert_eq!(
        MPTAmount::try_from(value).expect("mpt"),
        MPTAmount::from(25)
    );
    assert_eq!(
        NumberParts::from(MPTAmount::from(25))
            .try_to_i64()
            .expect("i64"),
        25
    );

    assert_eq!(
        mpt_amount::mul_ratio(MPTAmount::from(10), 3, 4, false).expect("ratio"),
        MPTAmount::from(7)
    );
    assert_eq!(
        mpt_amount::mul_ratio(MPTAmount::from(10), 3, 4, true).expect("ratio"),
        MPTAmount::from(8)
    );
    assert_eq!(
        mpt_amount::mul_ratio(MPTAmount::from(-10), 3, 4, false).expect("ratio"),
        MPTAmount::from(-8)
    );
    assert_eq!(
        mpt_amount::mul_ratio(MPTAmount::from(-10), 3, 4, true).expect("ratio"),
        MPTAmount::from(-7)
    );
    assert_eq!(
        mpt_amount::mul_ratio(MPTAmount::from(1), 1, 0, false),
        Err(NumberArithmeticError::DivideByZero)
    );
    assert_eq!(
        mpt_amount::mul_ratio(MPTAmount::from(i64::MAX), 2, 1, false),
        Err(NumberArithmeticError::Overflow)
    );
}

#[test]
fn st_number_floor_boundaries_match_current_iou_floor_by_scale() {
    let _rounding = NumberRoundModeGuard::new(RoundingMode::ToNearest);

    {
        let _scale = NumberMantissaScaleGuard::new(MantissaScale::Small);

        assert_eq!(
            normalized_parts_from_string("1e-32753"),
            Ok(NumberParts::min(MantissaScale::Small))
        );
        assert_eq!(
            normalized_parts_from_string("1e-32754"),
            Ok(NumberParts::zero())
        );
        assert!(
            number_from_json_input(NumberJsonInput::String("1e-32754"))
                .expect("underflow should still construct")
                .is_default()
        );
    }

    {
        let _scale = NumberMantissaScaleGuard::new(MantissaScale::Large);

        assert_eq!(
            normalized_parts_from_string("1e-32750"),
            Ok(NumberParts::min(MantissaScale::Large))
        );
        assert_eq!(
            normalized_parts_from_string("1e-32751"),
            Ok(NumberParts::zero())
        );
        assert!(
            number_from_json_input(NumberJsonInput::String("1e-32751"))
                .expect("underflow should still construct")
                .is_default()
        );
    }
}

#[test]
fn st_number_amount_range_boundaries_match_current_shared_contract_by_scale() {
    let _rounding = NumberRoundModeGuard::new(RoundingMode::TowardsZero);

    {
        let _scale = NumberMantissaScaleGuard::new(MantissaScale::Small);

        assert_eq!(
            normalized_parts_from_string("9999999999999999e32768"),
            Ok(NumberParts::max(MantissaScale::Small))
        );
        assert_eq!(
            normalized_parts_from_string("99999999999999999e32768"),
            Err(NumberPartsError::ExponentOverflow)
        );
    }

    {
        let _scale = NumberMantissaScaleGuard::new(MantissaScale::Large);

        assert_eq!(
            normalized_parts_from_string("9223372036854775807e32768"),
            Ok(NumberParts::max(MantissaScale::Large))
        );
        assert_eq!(
            normalized_parts_from_string("9223372036854775808e32768"),
            Err(NumberPartsError::ExponentOverflow)
        );
    }
}

#[test]
fn iou_amount_zero_and_signum_match_cpp() {
    let zero = IOUAmount::from_parts(0, 0).expect("canonical zero");
    assert_eq!(zero.mantissa(), 0);
    assert_eq!(zero.exponent(), IOU_ZERO_EXPONENT);
    assert_eq!(zero.signum(), 0);
    assert!(!bool::from(zero));
    assert_eq!(zero, -zero);

    let default_zero = IOUAmount::default();
    assert_eq!(default_zero, zero);

    let negative = IOUAmount::from_parts(-1, 0).expect("negative");
    let positive = IOUAmount::from_parts(1, 0).expect("positive");
    assert_eq!(negative.signum(), -1);
    assert_eq!(positive.signum(), 1);
}

#[test]
fn iou_amount_ordering_and_strings_match_cpp() {
    let negative = IOUAmount::from_parts(-2, 0).expect("negative");
    let zero = IOUAmount::from_parts(0, 0).expect("zero");
    let positive = IOUAmount::from_parts(2, 0).expect("positive");

    assert!(negative < zero);
    assert!(positive > zero);
    assert!(negative < positive);

    assert_eq!(negative.to_string(), "-2");
    assert_eq!(zero.to_string(), "0");
    assert_eq!(
        IOUAmount::from_parts(25, -3).expect("fraction").to_string(),
        "0.025"
    );
    assert_eq!(
        IOUAmount::from_parts(-25, -3)
            .expect("fraction")
            .to_string(),
        "-0.025"
    );
    assert_eq!(
        IOUAmount::from_parts(25, 1).expect("scaled").to_string(),
        "250"
    );
    assert_eq!(
        IOUAmount::from_parts(2, 20)
            .expect("scientific")
            .to_string(),
        "2e20"
    );
    assert_eq!(
        IOUAmount::from_parts(-2, -20)
            .expect("scientific")
            .to_string(),
        "-2e-20"
    );
}

#[test]
fn iou_amount_mul_ratio_rounding_and_underflow() {
    let min_mantissa = 1_000_000_000_000_000i64;
    let max_mantissa = 9_999_999_999_999_999i64;
    let min_exponent = -96i32;
    let max_exponent = 80i32;
    let max_uint = u32::MAX;

    let tiny = IOUAmount::from_parts(min_mantissa, min_exponent).expect("tiny");
    assert_eq!(
        iou_amount::mul_ratio(tiny, 1, max_uint, true).expect("ratio"),
        tiny
    );
    assert_eq!(
        iou_amount::mul_ratio(tiny, 1, max_uint, false).expect("ratio"),
        IOUAmount::default()
    );

    let tiny_negative = IOUAmount::from_parts(-min_mantissa, min_exponent).expect("tiny negative");
    assert_eq!(
        iou_amount::mul_ratio(tiny_negative, 1, max_uint, true).expect("ratio"),
        IOUAmount::default()
    );
    assert_eq!(
        iou_amount::mul_ratio(tiny_negative, 1, max_uint, false).expect("ratio"),
        tiny_negative
    );

    let big = IOUAmount::from_parts(max_mantissa, max_exponent).expect("big");
    assert_eq!(
        iou_amount::mul_ratio(big, max_uint, max_uint, true).expect("ratio"),
        big
    );
    assert_eq!(
        iou_amount::mul_ratio(big, max_uint, max_uint, false).expect("ratio"),
        big
    );

    let one = IOUAmount::from_parts(1, 0).expect("one");
    let rounded_up = iou_amount::mul_ratio(one, max_uint - 1, max_uint, true).expect("ratio");
    let rounded_down = iou_amount::mul_ratio(one, max_uint - 1, max_uint, false).expect("ratio");
    assert_eq!(rounded_up.mantissa() - rounded_down.mantissa(), 1);

    assert_eq!(
        iou_amount::mul_ratio(one, 1, 0, true),
        Err(NumberArithmeticError::DivideByZero)
    );
    assert_eq!(
        iou_amount::mul_ratio(big, 2, 0, true),
        Err(NumberArithmeticError::DivideByZero)
    );
}

#[test]
fn mpt_amount_direct_operators_wrap_i64_boundaries() {
    assert_eq!(
        (MPTAmount::from(i64::MAX) + MPTAmount::from(1)).value(),
        i64::MIN
    );
    assert_eq!(
        (MPTAmount::from(i64::MIN) - MPTAmount::from(1)).value(),
        i64::MAX
    );
    assert_eq!((MPTAmount::from(i64::MIN) * -1).value(), i64::MIN);
    assert_eq!((-MPTAmount::from(i64::MIN)).value(), i64::MIN);

    let mut add = MPTAmount::from(i64::MAX);
    add += MPTAmount::from(1);
    assert_eq!(add.value(), i64::MIN);
    let mut subtract = MPTAmount::from(i64::MIN);
    subtract -= MPTAmount::from(1);
    assert_eq!(subtract.value(), i64::MAX);
    let mut multiply = MPTAmount::from(i64::MIN);
    multiply *= -1;
    assert_eq!(multiply.value(), i64::MIN);
}

#[test]
fn xrp_amount_direct_operators_wrap_i64_boundaries() {
    assert_eq!(
        (XRPAmount::from(i64::MAX) + XRPAmount::from(1)).drops(),
        i64::MIN
    );
    assert_eq!(
        (XRPAmount::from(i64::MIN) - XRPAmount::from(1)).drops(),
        i64::MAX
    );
    assert_eq!((XRPAmount::from(i64::MIN) * -1).drops(), i64::MIN);
    assert_eq!((-XRPAmount::from(i64::MIN)).drops(), i64::MIN);

    let mut add = XRPAmount::from(i64::MAX);
    add += XRPAmount::from(1);
    assert_eq!(add.drops(), i64::MIN);
    let mut subtract = XRPAmount::from(i64::MIN);
    subtract -= 1;
    assert_eq!(subtract.drops(), i64::MAX);
    let mut multiply = XRPAmount::from(i64::MIN);
    multiply *= -1;
    assert_eq!(multiply.drops(), i64::MIN);
}
