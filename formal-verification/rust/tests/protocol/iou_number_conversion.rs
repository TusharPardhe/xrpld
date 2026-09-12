use basics::number::{
    MantissaScale, NUMBER_MAX_EXPONENT, NUMBER_MAX_REP, NUMBER_ZERO_EXPONENT,
    NumberArithmeticError, NumberMantissaScaleGuard, NumberParts,
};
use protocol::{
    IOU_ZERO_EXPONENT, IOUAmount,
    iou_amount::{
        MAX_IOU_EXPONENT, MAX_IOU_MANTISSA, MIN_IOU_EXPONENT, MIN_IOU_MANTISSA,
        raw_iou_parts_from_number,
    },
};

fn number(mantissa: u64, exponent: i32) -> NumberParts {
    NumberParts::unchecked(false, mantissa, exponent)
}

#[test]
fn raw_iou_number_parts_preserve_zero_and_out_of_range_exponents() {
    let _scale = NumberMantissaScaleGuard::new(MantissaScale::Large330);
    assert_eq!(
        raw_iou_parts_from_number(NumberParts::zero()),
        Ok((0, NUMBER_ZERO_EXPONENT))
    );
    assert_eq!(
        raw_iou_parts_from_number(number(MIN_IOU_MANTISSA as u64, 81)),
        Ok((MIN_IOU_MANTISSA, 81))
    );
    assert_eq!(
        raw_iou_parts_from_number(number(MIN_IOU_MANTISSA as u64, -200)),
        Ok((MIN_IOU_MANTISSA, -200))
    );
}

#[test]
fn canonical_iou_number_conversion_enforces_bounds_and_zero() {
    let _scale = NumberMantissaScaleGuard::new(MantissaScale::Large330);
    assert_eq!(
        IOUAmount::from_number(NumberParts::zero()),
        Ok(IOUAmount::new())
    );
    assert_eq!(IOUAmount::new().exponent(), IOU_ZERO_EXPONENT);
    assert_eq!(
        IOUAmount::from_number(number(MIN_IOU_MANTISSA as u64, 81)),
        Err(NumberArithmeticError::Overflow)
    );
    assert_eq!(
        IOUAmount::from_number(number(MIN_IOU_MANTISSA as u64, -200)),
        Ok(IOUAmount::new())
    );
}

#[test]
fn raw_iou_number_parts_and_canonical_amount_accept_exact_bounds() {
    let _scale = NumberMantissaScaleGuard::new(MantissaScale::Large330);
    for (mantissa, exponent) in [
        (MIN_IOU_MANTISSA, MIN_IOU_EXPONENT),
        (MAX_IOU_MANTISSA, MAX_IOU_EXPONENT),
    ] {
        let input = number(mantissa as u64, exponent);
        assert_eq!(raw_iou_parts_from_number(input), Ok((mantissa, exponent)));
        assert_eq!(
            IOUAmount::from_number(input),
            IOUAmount::from_parts(mantissa, exponent)
        );
    }
}

#[test]
fn raw_iou_number_parts_report_runtime_normalization_overflow() {
    let _scale = NumberMantissaScaleGuard::new(MantissaScale::Large330);
    let input = number(NUMBER_MAX_REP as u64, NUMBER_MAX_EXPONENT);
    assert_eq!(
        raw_iou_parts_from_number(input),
        Err(NumberArithmeticError::Overflow)
    );
    assert_eq!(
        IOUAmount::from_number(input),
        Err(NumberArithmeticError::Overflow)
    );
}
