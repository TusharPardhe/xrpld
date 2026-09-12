use crate::{abi::Number, int_abi, int_arithmetic};
use basics::number::{
    MantissaScale, NumberArithmeticError, NumberParts, RoundingMode, set_mantissa_scale,
    set_rounding_mode,
};
use protocol::{MPTAmount, XRPAmount, mpt_amount, xrp_amount};

pub struct Report {
    pub checks: usize,
    pub common_parity_checks: usize,
    pub divergence_classes: usize,
    pub divergence_observations: usize,
}

fn wire(value: NumberParts) -> Number {
    Number {
        negative: value.negative as u8,
        mantissa: value.mantissa,
        exponent: i64::from(value.exponent),
    }
}
fn number(value: Number) -> NumberParts {
    NumberParts::unchecked(value.negative != 0, value.mantissa, value.exponent as i32)
}
fn error(tag: u8) -> NumberArithmeticError {
    match tag {
        0 => NumberArithmeticError::Overflow,
        1 => NumberArithmeticError::DivideByZero,
        unknown => panic!(
            "Lean IntAmount error tag has no Quaxar NumberArithmeticError equivalent: {unknown}"
        ),
    }
}
fn mode(tag: u8) -> RoundingMode {
    [
        RoundingMode::ToNearest,
        RoundingMode::TowardsZero,
        RoundingMode::Downward,
        RoundingMode::Upward,
    ][tag as usize]
}
fn generated(state: &mut u64) -> i64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state as i64
}
fn ratio_same(lean: Result<i64, u8>, rust: Result<MPTAmount, NumberArithmeticError>) {
    assert_eq!(lean.map_err(error), rust.map(MPTAmount::value));
}

pub fn run() -> Report {
    set_mantissa_scale(MantissaScale::Large330);
    let min = i64::MIN;
    let max = i64::MAX;
    let values = [min, min + 1, -2, -1, 0, 1, 2, max - 1, max];
    let mut checks = 0;
    let divergence_observations = 0;
    for &value in &values {
        assert_eq!(int_abi::direct(0, value, 0), MPTAmount::from(value).value());
        assert_eq!(MPTAmount::from(value).signum(), value.signum() as i32);
        assert_eq!(XRPAmount::from(value).signum(), value.signum() as i32);
        checks += 3;
        for &other in &values {
            let expected = [
                value == other,
                value != other,
                value == other,
                value != other,
                value < other,
                value <= other,
                value > other,
                value >= other,
            ];
            for (relation, expected) in expected.into_iter().enumerate() {
                assert_eq!(int_abi::compare(relation as u8, value, other), expected);
                checks += 1;
            }
        }
    }
    let arithmetic = int_arithmetic::run(min, max, &values);
    checks += arithmetic.checks;
    for tag in 0..4 {
        set_rounding_mode(mode(tag));
        for &value in &values {
            let lean = number(int_abi::to_number(value, tag).unwrap());
            let quaxar = NumberParts::from(MPTAmount::from(value));
            assert_eq!(lean, quaxar);
            checks += 1;
        }
        let inputs = [
            NumberParts::zero(),
            NumberParts::from_i64_and_exponent(15, -1),
            NumberParts::from_i64_and_exponent(-15, -1),
            NumberParts::from_i64_and_exponent(25, -1),
            NumberParts::from_i64_and_exponent(-25, -1),
            NumberParts::from_i64(max),
            NumberParts::unchecked(false, 9_223_372_036_854_775_807, 5),
        ];
        for input in inputs {
            assert_eq!(
                int_abi::from_number(wire(input), tag).map_err(error),
                MPTAmount::from_number(input).map(MPTAmount::value)
            );
            checks += 1;
        }
        let mut seed = 0x1A2B_3C4D_5E6F_7788;
        for _ in 0..128 {
            let raw = generated(&mut seed);
            let input =
                NumberParts::from_i64_and_exponent(raw % 1_000_000_000, (raw as i32 % 5) - 2);
            assert_eq!(
                int_abi::from_number(wire(input), tag).map_err(error),
                MPTAmount::from_number(input).map(MPTAmount::value)
            );
            checks += 1;
        }
    }
    set_rounding_mode(RoundingMode::ToNearest);
    for &(value, num, den, up) in &[
        (0, 1, 0, false),
        (1, 1, 3, false),
        (1, 1, 3, true),
        (-1, 1, 3, false),
        (-1, 1, 3, true),
        (10, 3, 4, false),
        (10, 3, 4, true),
        (-10, 3, 4, false),
        (-10, 3, 4, true),
        (max, 0, 1, false),
        (max, 1, 1, false),
        (max, 2, 1, false),
        (1 << 31, 1 << 31, 1, false),
        (u32::MAX as i64 - 1, 1, u32::MAX, true),
    ] {
        ratio_same(
            int_abi::mul_ratio(value, num, den, up),
            mpt_amount::mul_ratio(MPTAmount::from(value), num, den, up),
        );
        assert_eq!(
            int_abi::mul_ratio(value, num, den, up).map_err(error),
            xrp_amount::mul_ratio(XRPAmount::from(value), num, den, up).map(XRPAmount::drops)
        );
        checks += 2;
    }
    ratio_same(
        int_abi::mul_ratio(min, 2, 1, false),
        mpt_amount::mul_ratio(MPTAmount::from(min), 2, 1, false),
    );
    assert_eq!(
        int_abi::mul_ratio(min, 2, 1, false).map_err(error),
        Err(NumberArithmeticError::Overflow)
    );
    checks += 2;
    assert_eq!(checks, 1_325, "retain IntAmount harness coverage");
    assert_eq!(divergence_observations, 0);
    Report {
        checks,
        common_parity_checks: checks,
        divergence_classes: 0,
        divergence_observations,
    }
}
