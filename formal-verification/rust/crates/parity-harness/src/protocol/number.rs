use crate::abi::{self, Number};
use basics::number::{
    MantissaScale, NUMBER_MAX_EXPONENT, NUMBER_MAX_REP, NUMBER_MIN_EXPONENT, NUMBER_ZERO_EXPONENT,
    NumberArithmeticError, NumberParts, RoundingMode, set_mantissa_scale, set_rounding_mode,
};

fn wire(value: NumberParts) -> Number {
    Number {
        negative: u8::from(value.negative),
        mantissa: value.mantissa,
        exponent: i64::from(value.exponent),
    }
}
fn rust(value: Number) -> NumberParts {
    NumberParts::unchecked(
        value.negative != 0,
        value.mantissa,
        i32::try_from(value.exponent).expect("Lean exponent fits i32"),
    )
}
fn classify_lean_error(raw: u8) -> NumberArithmeticError {
    match raw {
        0 => NumberArithmeticError::Overflow,
        1 => NumberArithmeticError::DivideByZero,
        unknown => panic!(
            "Lean Number error tag has no Quaxar NumberArithmeticError equivalent: {unknown}"
        ),
    }
}
fn same_result(
    actual: Result<Number, u8>,
    expected: Result<NumberParts, NumberArithmeticError>,
) -> bool {
    match (actual, expected) {
        (Ok(a), Ok(b)) => rust(a) == b,
        (Err(0), Err(NumberArithmeticError::Overflow))
        | (Err(1), Err(NumberArithmeticError::DivideByZero)) => true,
        _ => false,
    }
}
fn generated(state: &mut u64, index: usize) -> NumberParts {
    if index.is_multiple_of(29) {
        return NumberParts::zero();
    }
    let next = |s: &mut u64| {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    };
    let min = 1_000_000_000_000_000_000_u64;
    NumberParts::unchecked(
        next(state) & 1 != 0,
        min + next(state) % (NUMBER_MAX_REP as u64 - min + 1),
        (next(state) % 257) as i32 - 128,
    )
}

pub fn run() -> usize {
    set_mantissa_scale(MantissaScale::Large330);
    let zero = NumberParts::zero();
    let one = NumberParts::one(MantissaScale::Large330);
    let unit = NumberParts::unchecked(false, 1_000_000_000_000_000_000, 0);
    let distant = NumberParts::unchecked(false, 1_234_567_890_123_456_789, -22);
    let cusp = NumberParts::unchecked(false, NUMBER_MAX_REP as u64, 0);
    let factor = NumberParts::unchecked(false, 1_000_000_000_000_000_001, -18);
    let half = NumberParts::unchecked(false, 5_000_000_000_000_000_000, -19);
    let exact_zero_tail = NumberParts::unchecked(false, 1_000_000_000_000_000_000, -20);
    let cusp_above = NumberParts::unchecked(false, 9_223_372_036_854_775_810, 0);
    let half_above = NumberParts::unchecked(false, 5_000_000_000_000_000_001, -19);
    let two = NumberParts::try_from_external_parts(2, 0, MantissaScale::Large330).unwrap();
    let min = NumberParts::unchecked(false, 1_000_000_000_000_000_000, NUMBER_MIN_EXPONENT);
    let max = NumberParts::unchecked(false, NUMBER_MAX_REP as u64, NUMBER_MAX_EXPONENT);
    let values = [
        zero, one, -one, unit, -unit, distant, cusp, factor, half, min, max,
    ];
    for value in values {
        assert!(value.is_normalized(MantissaScale::Large330));
        assert_eq!(rust(abi::normalized_roundtrip(wire(value))), value);
        assert_eq!(rust(abi::raw_roundtrip(wire(value))), value);
        assert_eq!(rust(abi::neg(wire(value))), -value);
        assert_eq!(abi::signum(wire(value)), i64::from(value.signum()));
        for mode in 0..4 {
            assert_eq!(rust(abi::normalize(wire(value), mode).unwrap()), value);
        }
    }
    for (lhs, rhs) in [
        (zero, one),
        (one, one),
        (-one, zero),
        (cusp, factor),
        (min, max),
    ] {
        let expected = [
            lhs == rhs,
            lhs != rhs,
            lhs < rhs,
            lhs <= rhs,
            lhs > rhs,
            lhs >= rhs,
        ];
        for (relation, expected) in expected.into_iter().enumerate() {
            assert_eq!(abi::compare(relation as u8, wire(lhs), wire(rhs)), expected);
        }
    }
    let pairs = [
        (one, two),
        (unit, exact_zero_tail),
        (unit, distant),
        (cusp, factor),
        (-unit, distant),
        (max, one),
        (one, zero),
        (min, max),
        (cusp_above, one),
        (unit, half),
        (unit, half_above),
        (-unit, -half),
    ];
    let mut checks = 0;
    for (tag, mode) in [
        (0, RoundingMode::ToNearest),
        (1, RoundingMode::TowardsZero),
        (2, RoundingMode::Downward),
        (3, RoundingMode::Upward),
    ] {
        set_rounding_mode(mode);
        for (lhs, rhs) in pairs.into_iter().chain((0..500).map(|i| {
            let mut s = 0x5eed_f0a1_cafe_beef ^ i as u64;
            (generated(&mut s, i), generated(&mut s, i + 11))
        })) {
            for (op, expected) in [
                lhs.try_add(rhs),
                lhs.try_sub(rhs),
                lhs.try_mul(rhs),
                lhs.try_div(rhs),
            ]
            .into_iter()
            .enumerate()
            {
                assert!(
                    same_result(abi::binary(op as u8, wire(lhs), wire(rhs), tag), expected),
                    "op={op} mode={mode:?} lhs={lhs:?} rhs={rhs:?}"
                );
                checks += 1;
            }
        }
        assert_eq!(abi::binary(3, wire(one), wire(zero), tag), Err(1));
        assert_eq!(one.try_div(zero), Err(NumberArithmeticError::DivideByZero));
        assert_eq!(abi::binary(0, wire(max), wire(max), tag), Err(0));
        assert_eq!(max.try_add(max), Err(NumberArithmeticError::Overflow));
        assert_eq!(abi::binary(2, wire(max), wire(unit), tag), Err(0));
        assert_eq!(max.try_mul(unit), Err(NumberArithmeticError::Overflow));
        assert_eq!(abi::binary(3, wire(max), wire(min), tag), Err(0));
        assert_eq!(max.try_div(min), Err(NumberArithmeticError::Overflow));
        checks += 5;
        assert_eq!(
            abi::binary(3, wire(min), wire(max), tag).map(rust),
            Ok(zero)
        );
        for value in [unit, -unit, half, -half] {
            assert_eq!(
                abi::to_rep(wire(value), tag)
                    .map(|v| v as u64)
                    .map_err(classify_lean_error),
                value.try_to_i64().map(|v| v as u64)
            );
        }
    }
    set_rounding_mode(RoundingMode::ToNearest);
    assert_eq!(zero.exponent, NUMBER_ZERO_EXPONENT);
    checks
}
