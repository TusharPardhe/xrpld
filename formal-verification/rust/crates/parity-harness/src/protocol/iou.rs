use crate::{
    abi::Number,
    iou_abi::{self, Iou},
};
use basics::number::{
    MantissaScale, NumberArithmeticError, NumberParts, RoundingMode, set_mantissa_scale,
    set_rounding_mode,
};
use protocol::{
    IOUAmount,
    iou_amount::{mul_ratio, raw_iou_parts_from_number},
};

fn wire(n: NumberParts) -> Number {
    Number {
        negative: n.negative as u8,
        mantissa: n.mantissa,
        exponent: i64::from(n.exponent),
    }
}
fn number(n: Number) -> NumberParts {
    NumberParts::unchecked(n.negative != 0, n.mantissa, n.exponent as i32)
}
fn raw(a: IOUAmount) -> Iou {
    Iou {
        mantissa: a.mantissa(),
        exponent: i64::from(a.exponent()),
    }
}
fn raw_parts((mantissa, exponent): (i64, i32)) -> Iou {
    Iou {
        mantissa,
        exponent: i64::from(exponent),
    }
}
fn rust(a: Iou) -> IOUAmount {
    IOUAmount::from_parts(a.mantissa, a.exponent as i32).expect("Lean canonical IOU")
}
fn error(tag: u8) -> NumberArithmeticError {
    match tag {
        0 => NumberArithmeticError::Overflow,
        1 => NumberArithmeticError::DivideByZero,
        other => {
            panic!("Lean IOU error tag {other} has no Quaxar NumberArithmeticError equivalent")
        }
    }
}
fn same<T: std::fmt::Debug + PartialEq>(
    lean: Result<T, u8>,
    quaxar: Result<T, NumberArithmeticError>,
) {
    assert_eq!(lean.map_err(error), quaxar, "Lean/Quaxar outcome mismatch");
}
fn same_iou(lean: Result<Iou, u8>, quaxar: Result<IOUAmount, NumberArithmeticError>) {
    same(lean, quaxar.map(raw));
}
fn same_raw(lean: Result<Iou, u8>, quaxar: Result<(i64, i32), NumberArithmeticError>) {
    same(lean, quaxar.map(raw_parts));
}
fn mode(tag: u8) -> RoundingMode {
    [
        RoundingMode::ToNearest,
        RoundingMode::TowardsZero,
        RoundingMode::Downward,
        RoundingMode::Upward,
    ][tag as usize]
}
fn generated(seed: &mut u64) -> IOUAmount {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    let m = 1_000_000_000_000_000 + (*seed % 9_000_000_000_000_000) as i64;
    IOUAmount::from_parts(
        if *seed & 1 == 0 { m } else { -m },
        (*seed % 177) as i32 - 96,
    )
    .unwrap()
}

pub fn run() -> usize {
    set_mantissa_scale(MantissaScale::Large330);
    let min = 1_000_000_000_000_000;
    let max = 9_999_999_999_999_999;
    let mut values = vec![
        IOUAmount::new(),
        IOUAmount::from_parts(min, -96).unwrap(),
        IOUAmount::from_parts(-min, -96).unwrap(),
        IOUAmount::from_parts(max, 80).unwrap(),
        IOUAmount::from_parts(-max, 80).unwrap(),
        IOUAmount::from_parts(max, 0).unwrap(),
    ];
    let mut seed = 0x1_0u64;
    values.extend((0..96).map(|_| generated(&mut seed)));
    let conversions = [
        NumberParts::zero(),
        NumberParts::unchecked(false, min as u64, 81),
        NumberParts::unchecked(false, min as u64, -200),
    ];
    let mut checks = 0;
    for tag in 0..4 {
        set_rounding_mode(mode(tag));
        for input in conversions {
            same_raw(
                iou_abi::from_number(wire(input), tag),
                raw_iou_parts_from_number(input),
            );
            same_iou(
                iou_abi::of_number(wire(input), tag),
                IOUAmount::from_number(input),
            );
            checks += 2;
        }
        for &(m, e) in &[
            (0, 0),
            (1, 0),
            (-1, 0),
            (min - 1, 0),
            (max + 1, 0),
            (min, -110),
            (max, 81),
        ] {
            same_iou(
                iou_abi::of_parts(m, e, tag),
                IOUAmount::from_parts(m, e as i32),
            );
            checks += 1;
        }
        for a in &values {
            assert_eq!(
                iou_abi::build(a.mantissa(), i64::from(a.exponent())),
                raw(*a)
            );
            checks += 1;
            same(
                iou_abi::to_number(raw(*a), tag).map(number),
                Ok(NumberParts::from(*a)),
            );
            checks += 1;
            same_iou(
                iou_abi::of_number(wire(NumberParts::from(*a)), tag),
                IOUAmount::from_number(NumberParts::from(*a)),
            );
            checks += 1;
            same_raw(
                iou_abi::from_number(wire(NumberParts::from(*a)), tag),
                raw_iou_parts_from_number(NumberParts::from(*a)),
            );
            checks += 1;
            same(iou_abi::neg(raw(*a), tag).map(rust), Ok(-*a));
            checks += 1;
        }
        for pair in values.windows(2).chain(values.windows(1)) {
            let (a, b) = (pair[0], pair[pair.len() - 1]);
            for (relation, expected) in [(a == b), (a != b), (a < b), (a <= b), (a > b), (a >= b)]
                .into_iter()
                .enumerate()
            {
                assert_eq!(
                    iou_abi::compare(relation as u8, raw(a), raw(b), tag),
                    Ok(expected)
                );
                checks += 1;
            }
            same(
                iou_abi::binary(0, raw(a), raw(b), tag).map(rust),
                a.checked_add(b),
            );
            same(
                iou_abi::binary(1, raw(a), raw(b), tag).map(rust),
                a.checked_sub(b),
            );
            checks += 2;
        }
        for a in &values {
            for &(n, d, up) in &[
                (0, 1, false),
                (1, 3, false),
                (1, 3, true),
                (7, 13, false),
                (u32::MAX, 1, true),
                (1, u32::MAX, true),
                (1, 0, false),
            ] {
                same(
                    iou_abi::mul_ratio(raw(*a), n, d, up, tag).map(rust),
                    mul_ratio(*a, n, d, up),
                );
                checks += 1;
            }
        }
    }
    set_rounding_mode(RoundingMode::ToNearest);
    checks
}
