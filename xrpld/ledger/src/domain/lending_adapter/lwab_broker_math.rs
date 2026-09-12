//! Cover-specific Number/STAmount conversions and cover-scale rounding.
use super::{
    lwab_create_math as base,
    lwab_types::{Number, NumericType, STAmount},
};
use basics::number::{
    MantissaScale, NumberArithmeticError, NumberParts, NumberRoundModeGuard, RoundingMode,
};

pub(super) const NEAREST: RoundingMode = RoundingMode::ToNearest;
const OVERFLOW: u8 = 0;
const CANNOT_CONVERT: u8 = 7;
const PRECISION: u8 = 39;

fn error(error: NumberArithmeticError) -> u8 {
    match error {
        NumberArithmeticError::Overflow => OVERFLOW,
        NumberArithmeticError::DivideByZero => 1,
    }
}
fn raw(x: Number) -> Result<NumberParts, u8> {
    base::raw(x).map_err(|_| CANNOT_CONVERT)
}
fn wire(x: NumberParts) -> Number {
    base::wire(x)
}
pub(super) fn add(left: Number, right: NumberParts) -> Result<Number, u8> {
    let _rounding = NumberRoundModeGuard::new(NEAREST);
    raw(left)?.try_add(right).map(wire).map_err(error)
}
pub(super) fn negative(value: NumberParts) -> NumberParts {
    NumberParts::unchecked(
        value.mantissa != 0 && !value.negative,
        value.mantissa,
        value.exponent,
    )
}
fn scale(nt: NumericType, cover: Number) -> Result<i32, u8> {
    let exponent = base::exponent(nt, raw(cover)?).map_err(|_| CANNOT_CONVERT)?;
    match nt {
        NumericType::Fractional if exponent > 80 => Err(OVERFLOW),
        NumericType::Fractional if exponent < -96 => Ok(-100),
        _ => Ok(exponent),
    }
}
fn mode_round(rem: u64, divisor: u64, negative: bool, mode: RoundingMode) -> bool {
    rem != 0
        && match mode {
            RoundingMode::ToNearest => rem >= divisor / 2,
            RoundingMode::Upward => !negative,
            RoundingMode::Downward => negative,
            RoundingMode::TowardsZero => false,
        }
}
fn fractional_number(amount: STAmount, mode: RoundingMode) -> Result<NumberParts, u8> {
    let exponent = i32::try_from(amount.exponent).map_err(|_| CANNOT_CONVERT)?;
    if amount.mantissa == 0 {
        return Ok(NumberParts::zero());
    }
    let mut mantissa = u128::from(amount.mantissa);
    let mut exponent = exponent;
    while mantissa < 1_000_000_000_000_000 {
        mantissa = mantissa.checked_mul(10).ok_or(OVERFLOW)?;
        exponent = exponent.checked_sub(1).ok_or(OVERFLOW)?;
    }
    while mantissa > 9_999_999_999_999_999 {
        let rem = (mantissa % 10) as u64;
        mantissa /= 10;
        if mode_round(rem, 10, amount.negative, mode) {
            mantissa += 1;
        }
        exponent = exponent.checked_add(1).ok_or(OVERFLOW)?;
    }
    if mantissa == 10_000_000_000_000_000 {
        mantissa /= 10;
        exponent = exponent.checked_add(1).ok_or(OVERFLOW)?;
    }
    if exponent > 80 {
        return Err(OVERFLOW);
    }
    if exponent < -96 {
        return Ok(NumberParts::zero());
    }
    let mantissa = u64::try_from(mantissa).map_err(|_| OVERFLOW)?;
    NumberParts::unchecked(amount.negative, mantissa, exponent)
        .try_normalize_exact(MantissaScale::Large)
        .map_err(|_| CANNOT_CONVERT)
}
pub(super) fn number(amount: STAmount, mode: RoundingMode) -> Result<NumberParts, u8> {
    match amount.numeric_type {
        NumericType::Fractional => fractional_number(amount, mode),
        NumericType::Integral { .. } => {
            let signed = if amount.negative {
                (amount.mantissa as i64).wrapping_neg()
            } else {
                amount.mantissa as i64
            };
            NumberParts::try_from_external_parts(signed, 0, MantissaScale::Large)
                .map_err(|_| CANNOT_CONVERT)
        }
    }
}
fn fractional_amount(value: NumberParts, mode: RoundingMode) -> Result<STAmount, u8> {
    if value.mantissa == 0 {
        return Ok(zero(NumericType::Fractional));
    }
    let mut mantissa = value.mantissa;
    let mut exponent = value.exponent;
    let digits = mantissa.ilog10() as i32 + 1;
    let drop = (digits - 16).max(0) as u32;
    if drop != 0 {
        let divisor = 10_u64.pow(drop);
        let rem = mantissa % divisor;
        mantissa /= divisor;
        if mode_round(rem, divisor, value.negative, mode) {
            mantissa = mantissa.checked_add(1).ok_or(OVERFLOW)?;
        }
        exponent = exponent.checked_add(drop as i32).ok_or(OVERFLOW)?;
    }
    if mantissa == 10_000_000_000_000_000 {
        mantissa /= 10;
        exponent = exponent.checked_add(1).ok_or(OVERFLOW)?;
    }
    while mantissa < 1_000_000_000_000_000 {
        mantissa = mantissa.checked_mul(10).ok_or(OVERFLOW)?;
        exponent = exponent.checked_sub(1).ok_or(OVERFLOW)?;
    }
    if exponent > 80 {
        return Err(OVERFLOW);
    }
    if exponent < -96 {
        return Ok(zero(NumericType::Fractional));
    }
    Ok(STAmount {
        numeric_type: NumericType::Fractional,
        mantissa,
        exponent: i64::from(exponent),
        negative: value.negative,
    })
}
fn amount(value: NumberParts, nt: NumericType, mode: RoundingMode) -> Result<STAmount, u8> {
    match nt {
        NumericType::Fractional => fractional_amount(value, mode),
        NumericType::Integral { maximum, .. } => {
            let value = base::round(nt, value, mode, 0).map_err(|_| CANNOT_CONVERT)?;
            if value.mantissa > maximum {
                return Err(OVERFLOW);
            }
            Ok(STAmount {
                numeric_type: nt,
                mantissa: value.mantissa,
                exponent: 0,
                negative: value.negative,
            })
        }
    }
}
pub(super) fn zero(nt: NumericType) -> STAmount {
    STAmount {
        numeric_type: nt,
        mantissa: 0,
        exponent: if matches!(nt, NumericType::Fractional) {
            -100
        } else {
            0
        },
        negative: false,
    }
}
fn round_cover(
    nt: NumericType,
    cover: Number,
    amount0: STAmount,
    mode: RoundingMode,
) -> Result<STAmount, u8> {
    if !matches!(amount0.numeric_type, NumericType::Fractional) || amount0.mantissa == 0 {
        return Ok(amount0);
    }
    let cover_scale = scale(nt, cover)?;
    if amount0.exponent >= i64::from(cover_scale) {
        return Ok(amount0);
    }
    let value = number(amount0, mode)?;
    let rounded =
        base::round(amount0.numeric_type, value, mode, cover_scale).map_err(|_| CANNOT_CONVERT)?;
    amount(rounded, amount0.numeric_type, mode)
}
pub(super) fn can_apply(nt: NumericType, cover: Number, amount0: STAmount) -> Result<u8, u8> {
    if amount0.mantissa == 0 {
        return Ok(PRECISION);
    }
    let rounded = round_cover(nt, cover, amount0, NEAREST)?;
    Ok(if rounded.mantissa == 0 { PRECISION } else { 0 })
}
pub(super) fn rounded(nt: NumericType, cover: Number, amount0: STAmount) -> Result<STAmount, u8> {
    round_cover(nt, cover, amount0, RoundingMode::Downward)
}
