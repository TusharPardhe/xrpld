//! Exact arithmetic kernels used only by Lending raw-create LWAB.

use super::lwab_types::{Number, NumericType, Vault};
use basics::number::{MantissaScale, NumberParts, NumberRoundModeGuard, RoundingMode, power};

pub(super) const TER_INTERNAL: u8 = 1;
pub(super) const TER_INSUFFICIENT_FUNDS: u8 = 22;
pub(super) const TER_LIMIT_EXCEEDED: u8 = 38;
pub(super) const TER_PRECISION_LOSS: u8 = 39;
pub(super) const ERROR_NOT_LAWFUL: u8 = 8;

pub(super) fn raw(x: Number) -> Result<NumberParts, u8> {
    let exponent = i32::try_from(x.exponent).map_err(|_| TER_INTERNAL)?;
    let value = NumberParts::unchecked(x.negative, x.mantissa, exponent);
    value
        .is_normalized(MantissaScale::Large)
        .then_some(value)
        .ok_or(TER_INTERNAL)
}
pub(super) fn wire(x: NumberParts) -> Number {
    Number {
        negative: x.negative,
        mantissa: x.mantissa,
        exponent: i64::from(x.exponent),
    }
}
pub(super) fn nearest<T>(
    run: impl FnOnce() -> Result<T, basics::number::NumberArithmeticError>,
) -> Result<T, u8> {
    let _mode = NumberRoundModeGuard::new(RoundingMode::ToNearest);
    run().map_err(|_| TER_INTERNAL)
}
fn grid(value: NumberParts, scale: i32, mode: RoundingMode) -> Result<NumberParts, u8> {
    if value.mantissa == 0 || value.exponent >= scale {
        return Ok(value);
    }
    let delta = scale.checked_sub(value.exponent).ok_or(TER_INTERNAL)?;
    let (mut mantissa, nonzero) = if delta >= 20 {
        (0_u64, true)
    } else {
        let divisor = 10_u64.pow(delta as u32);
        (value.mantissa / divisor, value.mantissa % divisor != 0)
    };
    let increment = match mode {
        RoundingMode::ToNearest if delta < 20 => {
            value.mantissa % 10_u64.pow(delta as u32) >= 5 * 10_u64.pow(delta as u32 - 1)
        }
        RoundingMode::ToNearest => false,
        RoundingMode::Upward => !value.negative && nonzero,
        RoundingMode::Downward => value.negative && nonzero,
        RoundingMode::TowardsZero => false,
    };
    mantissa = mantissa
        .checked_add(u64::from(increment))
        .ok_or(TER_INTERNAL)?;
    NumberParts::unchecked(value.negative && mantissa != 0, mantissa, scale)
        .try_normalize_exact(MantissaScale::Large)
        .map_err(|_| TER_INTERNAL)
}
fn fractional(value: NumberParts, scale: i32, mode: RoundingMode) -> Result<NumberParts, u8> {
    if value.mantissa == 0 {
        return Ok(value);
    }
    let digits = value.mantissa.ilog10() as i32 + 1;
    let value = if digits > 16 {
        grid(value, value.exponent + digits - 16, RoundingMode::ToNearest)?
    } else {
        value
    };
    grid(value, scale, mode)
}
fn integral(value: NumberParts, maximum: u64, mode: RoundingMode) -> Result<NumberParts, u8> {
    let rounded = grid(value, 0, mode)?;
    if rounded.negative || rounded.exponent != 0 || rounded.mantissa > maximum {
        return Err(TER_INTERNAL);
    }
    Ok(rounded)
}
pub(super) fn round(
    nt: NumericType,
    value: NumberParts,
    mode: RoundingMode,
    scale: i32,
) -> Result<NumberParts, u8> {
    match nt {
        NumericType::Fractional => fractional(value, scale, mode),
        NumericType::Integral { maximum, .. } => integral(value, maximum, mode),
    }
}
pub(super) fn exponent(nt: NumericType, value: NumberParts) -> Result<i32, u8> {
    match nt {
        NumericType::Fractional => {
            if value.mantissa == 0 {
                Ok(-100)
            } else {
                Ok(value.exponent + (value.mantissa.ilog10() as i32 + 1 - 16).max(0))
            }
        }
        NumericType::Integral { .. } => Ok(0),
    }
}
pub(super) fn tenth_bips(
    value: NumberParts,
    rate: u32,
    mode: RoundingMode,
) -> Result<NumberParts, u8> {
    let rate = NumberParts::from_i64(i64::from(rate));
    let hundred_thousand = NumberParts::from_i64(100_000);
    let _mode = NumberRoundModeGuard::new(mode);
    value
        .try_mul(rate)
        .and_then(|x| x.try_div(hundred_thousand))
        .map_err(|_| TER_INTERNAL)
}
pub(super) fn periodic_rate(interest: u32, interval: u32) -> Result<NumberParts, u8> {
    let prorated = tenth_bips(
        NumberParts::from_i64(i64::from(interval)),
        interest,
        RoundingMode::ToNearest,
    )?;
    nearest(|| prorated.try_div(NumberParts::from_i64(31_536_000)))
}

include!("lwab_create_math_amortization.rs");
include!("lwab_create_math_lawful.rs");
