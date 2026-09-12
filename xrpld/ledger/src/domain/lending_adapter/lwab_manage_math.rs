use super::{
    lwab_create_math as math,
    lwab_types::{Number, NumericType, Vault},
};
use basics::number::{NumberArithmeticError, NumberParts, NumberRoundModeGuard, RoundingMode};

pub(super) const OVERFLOW: u8 = 0;
pub(super) const NOT_LAWFUL: u8 = 8;
pub(super) fn raw(x: Number) -> Result<NumberParts, u8> {
    math::raw(x)
}
pub(super) fn wire(x: NumberParts) -> Number {
    math::wire(x)
}
fn arithmetic(error: NumberArithmeticError) -> u8 {
    match error {
        NumberArithmeticError::Overflow => OVERFLOW,
        NumberArithmeticError::DivideByZero => 1,
    }
}
pub(super) fn nearest(
    run: impl FnOnce() -> Result<NumberParts, NumberArithmeticError>,
) -> Result<NumberParts, u8> {
    let _mode = NumberRoundModeGuard::new(RoundingMode::ToNearest);
    run().map_err(arithmetic)
}
pub(super) fn add(left: Number, right: Number) -> Result<NumberParts, u8> {
    let left = raw(left)?;
    let right = raw(right)?;
    nearest(|| left.try_add(right))
}
pub(super) fn sub(left: Number, right: Number) -> Result<NumberParts, u8> {
    let left = raw(left)?;
    let right = raw(right)?;
    nearest(|| left.try_sub(right))
}
pub(super) fn less(left: Number, right: Number) -> Result<bool, u8> {
    Ok(raw(left)? < raw(right)?)
}
pub(super) fn greater(left: Number, right: Number) -> Result<bool, u8> {
    Ok(raw(left)? > raw(right)?)
}
pub(super) fn round(
    nt: NumericType,
    value: NumberParts,
    mode: RoundingMode,
    scale: i32,
) -> Result<NumberParts, u8> {
    math::round(nt, value, mode, scale)
}
pub(super) fn scale(vault: Vault) -> Result<i32, u8> {
    math::exponent(vault.numeric_type, raw(vault.assets_total)?)
}
pub(super) fn adjust(
    nt: NumericType,
    value: Number,
    delta: Number,
    scale: i32,
) -> Result<Number, u8> {
    let rounded = round(nt, add(value, delta)?, RoundingMode::ToNearest, scale)?;
    Ok(if rounded.negative {
        Number::ZERO
    } else {
        wire(rounded)
    })
}
pub(super) fn negative(value: Number) -> Result<Number, u8> {
    let value = raw(value)?;
    Ok(wire(NumberParts::unchecked(
        value.mantissa != 0 && !value.negative,
        value.mantissa,
        value.exponent,
    )))
}
pub(super) fn cover(
    broker_debt: Number,
    minimum: u32,
    liquidation: u32,
    nt: NumericType,
    scale: i32,
    default: Number,
    available: Number,
) -> Result<Number, u8> {
    let minimum = math::tenth_bips(raw(broker_debt)?, minimum, RoundingMode::Upward)?;
    let liquidation = math::tenth_bips(minimum, liquidation, RoundingMode::Upward)?;
    let capped = liquidation.min(raw(default)?);
    let rounded = round(nt, capped, RoundingMode::Upward, scale)?;
    Ok(wire(rounded.min(raw(available)?)))
}
pub(super) fn dust_adjust(available: Number, total: Number) -> Result<Number, u8> {
    let available_raw = raw(available)?;
    let total_raw = raw(total)?;
    if available_raw <= total_raw {
        return Ok(total);
    }
    let overshoot = nearest(|| available_raw.try_sub(total_raw))?;
    Ok(if available_raw.exponent - overshoot.exponent > 13 {
        available
    } else {
        total
    })
}
pub(super) fn lawful(vault: Vault) -> bool {
    math::lawful(vault)
}
