//! Lossless shared conversion and withdrawal transition kernels.

use super::{Amount, NumericType, Vault, zero_amount, zero_number};
use basics::number::{NumberParts, NumberRoundModeGuard, RoundingMode};

pub(super) const OVERFLOW: u8 = 0;
pub(super) const DIV_BY_ZERO: u8 = 1;
pub(super) const NOT_LAWFUL: u8 = 8;
pub(super) const TER_NO_PERMISSION: u8 = 13;
pub(super) const TER_INSUFFICIENT_FUNDS: u8 = 22;
pub(super) const TER_PRECISION_LOSS: u8 = 39;

pub(super) fn amount_number(amount: Amount) -> Result<NumberParts, u8> {
    match amount.numeric_type {
        NumericType::Fractional => {
            if amount.mantissa == 0 {
                Ok(NumberParts::zero())
            } else {
                NumberParts::unchecked(amount.negative, amount.mantissa, amount.exponent as i32)
                    .try_normalize_exact(basics::number::MantissaScale::Large)
                    .map_err(|_| OVERFLOW)
            }
        }
        NumericType::Integral { maximum, .. } => {
            if amount.negative || amount.exponent != 0 || amount.mantissa > maximum {
                return Err(NOT_LAWFUL);
            }
            let value = i64::try_from(amount.mantissa).map_err(|_| NOT_LAWFUL)?;
            NumberParts::try_from_external_parts(value, 0, basics::number::MantissaScale::Large)
                .map_err(|_| OVERFLOW)
        }
    }
}

pub(super) fn amount_from_number(kind: NumericType, value: NumberParts) -> Result<Amount, u8> {
    if value.mantissa == 0 {
        return Ok(zero_amount(kind));
    }
    match kind {
        NumericType::Fractional => fractional_amount(value),
        NumericType::Integral { maximum, .. } => {
            let (mantissa, exponent) = value.external_parts().map_err(|_| OVERFLOW)?;
            let factor = 10_i64
                .checked_pow(exponent.unsigned_abs())
                .ok_or(OVERFLOW)?;
            let signed = if exponent >= 0 {
                mantissa.checked_mul(factor).ok_or(OVERFLOW)?
            } else if mantissa % factor == 0 {
                mantissa / factor
            } else {
                return Err(TER_PRECISION_LOSS);
            };
            let magnitude = signed.unsigned_abs();
            if signed < 0 || magnitude > maximum {
                return Err(NOT_LAWFUL);
            }
            Ok(Amount {
                numeric_type: kind,
                mantissa: magnitude,
                exponent: 0,
                negative: false,
            })
        }
    }
}

fn fractional_amount(value: NumberParts) -> Result<Amount, u8> {
    if value.mantissa == 0 {
        return Ok(zero_amount(NumericType::Fractional));
    }
    let mut mantissa = value.mantissa;
    let mut exponent = value.exponent;
    while mantissa > 9_999_999_999_999_999 {
        mantissa /= 10;
        exponent = exponent.checked_add(1).ok_or(OVERFLOW)?;
    }
    while mantissa < 1_000_000_000_000_000 {
        mantissa = mantissa.checked_mul(10).ok_or(OVERFLOW)?;
        exponent = exponent.checked_sub(1).ok_or(OVERFLOW)?;
    }
    Ok(Amount {
        numeric_type: NumericType::Fractional,
        mantissa,
        exponent: i64::from(exponent),
        negative: value.negative,
    })
}

pub(super) fn math<T>(
    f: impl FnOnce() -> Result<T, basics::number::NumberArithmeticError>,
) -> Result<T, u8> {
    let _round = NumberRoundModeGuard::new(RoundingMode::ToNearest);
    f().map_err(|error| match error {
        basics::number::NumberArithmeticError::Overflow => OVERFLOW,
        basics::number::NumberArithmeticError::DivideByZero => DIV_BY_ZERO,
    })
}

pub(super) fn shares_to_assets(vault: Vault, shares: Amount, waive: bool) -> Result<Amount, u8> {
    let shares = amount_number(shares)?;
    let nav = math(|| {
        vault
            .total
            .try_sub(if waive { zero_number() } else { vault.loss })
    })?;
    if nav == zero_number() {
        return Ok(zero_amount(vault.numeric_type));
    }
    let assets = math(|| nav.try_mul(shares).and_then(|x| x.try_div(vault.shares)))?;
    amount_from_number(vault.numeric_type, assets)
}

pub(super) fn int64() -> NumericType {
    NumericType::Integral {
        maximum: 9_223_372_036_854_775_807,
        offset: 18,
        sqrt: 3_037_000_499,
        shift: 2_147_483_648,
    }
}

pub(super) fn withdraw(
    vault: Vault,
    by_shares: bool,
    amount: Amount,
    waive: bool,
) -> Result<(Option<u8>, Vault, Amount, Amount), u8> {
    let shares = if by_shares {
        amount_number(amount)?
    } else {
        let assets = amount_number(amount)?;
        let nav = math(|| {
            vault
                .total
                .try_sub(if waive { zero_number() } else { vault.loss })
        })?;
        math(|| vault.shares.try_mul(assets).and_then(|x| x.try_div(nav)))?
    };
    if shares == vault.shares {
        return final_withdrawal(vault, shares);
    }
    let assets = shares_to_assets(vault, amount_from_number(int64(), shares)?, waive)?;
    let asset_number = amount_number(assets)?;
    if asset_number == zero_number() {
        return rejected(vault, TER_PRECISION_LOSS);
    }
    if asset_number > vault.available {
        return rejected(vault, TER_INSUFFICIENT_FUNDS);
    }
    let next = Vault {
        total: math(|| vault.total.try_sub(asset_number))?,
        available: math(|| vault.available.try_sub(asset_number))?,
        shares: math(|| vault.shares.try_sub(shares))?,
        ..vault
    };
    Ok((None, next, assets, amount_from_number(int64(), shares)?))
}

fn final_withdrawal(
    vault: Vault,
    shares: NumberParts,
) -> Result<(Option<u8>, Vault, Amount, Amount), u8> {
    if vault.loss != zero_number() {
        return rejected(vault, 24);
    }
    Ok((
        None,
        Vault {
            total: zero_number(),
            available: zero_number(),
            shares: zero_number(),
            ..vault
        },
        amount_from_number(vault.numeric_type, vault.available)?,
        amount_from_number(int64(), shares)?,
    ))
}

fn rejected(vault: Vault, ter: u8) -> Result<(Option<u8>, Vault, Amount, Amount), u8> {
    Ok((
        Some(ter),
        vault,
        zero_amount(vault.numeric_type),
        zero_amount(int64()),
    ))
}
