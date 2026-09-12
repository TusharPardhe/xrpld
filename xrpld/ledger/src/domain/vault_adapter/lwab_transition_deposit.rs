//! Lossless LWAB rounding and deposit transition kernels.

use super::transition::{self, OVERFLOW, TER_NO_PERMISSION, TER_PRECISION_LOSS};

const TER_LOCKED: u8 = 29;
const TER_LIMIT_EXCEEDED: u8 = 38;
use super::{Amount, Vault, zero_amount, zero_number};

pub(super) fn rounded_deposit(vault: Vault, amount: Amount) -> Result<Result<Amount, u8>, u8> {
    let amount_number = transition::amount_number(amount)?;
    if amount_number == zero_number() {
        return Ok(Err(TER_PRECISION_LOSS));
    }
    if matches!(vault.numeric_type, super::NumericType::Integral { .. }) {
        return Ok(Ok(amount));
    }
    let post = transition::math(|| vault.total.try_add(amount_number))?;
    if amount_number.exponent < post.exponent {
        let digits = (post.exponent - amount_number.exponent) as u32;
        let divisor = 10_u64.checked_pow(digits).ok_or(OVERFLOW)?;
        let mantissa = amount_number.mantissa / divisor * divisor;
        return if mantissa == 0 {
            Ok(Err(TER_PRECISION_LOSS))
        } else {
            Ok(Ok(Amount { mantissa, ..amount }))
        };
    }
    Ok(Ok(amount))
}

pub(super) fn deposit(
    vault: Vault,
    amount: Amount,
    donation: bool,
) -> Result<(Option<u8>, Vault, Amount, Amount), u8> {
    let rounded = match rounded_deposit(vault, amount)? {
        Ok(value) => value,
        Err(ter) => return rejected(vault, ter),
    };
    if donation && vault.shares == zero_number() {
        return rejected(vault, TER_NO_PERMISSION);
    }
    if vault.total == zero_number() && vault.shares != zero_number() && !donation {
        return rejected(vault, TER_LOCKED);
    }
    let deposited = transition::amount_number(rounded)?;
    let shares = if donation {
        zero_number()
    } else if vault.total == zero_number() {
        deposited
    } else {
        transition::math(|| {
            vault
                .shares
                .try_mul(deposited)
                .and_then(|x| x.try_div(vault.total))
        })?
    };
    let issued = transition::amount_from_number(transition::int64(), shares)?;
    if !donation && issued.mantissa == 0 {
        return rejected(vault, TER_PRECISION_LOSS);
    }
    let total = transition::math(|| vault.total.try_add(deposited))?;
    if vault.maximum.is_some_and(|maximum| total > maximum) {
        return rejected(vault, TER_LIMIT_EXCEEDED);
    }
    let next = Vault {
        total,
        available: transition::math(|| vault.available.try_add(deposited))?,
        shares: transition::math(|| vault.shares.try_add(shares))?,
        ..vault
    };
    Ok((None, next, rounded, issued))
}

fn rejected(vault: Vault, ter: u8) -> Result<(Option<u8>, Vault, Amount, Amount), u8> {
    Ok((
        Some(ter),
        vault,
        zero_amount(vault.numeric_type),
        zero_amount(transition::int64()),
    ))
}
