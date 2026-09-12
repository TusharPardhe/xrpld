//! Full LWAB clawback, raw/terminal burn, and burn-decision transition kernels.

use super::transition::{self, NOT_LAWFUL, TER_NO_PERMISSION, TER_PRECISION_LOSS};
use super::{Amount, NumericType, Vault, zero_amount, zero_number};
use basics::number::MantissaScale;

const TER_INTERNAL: u8 = 24;

pub(super) fn clawback(
    vault: Vault,
    assets: Amount,
    holder_shares: Amount,
) -> Result<(Option<u8>, Vault, Amount, Amount), u8> {
    if assets.negative {
        return rejected(vault, TER_INTERNAL);
    }
    let shares = if assets.mantissa == 0 {
        transition::amount_number(holder_shares)?
    } else {
        assets_to_shares(vault, assets)?
    };
    let mut recovered = transition::shares_to_assets(
        vault,
        transition::amount_from_number(transition::int64(), shares)?,
        false,
    )?;
    if transition::amount_number(recovered)? > vault.available {
        recovered = transition::amount_from_number(vault.numeric_type, vault.available)?;
        let clamped_shares = assets_to_shares(vault, recovered)?;
        recovered = transition::shares_to_assets(
            vault,
            transition::amount_from_number(transition::int64(), clamped_shares)?,
            false,
        )?;
        if transition::amount_number(recovered)? > vault.available {
            return rejected(vault, TER_INTERNAL);
        }
        return commit_clawback(vault, recovered, clamped_shares);
    }
    commit_clawback(vault, recovered, shares)
}

fn assets_to_shares(vault: Vault, assets: Amount) -> Result<basics::number::NumberParts, u8> {
    let nav = transition::math(|| vault.total.try_sub(vault.loss))?;
    if nav == zero_number() {
        return Ok(zero_number());
    }
    let assets = transition::amount_number(assets)?;
    let shares = transition::math(|| vault.shares.try_mul(assets).and_then(|x| x.try_div(nav)))?;
    Ok(shares.truncate(MantissaScale::Large))
}

fn commit_clawback(
    vault: Vault,
    recovered: Amount,
    shares: basics::number::NumberParts,
) -> Result<(Option<u8>, Vault, Amount, Amount), u8> {
    let recovered_number = transition::amount_number(recovered)?;
    if shares == zero_number() || recovered_number == zero_number() {
        return rejected(vault, TER_PRECISION_LOSS);
    }
    let total = transition::math(|| vault.total.try_sub(recovered_number))?;
    let next = Vault {
        total,
        available: transition::math(|| vault.available.try_sub(recovered_number))?,
        shares: transition::math(|| vault.shares.try_sub(shares))?,
        ..vault
    };
    if !super::validation::lawful(next) {
        return Err(NOT_LAWFUL);
    }
    Ok((
        None,
        associate_terminal(next)?,
        recovered,
        transition::amount_from_number(transition::int64(), shares)?,
    ))
}

pub(super) fn burn_raw(vault: Vault, shares: Amount) -> Result<Vault, u8> {
    let destroyed = transition::amount_number(shares)?;
    let next = Vault {
        shares: transition::math(|| vault.shares.try_sub(destroyed))?,
        ..vault
    };
    if super::validation::lawful(next) {
        Ok(next)
    } else {
        Err(NOT_LAWFUL)
    }
}

pub(super) fn burn_terminal(vault: Vault, shares: Amount) -> Result<Vault, u8> {
    associate_terminal(burn_raw(vault, shares)?)
}

pub(super) fn can_burn_shares(vault: Vault) -> Result<Amount, u8> {
    if vault.shares == zero_number()
        || vault.total != zero_number()
        || vault.available != zero_number()
    {
        return Err(TER_NO_PERMISSION);
    }
    transition::amount_from_number(transition::int64(), vault.shares)
}

pub(super) fn associate_terminal(vault: Vault) -> Result<Vault, u8> {
    let associate = |value| {
        let associated = transition::amount_from_number(vault.numeric_type, value)?;
        transition::amount_number(associated)
    };
    let next = Vault {
        total: associate(vault.total)?,
        available: associate(vault.available)?,
        reserved: associate(vault.reserved)?,
        maximum: vault.maximum.map(associate).transpose()?,
        loss: associate(vault.loss)?,
        ..vault
    };
    if super::validation::lawful(next) {
        Ok(next)
    } else {
        Err(NOT_LAWFUL)
    }
}

fn rejected(vault: Vault, ter: u8) -> Result<(Option<u8>, Vault, Amount, Amount), u8> {
    Ok((
        Some(ter),
        vault,
        zero_amount(vault.numeric_type),
        zero_amount(NumericType::Integral {
            maximum: 9_223_372_036_854_775_807,
            offset: 18,
            sqrt: 3_037_000_499,
            shift: 2_147_483_648,
        }),
    ))
}
