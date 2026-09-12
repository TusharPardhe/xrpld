//! Raw construction, clawback, burn, and Vault decision LWAB route bodies.

use super::transition;
use super::transition_admin;
use super::*;

pub(super) fn build_raw(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    build(r, false)
}

pub(super) fn build_terminal(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    build(r, true)
}

fn build(r: &mut Reader<'_>, terminal: bool) -> Result<Vec<u8>, DecodeError> {
    let value = read_build(r)?;
    r.done()?;
    let mut out = Vec::new();
    match lawful(value)
        .then_some(value)
        .ok_or(transition::NOT_LAWFUL)
        .and_then(|value| {
            if terminal {
                transition_admin::associate_terminal(value)
            } else {
                Ok(value)
            }
        }) {
        Ok(value) => {
            out.push(0);
            vault(&mut out, value)?;
        }
        Err(error) => out.extend([1, error]),
    }
    Ok(out)
}

pub(super) fn clawback(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    let value = read_vault(r)?;
    let assets = read_amount(r)?;
    let holder_shares = read_amount(r)?;
    r.done()?;
    let mut out = Vec::new();
    match transition_admin::clawback(value, assets, holder_shares) {
        Ok((ter, next, recovered, destroyed)) => {
            out.push(0);
            option_ter(&mut out, ter);
            vault(&mut out, next)?;
            amount(&mut out, recovered)?;
            amount(&mut out, destroyed)?;
        }
        Err(error) => out.extend([1, error]),
    }
    Ok(out)
}

pub(super) fn burn_raw(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    burn(r, transition_admin::burn_raw)
}

pub(super) fn burn_terminal(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    burn(r, transition_admin::burn_terminal)
}

fn burn(
    r: &mut Reader<'_>,
    operation: fn(Vault, Amount) -> Result<Vault, u8>,
) -> Result<Vec<u8>, DecodeError> {
    let value = read_vault(r)?;
    let shares = read_amount(r)?;
    r.done()?;
    let mut out = Vec::new();
    match operation(value, shares) {
        Ok(next) => {
            out.push(0);
            vault(&mut out, next)?;
        }
        Err(error) => out.extend([1, error]),
    }
    Ok(out)
}

pub(super) fn can_burn(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    let value = read_vault(r)?;
    r.done()?;
    let mut out = vec![0];
    match transition_admin::can_burn_shares(value) {
        Ok(shares) => {
            out.push(0);
            amount(&mut out, shares)?;
        }
        Err(ter) => out.extend([1, ter]),
    }
    Ok(out)
}

pub(super) fn can_delete(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    let value = read_vault(r)?;
    r.done()?;
    Ok(vec![if value.total == zero_number()
        && value.available == zero_number()
        && value.shares == zero_number()
    {
        TER_SUCCESS
    } else {
        TER_HAS_OBLIGATIONS
    }])
}

pub(super) fn can_set(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    let value = read_vault(r)?;
    let maximum = read_number(r)?;
    r.done()?;
    Ok(vec![
        if maximum == zero_number() || maximum >= value.total {
            TER_SUCCESS
        } else {
            TER_LIMIT_EXCEEDED
        },
    ])
}

fn read_build(r: &mut Reader<'_>) -> Result<Vault, DecodeError> {
    Ok(Vault {
        total: read_number(r)?,
        available: read_number(r)?,
        reserved: zero_number(),
        maximum: read_option_number(r)?,
        numeric_type: read_numeric_type(r)?,
        scale: r.u8()?,
        shares: read_number(r)?,
        loss: read_number(r)?,
    })
}

fn option_ter(out: &mut Vec<u8>, value: Option<u8>) {
    match value {
        Some(ter) => out.extend([1, ter]),
        None => out.push(0),
    }
}
