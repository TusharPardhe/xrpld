//! Rounding, deposit, quote, and withdrawal LWAB route bodies.

use super::transition;
use super::transition_deposit;
use super::*;

pub(super) fn round_deposit(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    let vault_value = read_vault(r)?;
    let request = read_amount(r)?;
    r.done()?;
    let mut out = vec![0];
    match transition_deposit::rounded_deposit(vault_value, request) {
        Ok(Ok(amount_value)) => {
            out.push(0);
            amount(&mut out, amount_value)?;
        }
        Ok(Err(ter)) => out.extend([1, ter]),
        Err(error) => out.extend([1, error]),
    }
    Ok(out)
}

pub(super) fn deposit(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    let vault_value = read_vault(r)?;
    let request = read_amount(r)?;
    let donation = boolean(r)?;
    r.done()?;
    let mut out = Vec::new();
    match transition_deposit::deposit(vault_value, request, donation) {
        Ok((ter, next, deposited, shares)) => {
            out.push(0);
            option_ter(&mut out, ter);
            vault(&mut out, next)?;
            amount(&mut out, deposited)?;
            amount(&mut out, shares)?;
        }
        Err(error) => out.extend([1, error]),
    }
    Ok(out)
}

fn read_withdraw_amount(r: &mut Reader<'_>) -> Result<(bool, Amount), DecodeError> {
    let tag = r.u8()?;
    let amount = read_amount(r)?;
    match tag {
        0 => Ok((false, amount)),
        1 => Ok((true, amount)),
        actual => Err(DecodeError::BadTag {
            expected: 0,
            actual,
        }),
    }
}

pub(super) fn quote_withdraw(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    let vault_value = read_vault(r)?;
    let (_, request) = read_withdraw_amount(r)?;
    let waive = boolean(r)?;
    r.done()?;
    let mut out = Vec::new();
    match transition::shares_to_assets(vault_value, request, waive) {
        Ok(value) => {
            out.push(0);
            amount(&mut out, value)?;
        }
        Err(error) => out.extend([1, error]),
    }
    Ok(out)
}

pub(super) fn withdraw(r: &mut Reader<'_>) -> Result<Vec<u8>, DecodeError> {
    let vault_value = read_vault(r)?;
    let (by_shares, request) = read_withdraw_amount(r)?;
    let waive = boolean(r)?;
    r.done()?;
    let mut out = Vec::new();
    match transition::withdraw(vault_value, by_shares, request, waive) {
        Ok((ter, next, assets, shares)) => {
            out.push(0);
            option_ter(&mut out, ter);
            vault(&mut out, next)?;
            amount(&mut out, assets)?;
            amount(&mut out, shares)?;
        }
        Err(error) => out.extend([1, error]),
    }
    Ok(out)
}

fn option_ter(out: &mut Vec<u8>, value: Option<u8>) {
    match value {
        Some(ter) => out.extend([1, ter]),
        None => out.push(0),
    }
}
