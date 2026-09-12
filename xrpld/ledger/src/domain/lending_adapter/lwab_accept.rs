//! Exact LWAB Loan.accept raw (4) and terminal (20) transitions.

use super::{
    lwab_create_math as math,
    lwab_primitive::{self as p, Reader, WireError},
    lwab_records as records,
    lwab_types::*,
};
use basics::number::{NumberArithmeticError, NumberParts, NumberRoundModeGuard, RoundingMode};

const OVERFLOW: u8 = 0;
const DIV_BY_ZERO: u8 = 1;
const OUT_OF_RANGE: u8 = 2;
const NOT_LAWFUL: u8 = 8;

enum Outcome {
    Value(LoanVault),
    Model(u8),
}

pub(super) fn dispatch(input: &[u8], terminal: bool) -> Vec<u8> {
    let route = if terminal { 20 } else { 4 };
    let request = match p::read_envelope(route, input).and_then(read_request) {
        Ok(value) => value,
        Err(error) => return super::finish(route, Err(error)),
    };
    let payload = match accept(request, terminal) {
        Outcome::Value(value) => {
            let mut payload = vec![0, 0];
            records::loan_vault(&mut payload, value).expect("accept result is canonical");
            payload
        }
        Outcome::Model(error) => vec![1, error],
    };
    super::finish(route, Ok(payload))
}

fn read_request(body: &[u8]) -> Result<LoanVaultRequest, WireError> {
    let mut reader = Reader::new(body);
    let request = LoanVaultRequest {
        loan: records::read_loan(&mut reader)?,
        vault: records::read_vault(&mut reader)?,
    };
    reader.done()?;
    Ok(request)
}

fn arithmetic(error: NumberArithmeticError) -> u8 {
    match error {
        NumberArithmeticError::Overflow => OVERFLOW,
        NumberArithmeticError::DivideByZero => DIV_BY_ZERO,
    }
}

fn subtract(left: Number, right: Number) -> Result<Number, u8> {
    let left = math::raw(left)?;
    let right = math::raw(right)?;
    let _rounding = NumberRoundModeGuard::new(RoundingMode::ToNearest);
    left.try_sub(right).map(math::wire).map_err(arithmetic)
}

/// This is the `STAmount.ofNumber`/`toNumber` asset-association boundary. A
/// valid fractional field must remain inside the modeled IOU exponent range;
/// values that round to a different Number are rejected by Lean as notLawful.
fn integral_amount(value: Number) -> Result<u64, u8> {
    let value = math::raw(value)?;
    if value.mantissa == 0 {
        return Ok(0);
    }
    let (mantissa, exponent) = if value.mantissa > 9_223_372_036_854_775_807 {
        (
            value.mantissa / 10,
            value.exponent.checked_add(1).ok_or(OVERFLOW)?,
        )
    } else {
        (value.mantissa, value.exponent)
    };
    let amount = if exponent >= 0 {
        mantissa
            .checked_mul(10_u64.checked_pow(exponent as u32).ok_or(OVERFLOW)?)
            .ok_or(OVERFLOW)?
    } else if exponent <= -20 {
        0
    } else {
        let divisor = 10_u64.pow((-exponent) as u32);
        let quotient = mantissa / divisor;
        let remainder = mantissa % divisor;
        quotient
            + u64::from(remainder > divisor / 2 || remainder == divisor / 2 && quotient % 2 == 1)
    };
    (amount <= 9_223_372_036_854_775_807)
        .then_some(amount)
        .ok_or(OVERFLOW)
}

fn associate_number(numeric_type: NumericType, value: Number) -> Result<Number, u8> {
    let raw = math::raw(value)?;
    match numeric_type {
        NumericType::Fractional => {
            if raw.mantissa == 0 || (-99..=80).contains(&raw.exponent) {
                Ok(math::wire(raw))
            } else if raw.exponent > 80 {
                Err(OVERFLOW)
            } else {
                Ok(Number::ZERO)
            }
        }
        NumericType::Integral { maximum, .. } => {
            let amount = integral_amount(value)?;
            if amount > maximum {
                return Err(OUT_OF_RANGE);
            }
            let signed = if value.negative {
                -(amount as i64)
            } else {
                amount as i64
            };
            Ok(math::wire(NumberParts::from_i64(signed)))
        }
    }
}

pub(super) fn associate(vault: Vault) -> Result<Vault, u8> {
    let assets_maximum = match vault.assets_maximum {
        Some(value) => Some(associate_number(vault.numeric_type, value)?),
        None => None,
    };
    let associated = Vault {
        assets_total: associate_number(vault.numeric_type, vault.assets_total)?,
        assets_available: associate_number(vault.numeric_type, vault.assets_available)?,
        assets_reserved: associate_number(vault.numeric_type, vault.assets_reserved)?,
        assets_maximum,
        numeric_type: vault.numeric_type,
        scale: vault.scale,
        shares_total: vault.shares_total,
        loss_unrealized: associate_number(vault.numeric_type, vault.loss_unrealized)?,
    };
    math::lawful(associated)
        .then_some(associated)
        .ok_or(NOT_LAWFUL)
}

fn accept(request: LoanVaultRequest, terminal: bool) -> Outcome {
    let reserved = match subtract(
        request.vault.assets_reserved,
        request.loan.principal_outstanding,
    ) {
        Ok(value) => value,
        Err(error) => return Outcome::Model(error),
    };
    let vault = Vault {
        assets_reserved: reserved,
        ..request.vault
    };
    if !math::lawful(vault) {
        return Outcome::Model(NOT_LAWFUL);
    }
    let vault = if terminal {
        match associate(vault) {
            Ok(value) => value,
            Err(error) => return Outcome::Model(error),
        }
    } else {
        vault
    };
    Outcome::Value(LoanVault {
        vault_identity: request.loan.vault_identity,
        loan: Loan {
            pending: false,
            ..request.loan
        },
        vault,
    })
}
