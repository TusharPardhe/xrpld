//! Exact terminal LWAB create routes (17--19): raw create, then one association.

use super::{
    Lifecycle, Payload, Response, lwab_create_math as math,
    lwab_primitive::{self as p},
    lwab_records as records,
    lwab_types::{LendingState, Number, NumericType, Vault},
};
use basics::number::NumberParts;

const OVERFLOW: u8 = 0;
const OUT_OF_RANGE: u8 = 2;
const NOT_LAWFUL: u8 = 8;

pub(super) fn dispatch(input: &[u8], raw_route: u8, route: u8) -> Vec<u8> {
    if let Err(error) = p::read_envelope(route, input) {
        return super::finish(route, Err(error));
    }
    let mut raw_input = input.to_vec();
    raw_input[5] = raw_route;
    let mut raw = super::create::dispatch(&raw_input, mode(raw_route));
    let payload = match super::decode_response(raw_route, &raw).expect("raw create response") {
        Response::DecodeError(_) => {
            raw[5] = route.wrapping_add(128);
            return raw;
        }
        Response::Ok(Payload::State(Lifecycle::Value(state))) => match associate(state.vault) {
            Ok(vault) => {
                let mut value = vec![0, 0];
                records::state(&mut value, LendingState { vault, ..state })
                    .expect("associated state is canonical");
                value
            }
            Err(error) => vec![1, error],
        },
        Response::Ok(Payload::State(Lifecycle::RejectedTer(_)))
        | Response::Ok(Payload::State(Lifecycle::ModelError(_))) => raw[11..].to_vec(),
        _ => unreachable!("raw create response kind"),
    };
    super::finish(route, Ok(payload))
}

fn mode(route: u8) -> super::create::CreateMode {
    match route {
        1 => super::create::CreateMode::RequestPending,
        2 => super::create::CreateMode::Pending,
        3 => super::create::CreateMode::Immediate,
        _ => unreachable!("raw create route"),
    }
}

fn associate_number(numeric_type: NumericType, value: Number) -> Result<Number, u8> {
    let raw = math::raw(value)?;
    match numeric_type {
        NumericType::Fractional if raw.mantissa == 0 || (-99..=80).contains(&raw.exponent) => {
            Ok(math::wire(raw))
        }
        NumericType::Fractional if raw.exponent > 80 => Err(OVERFLOW),
        NumericType::Fractional => Ok(Number::ZERO),
        NumericType::Integral { maximum, .. } => {
            let amount = integral_amount(raw)?;
            if amount > maximum {
                return Err(OUT_OF_RANGE);
            }
            Ok(math::wire(NumberParts::from_i64(if value.negative {
                -(amount as i64)
            } else {
                amount as i64
            })))
        }
    }
}
fn integral_amount(raw: NumberParts) -> Result<u64, u8> {
    if raw.mantissa == 0 {
        return Ok(0);
    }
    if raw.exponent >= 0 {
        return raw
            .mantissa
            .checked_mul(10_u64.checked_pow(raw.exponent as u32).ok_or(OVERFLOW)?)
            .ok_or(OVERFLOW);
    }
    if raw.exponent <= -20 {
        return Ok(0);
    }
    let divisor = 10_u64.pow((-raw.exponent) as u32);
    let quotient = raw.mantissa / divisor;
    Ok(quotient
        + u64::from(
            raw.mantissa % divisor > divisor / 2
                || raw.mantissa % divisor == divisor / 2 && quotient % 2 == 1,
        ))
}
fn associate(vault: Vault) -> Result<Vault, u8> {
    let nt = vault.numeric_type;
    let value = Vault {
        assets_total: associate_number(nt, vault.assets_total)?,
        assets_available: associate_number(nt, vault.assets_available)?,
        assets_reserved: associate_number(nt, vault.assets_reserved)?,
        assets_maximum: vault
            .assets_maximum
            .map(|x| associate_number(nt, x))
            .transpose()?,
        numeric_type: nt,
        scale: vault.scale,
        shares_total: vault.shares_total,
        loss_unrealized: associate_number(nt, vault.loss_unrealized)?,
    };
    math::lawful(value).then_some(value).ok_or(NOT_LAWFUL)
}
