//! Lean-compatible Vault `LWAB` route dispatcher.

#[path = "lwab_primitive.rs"]
mod primitive;
#[path = "lwab_types.rs"]
mod types;
#[path = "lwab_validation.rs"]
mod validation;
pub use primitive::{DecodeError, MAGIC, VERSION};
pub use types::{Amount, NumericType, Vault};

use basics::number::NumberParts;
use primitive::{Reader, decode_error_response, payload, response};
use types::{
    amount, boolean, number, read_amount, read_number, read_numeric_type, read_option_number,
    read_vault, vault, zero_amount, zero_number,
};
use validation::lawful;

const TER_SUCCESS: u8 = 0;
const TER_HAS_OBLIGATIONS: u8 = 16;
const TER_LIMIT_EXCEEDED: u8 = 38;
#[path = "lwab_operations.rs"]
mod operations;
#[path = "lwab_operations_admin.rs"]
mod operations_admin;
#[path = "lwab_transition.rs"]
mod transition;
#[path = "lwab_transition_admin.rs"]
mod transition_admin;
#[path = "lwab_transition_deposit.rs"]
mod transition_deposit;

pub fn encode_build_request(route: u8, value: Vault) -> Result<Vec<u8>, DecodeError> {
    if route != 1 && route != 2 {
        return Err(DecodeError::OutOfRange { offset: 0 });
    }
    let mut body = Vec::new();
    number(&mut body, value.total)?;
    number(&mut body, value.available)?;
    types::option_number(&mut body, value.maximum)?;
    types::numeric_type(&mut body, value.numeric_type);
    body.push(value.scale);
    number(&mut body, value.shares)?;
    number(&mut body, value.loss)?;
    Ok(response(route, body))
}

/// Encodes Lean's `AmountRequest` for routes 3, 8, and 9.
pub fn encode_amount_request(
    route: u8,
    value: Vault,
    request: Amount,
) -> Result<Vec<u8>, DecodeError> {
    if !matches!(route, 3 | 8 | 9) {
        return Err(DecodeError::OutOfRange { offset: 0 });
    }
    let mut body = Vec::new();
    vault(&mut body, value)?;
    amount(&mut body, request)?;
    Ok(response(route, body))
}
/// Encodes Lean's `DonationRequest` (route 4).
pub fn encode_deposit_request(
    value: Vault,
    request: Amount,
    donation: bool,
) -> Result<Vec<u8>, DecodeError> {
    let mut body = Vec::new();
    vault(&mut body, value)?;
    amount(&mut body, request)?;
    body.push(donation as u8);
    Ok(response(4, body))
}
/// Encodes Lean's `WithdrawRequest` (routes 5 and 6).
pub fn encode_withdraw_request(
    route: u8,
    value: Vault,
    by_shares: bool,
    request: Amount,
    waive: bool,
) -> Result<Vec<u8>, DecodeError> {
    if !matches!(route, 5 | 6) {
        return Err(DecodeError::OutOfRange { offset: 0 });
    }
    let mut body = Vec::new();
    vault(&mut body, value)?;
    body.push(by_shares as u8);
    amount(&mut body, request)?;
    body.push(waive as u8);
    Ok(response(route, body))
}
/// Encodes Lean's `ClawbackRequest` (route 7).
pub fn encode_clawback_request(
    value: Vault,
    assets: Amount,
    shares: Amount,
) -> Result<Vec<u8>, DecodeError> {
    let mut body = Vec::new();
    vault(&mut body, value)?;
    amount(&mut body, assets)?;
    amount(&mut body, shares)?;
    Ok(response(7, body))
}
/// Encodes a complete Vault-only request (routes 10 and 11).
pub fn encode_vault_only_request(route: u8, value: Vault) -> Result<Vec<u8>, DecodeError> {
    if !matches!(route, 10 | 11) {
        return Err(DecodeError::OutOfRange { offset: 0 });
    }
    let mut body = Vec::new();
    vault(&mut body, value)?;
    Ok(response(route, body))
}
/// Encodes Lean's `SetRequest` (route 12).
pub fn encode_set_request(value: Vault, maximum: NumberParts) -> Result<Vec<u8>, DecodeError> {
    let mut body = Vec::new();
    vault(&mut body, value)?;
    number(&mut body, maximum)?;
    Ok(response(12, body))
}
/// Dispatches a request for `route` exactly as the corresponding Lean export:
/// request tags are `1..=12` and response tags are `129..=140`.
pub fn dispatch_route(route: u8, input: &[u8]) -> Vec<u8> {
    let body = match payload(route, input) {
        Ok(body) => body,
        Err(error) => return decode_error_response(route, error),
    };
    let mut reader = Reader::new(body);
    let result = match route {
        1 => operations_admin::build_raw(&mut reader),
        2 => operations_admin::build_terminal(&mut reader),
        3 => operations::round_deposit(&mut reader),
        4 => operations::deposit(&mut reader),
        5 => operations::quote_withdraw(&mut reader),
        6 => operations::withdraw(&mut reader),
        7 => operations_admin::clawback(&mut reader),
        8 => operations_admin::burn_raw(&mut reader),
        9 => operations_admin::burn_terminal(&mut reader),
        10 => operations_admin::can_burn(&mut reader),
        11 => operations_admin::can_delete(&mut reader),
        12 => operations_admin::can_set(&mut reader),
        actual => {
            return decode_error_response(
                route,
                DecodeError::BadTag {
                    expected: 1,
                    actual,
                },
            );
        }
    };
    match result {
        Ok(payload) => response(route + 128, [vec![0], payload].concat()),
        Err(error) => decode_error_response(route, error),
    }
}
