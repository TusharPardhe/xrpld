//! Lean-compatible Lending LWAB v1 dispatcher for implemented Lending routes.

#[path = "lwab_primitive.rs"]
mod lwab_primitive;
#[path = "lwab_records.rs"]
mod lwab_records;
#[path = "lwab_requests.rs"]
mod lwab_requests;
#[path = "lwab_response.rs"]
mod lwab_response;
#[path = "lwab_types.rs"]
mod lwab_types;

pub use lwab_primitive::{MAGIC, VERSION, WireError};
pub use lwab_requests::{Request, encode_request};
pub use lwab_response::{Lifecycle, Payload, Response, decode_response};
pub use lwab_types::*;

/// Dispatches implemented Lending LWAB routes. Unsupported routes retain the
/// canonical tagged decoder error rather than an invented result.
pub fn dispatch_route(route: u8, input: &[u8]) -> Vec<u8> {
    match route {
        1 => create::dispatch(input, create::CreateMode::RequestPending),
        2 => create::dispatch(input, create::CreateMode::Pending),
        3 => create::dispatch(input, create::CreateMode::Immediate),
        4 => accept::dispatch(input, false),
        5 => delete::dispatch(input, false),
        6 | 7 | 8 => payment::dispatch(input, route, false),
        9 | 10 | 11 => manage::dispatch(input, route, false),
        12 | 13 | 14 | 15 | 16 => broker::dispatch(input, route),
        17 => terminal_create::dispatch(input, 1, 17),
        18 => terminal_create::dispatch(input, 2, 18),
        19 => terminal_create::dispatch(input, 3, 19),
        20 => accept::dispatch(input, true),
        21 => delete::dispatch(input, true),
        22 | 23 | 24 => payment::dispatch(input, route - 16, true),
        25 | 26 | 27 => manage::dispatch(input, route - 16, true),
        _ => finish(route, Err(WireError::OutOfRange(0))),
    }
}

fn finish(route: u8, payload: Result<Vec<u8>, WireError>) -> Vec<u8> {
    let payload = match payload {
        Ok(value) => [vec![0], value].concat(),
        Err(error) => [vec![1], encode_decode_error(error)].concat(),
    };
    lwab_primitive::envelope(route.wrapping_add(128), payload)
}

fn word(out: &mut Vec<u8>, value: usize) {
    out.extend((value as u64).to_le_bytes());
}
fn encode_decode_error(error: WireError) -> Vec<u8> {
    let mut out = Vec::new();
    match error {
        WireError::Truncated {
            offset,
            needed,
            remaining,
        } => {
            out.push(0);
            word(&mut out, offset);
            word(&mut out, needed);
            word(&mut out, remaining);
        }
        WireError::Trailing { offset, remaining } => {
            out.push(1);
            word(&mut out, offset);
            word(&mut out, remaining);
        }
        WireError::BadMagic => out.push(2),
        WireError::BadVersion(actual) => out.extend([3, actual]),
        WireError::BadTag(expected, actual) => out.extend([4, expected, actual]),
        WireError::BadBoolean { offset, actual } => {
            out.push(5);
            word(&mut out, offset);
            out.push(actual);
        }
        WireError::BadOption { offset, actual } => {
            out.push(6);
            word(&mut out, offset);
            out.push(actual);
        }
        WireError::BadLength { offset, declared } => {
            out.push(7);
            word(&mut out, offset);
            word(&mut out, declared);
        }
        WireError::BadNumericType { offset, actual } => {
            out.push(8);
            word(&mut out, offset);
            out.push(actual);
        }
        WireError::OutOfRange(offset) => {
            out.push(9);
            word(&mut out, offset);
        }
        WireError::NonCanonical(offset) => {
            out.push(10);
            word(&mut out, offset);
        }
    }
    out
}

#[path = "lwab_accept.rs"]
mod accept;
#[path = "lwab_broker.rs"]
mod broker;
#[path = "lwab_create.rs"]
mod create;
#[path = "lwab_delete.rs"]
mod delete;
#[path = "lwab_broker_math.rs"]
mod lwab_broker_math;
#[path = "lwab_create_math.rs"]
mod lwab_create_math;
#[path = "lwab_manage_default.rs"]
mod lwab_manage_default;
#[path = "lwab_manage_math.rs"]
mod lwab_manage_math;
#[path = "lwab_manage.rs"]
mod manage;
#[path = "lwab_payment.rs"]
mod payment;
#[path = "lwab_terminal_create.rs"]
mod terminal_create;
