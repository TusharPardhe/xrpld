//! Exact LWAB broker-set and broker-cover routes 12 through 16.
use super::{
    lwab_broker_math as math,
    lwab_primitive::{self as p, Reader, WireError},
    lwab_records as records,
    lwab_types::*,
};
const INTERNAL: u8 = 1;

pub(super) fn dispatch(input: &[u8], route: u8) -> Vec<u8> {
    let result = p::read_envelope(route, input).and_then(|body| apply(route, body));
    match result {
        Ok(payload) => super::finish(route, Ok(payload)),
        Err(error) => super::finish(route, Err(error)),
    }
}
fn option_number(r: &mut Reader<'_>) -> Result<Option<Number>, WireError> {
    let offset = r.position();
    match r.u8()? {
        0 => Ok(None),
        1 => Ok(Some(r.number()?)),
        actual => Err(WireError::BadOption { offset, actual }),
    }
}
fn amount(r: &mut Reader<'_>) -> Result<STAmount, WireError> {
    Ok(STAmount {
        numeric_type: r.numeric_type()?,
        mantissa: r.u64()?,
        exponent: r.int()?,
        negative: r.boolean()?,
    })
}
fn read_create(r: &mut Reader<'_>) -> Result<BrokerCreateRequest, WireError> {
    Ok(BrokerCreateRequest {
        identity: records::bi(r)?,
        debt_maximum: option_number(r)?,
        management_fee_rate: option_u16(r)?,
        cover_rate_minimum: option_u32(r)?,
        cover_rate_liquidation: option_u32(r)?,
    })
}
fn option_u16(r: &mut Reader<'_>) -> Result<Option<u16>, WireError> {
    let offset = r.position();
    match r.u8()? {
        0 => Ok(None),
        1 => Ok(Some(r.u16()?)),
        actual => Err(WireError::BadOption { offset, actual }),
    }
}
fn option_u32(r: &mut Reader<'_>) -> Result<Option<u32>, WireError> {
    let offset = r.position();
    match r.u8()? {
        0 => Ok(None),
        1 => Ok(Some(r.u32()?)),
        actual => Err(WireError::BadOption { offset, actual }),
    }
}
fn apply(route: u8, body: &[u8]) -> Result<Vec<u8>, WireError> {
    let mut r = Reader::new(body);
    let payload = match route {
        12 => broker_create(read_create(&mut r)?),
        13 => {
            let broker = records::read_broker(&mut r)?;
            broker_update(broker, option_number(&mut r)?)
        }
        14 => {
            let request = CoverValidateRequest {
                numeric_type: r.numeric_type()?,
                cover_available: r.number()?,
                amount: amount(&mut r)?,
            };
            validate(request)
        }
        15 | 16 => {
            let request = CoverRequest {
                broker: records::read_broker(&mut r)?,
                numeric_type: r.numeric_type()?,
                amount: amount(&mut r)?,
            };
            cover(request, route == 15)
        }
        _ => return Err(WireError::OutOfRange(0)),
    };
    r.done()?;
    Ok(payload)
}
fn broker_only(broker: LoanBroker) -> Vec<u8> {
    let mut out = Vec::new();
    records::broker(&mut out, broker).expect("decoded canonical broker");
    out
}
fn broker_create(x: BrokerCreateRequest) -> Vec<u8> {
    broker_only(LoanBroker {
        identity: x.identity,
        management_fee_rate: x.management_fee_rate.unwrap_or(0),
        cover_rate_minimum: x.cover_rate_minimum.unwrap_or(0),
        cover_rate_liquidation: x.cover_rate_liquidation.unwrap_or(0),
        debt_total: Number::ZERO,
        debt_maximum: x.debt_maximum.unwrap_or(Number::ZERO),
        cover_available: Number::ZERO,
        loan_count: 0,
    })
}
fn broker_update(mut broker: LoanBroker, debt_maximum: Option<Number>) -> Vec<u8> {
    if let Some(value) = debt_maximum {
        broker.debt_maximum = value;
    }
    broker_only(broker)
}
fn validate(x: CoverValidateRequest) -> Vec<u8> {
    let ter = math::can_apply(x.numeric_type, x.cover_available, x.amount);
    match ter {
        Ok(value) => vec![0, value],
        Err(error) => vec![1, error],
    }
}
fn cover(x: CoverRequest, credit: bool) -> Vec<u8> {
    let rounded = match math::rounded(x.numeric_type, x.broker.cover_available, x.amount) {
        Ok(value) if value.mantissa != 0 => value,
        Ok(_) => return cover_result(INTERNAL, math::zero(x.numeric_type), x.broker),
        Err(error) => return vec![1, error],
    };
    let magnitude = match math::number(rounded, math::NEAREST) {
        Ok(value) => value,
        Err(error) => return vec![1, error],
    };
    let movement = if credit {
        magnitude
    } else {
        math::negative(magnitude)
    };
    let cover_available = match math::add(x.broker.cover_available, movement) {
        Ok(value) => value,
        Err(error) => return vec![1, error],
    };
    let mut broker = x.broker;
    broker.cover_available = cover_available;
    cover_result(0, rounded, broker)
}
fn cover_result(status: u8, amount: STAmount, broker: LoanBroker) -> Vec<u8> {
    let mut out = vec![0, status];
    p::stamount(&mut out, amount).expect("cover amount is lossless wire data");
    records::broker(&mut out, broker).expect("broker remains canonical");
    out
}
