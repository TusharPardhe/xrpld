use super::{
    lwab_primitive::{Reader, WireError, read_envelope},
    lwab_records as r,
    lwab_types::*,
};
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Response<T> {
    Ok(T),
    DecodeError(u8),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lifecycle<T> {
    Value(T),
    RejectedTer(u8),
    ModelError(u8),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CoverResult {
    pub status: u8,
    pub amount: STAmount,
    pub broker: LoanBroker,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Payload {
    State(Lifecycle<LendingState>),
    LoanVault(Lifecycle<LoanVault>),
    BrokerVault(Lifecycle<BrokerVault>),
    Vault(Lifecycle<Vault>),
    Broker(LoanBroker),
    Cover(Result<CoverResult, u8>),
    Ter(Result<u8, u8>),
}
fn stamount(r: &mut Reader) -> Result<STAmount, WireError> {
    Ok(STAmount {
        numeric_type: r.numeric_type()?,
        mantissa: r.u64()?,
        exponent: r.int()?,
        negative: r.boolean()?,
    })
}
fn lifecycle<T>(
    r: &mut Reader,
    read: impl FnOnce(&mut Reader) -> Result<T, WireError>,
) -> Result<Lifecycle<T>, WireError> {
    match r.u8()? {
        0 => match r.u8()? {
            0 => Ok(Lifecycle::Value(read(r)?)),
            1 => Ok(Lifecycle::RejectedTer(r.u8()?)),
            x => Err(WireError::BadTag(0, x)),
        },
        1 => Ok(Lifecycle::ModelError(r.u8()?)),
        x => Err(WireError::BadTag(0, x)),
    }
}
fn decode(operation: u8, input: &[u8]) -> Result<Response<Payload>, WireError> {
    let payload = read_envelope(
        operation.checked_add(128).ok_or(WireError::OutOfRange(0))?,
        input,
    )?;
    let mut r0 = Reader::new(payload);
    let outer = r0.u8()?;
    if outer == 1 {
        return Ok(Response::DecodeError(r0.u8()?));
    }
    if outer != 0 {
        return Err(WireError::BadTag(0, outer));
    };
    let value = match operation {
        1 | 2 | 3 | 6 | 7 | 8 | 17 | 18 | 19 | 22 | 23 | 24 => {
            Payload::State(lifecycle(&mut r0, r::read_state)?)
        }
        4 | 20 => Payload::LoanVault(lifecycle(&mut r0, r::read_loan_vault)?),
        5 | 11 | 21 | 27 => Payload::BrokerVault(lifecycle(&mut r0, r::read_broker_vault)?),
        9 | 10 | 25 | 26 => Payload::Vault(lifecycle(&mut r0, r::read_vault)?),
        12 | 13 => Payload::Broker(r::read_broker(&mut r0)?),
        14 => Payload::Ter(match r0.u8()? {
            0 => Ok(r0.u8()?),
            1 => Err(r0.u8()?),
            x => return Err(WireError::BadTag(0, x)),
        }),
        15 | 16 => Payload::Cover(match r0.u8()? {
            0 => Ok(CoverResult {
                status: r0.u8()?,
                amount: stamount(&mut r0)?,
                broker: r::read_broker(&mut r0)?,
            }),
            1 => Err(r0.u8()?),
            x => return Err(WireError::BadTag(0, x)),
        }),
        _ => return Err(WireError::OutOfRange(0)),
    };
    r0.done()?;
    Ok(Response::Ok(value))
}
pub fn decode_response(operation: u8, input: &[u8]) -> Result<Response<Payload>, WireError> {
    if !(1..=27).contains(&operation) {
        return Err(WireError::OutOfRange(0));
    }
    decode(operation, input)
}
