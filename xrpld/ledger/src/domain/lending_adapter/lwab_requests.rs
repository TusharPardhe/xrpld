//! Canonical request encoders and response decoders for all 27 Lending routes.

use super::{
    lwab_primitive::{self as p, Reader, WireError, read_envelope},
    lwab_records as r,
    lwab_response::Response,
    lwab_types::*,
};
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Request {
    Create(CreateRequest),
    LoanVault(LoanVaultRequest),
    Broker(BrokerRequest),
    Payment(PaymentRequest),
    Amount(AmountRequest),
    Default(DefaultRequest),
    BrokerCreate(BrokerCreateRequest),
    BrokerUpdate(BrokerUpdateRequest),
    Cover(CoverRequest),
    CoverValidate(CoverValidateRequest),
}
fn create(o: &mut Vec<u8>, x: CreateRequest) -> Result<(), WireError> {
    r::vault_identity(o, x.vault_identity);
    loan_identity(o, x.loan_identity);
    r::vault(o, x.vault)?;
    r::broker(o, x.broker)?;
    p::number(o, x.principal)?;
    rates(o, x.rates);
    fees(o, x.fees)?;
    schedule(o, x.schedule);
    p::boolean(o, x.allows_overpayment);
    p::boolean(o, x.pending);
    Ok(())
}
fn loan_identity(o: &mut Vec<u8>, x: LoanIdentity) {
    for v in [
        x.loan_id.0,
        x.broker_id.0,
        x.borrower.0,
        x.counterparty.0,
        x.issue.currency,
        x.issue.issuer.0,
    ] {
        p::u64(o, v)
    }
    p::boolean(o, x.authorization.counterparty_signed);
    p::boolean(o, x.authorization.deposit_authorized);
    p::boolean(o, x.authorization.credential_authorized);
    p::u64(o, x.metadata.transaction_id.0);
    p::u32(o, x.metadata.sequence);
    p::u32(o, x.metadata.ledger_close_time)
}
fn rates(o: &mut Vec<u8>, x: LoanRates) {
    for v in [
        x.interest,
        x.late_interest,
        x.close_interest,
        x.overpayment_interest,
        x.overpayment_fee,
    ] {
        p::u32(o, v)
    }
}
fn fees(o: &mut Vec<u8>, x: LoanFees) -> Result<(), WireError> {
    for v in [x.origination, x.service, x.late_payment, x.close_payment] {
        p::number(o, v)?
    }
    Ok(())
}
fn schedule(o: &mut Vec<u8>, x: LoanSchedule) {
    for v in [
        x.payment_interval,
        x.payment_total,
        x.grace_period,
        x.start_date,
    ] {
        p::u32(o, v)
    }
}
fn broker_request(o: &mut Vec<u8>, x: BrokerRequest) -> Result<(), WireError> {
    r::loan(o, x.loan)?;
    r::vault(o, x.vault)?;
    r::broker(o, x.broker)
}
fn payment_type(o: &mut Vec<u8>, x: PaymentType) {
    p::u8(
        o,
        match x {
            PaymentType::Regular => 0,
            PaymentType::Late => 1,
            PaymentType::Full => 2,
            PaymentType::Overpayment => 3,
        },
    )
}
fn encode_payload(request: Request) -> Result<Vec<u8>, WireError> {
    let mut o = Vec::new();
    match request {
        Request::Create(x) => create(&mut o, x)?,
        Request::LoanVault(x) => {
            r::loan(&mut o, x.loan)?;
            r::vault(&mut o, x.vault)?
        }
        Request::Broker(x) => broker_request(&mut o, x)?,
        Request::Payment(x) => {
            broker_request(&mut o, x.base)?;
            payment_type(&mut o, x.payment_type);
            p::number(&mut o, x.amount)?;
            p::u32(&mut o, x.now)
        }
        Request::Amount(x) => {
            broker_request(&mut o, x.base)?;
            p::number(&mut o, x.amount)?;
            p::u32(&mut o, x.now)
        }
        Request::Default(x) => {
            broker_request(&mut o, x.base)?;
            p::boolean(&mut o, x.impaired)
        }
        Request::BrokerCreate(x) => {
            r::broker_identity(&mut o, x.identity);
            p::option(&mut o, x.debt_maximum, p::number)?;
            p::option(&mut o, x.management_fee_rate, |o, v| {
                p::u16(o, v);
                Ok(())
            })?;
            p::option(&mut o, x.cover_rate_minimum, |o, v| {
                p::u32(o, v);
                Ok(())
            })?;
            p::option(&mut o, x.cover_rate_liquidation, |o, v| {
                p::u32(o, v);
                Ok(())
            })?
        }
        Request::BrokerUpdate(x) => {
            r::broker(&mut o, x.broker)?;
            p::option(&mut o, x.debt_maximum, p::number)?
        }
        Request::Cover(x) => {
            r::broker(&mut o, x.broker)?;
            p::numeric_type(&mut o, x.numeric_type);
            p::stamount(&mut o, x.amount)?
        }
        Request::CoverValidate(x) => {
            p::numeric_type(&mut o, x.numeric_type);
            p::number(&mut o, x.cover_available)?;
            p::stamount(&mut o, x.amount)?
        }
    };
    Ok(o)
}
pub fn encode_request(tag: u8, request: Request) -> Result<Vec<u8>, WireError> {
    if !(1..=27).contains(&tag) {
        return Err(WireError::OutOfRange(0));
    };
    Ok(p::envelope(tag, encode_payload(request)?))
}
/// Broker create/update returns `finish(tag, encodeBrokerOnly ...)`: no lifecycle wrapper.
pub fn decode_broker_response(
    operation: u8,
    input: &[u8],
) -> Result<Response<LoanBroker>, WireError> {
    let payload = read_envelope(operation + 128, input)?;
    let mut r0 = Reader::new(payload);
    match r0.u8()? {
        1 => Ok(Response::DecodeError(r0.u8()?)),
        0 => Ok(Response::Ok(r::decode_broker(&payload[r0.position()..])?)),
        x => Err(WireError::BadTag(0, x)),
    }
}
