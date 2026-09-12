use super::{
    lwab_create_math as math,
    lwab_primitive::{self as p, Reader, WireError},
    lwab_records as records,
    lwab_types::*,
};
use basics::number::{NumberParts, RoundingMode};

const TER_INVALID: u8 = 33;

enum Outcome {
    Rejected(u8),
    Model(u8),
    Value(LendingState),
}

pub(super) enum CreateMode {
    RequestPending,
    Pending,
    Immediate,
}

pub(super) fn dispatch(input: &[u8], mode: CreateMode) -> Vec<u8> {
    let (route, forced_pending) = match mode {
        CreateMode::RequestPending => (1, None),
        CreateMode::Pending => (2, Some(true)),
        CreateMode::Immediate => (3, Some(false)),
    };
    let mut request = match p::read_envelope(route, input).and_then(read_create) {
        Ok(value) => value,
        Err(error) => return super::finish(route, Err(error)),
    };
    // Lean's pending/immediate wrappers still decode the wire boolean, then
    // deliberately discard it when calling Loan.createPending/createImmediate.
    if let Some(pending) = forced_pending {
        request.pending = pending;
    }
    let payload = match create(request) {
        Outcome::Value(state) => {
            let mut value = vec![0, 0];
            records::state(&mut value, state).expect("constructed state canonical");
            value
        }
        Outcome::Rejected(ter) => vec![0, 1, ter],
        Outcome::Model(error) => vec![1, error],
    };
    super::finish(route, Ok(payload))
}

fn read_create(body: &[u8]) -> Result<CreateRequest, WireError> {
    let mut r = Reader::new(body);
    let value = CreateRequest {
        vault_identity: records::vi(&mut r)?,
        loan_identity: records::li(&mut r)?,
        vault: records::read_vault(&mut r)?,
        broker: records::read_broker(&mut r)?,
        principal: r.number()?,
        rates: rates(&mut r)?,
        fees: fees(&mut r)?,
        schedule: schedule(&mut r)?,
        allows_overpayment: r.boolean()?,
        pending: r.boolean()?,
    };
    r.done()?;
    Ok(value)
}
fn rates(r: &mut Reader<'_>) -> Result<LoanRates, WireError> {
    Ok(LoanRates {
        interest: r.u32()?,
        late_interest: r.u32()?,
        close_interest: r.u32()?,
        overpayment_interest: r.u32()?,
        overpayment_fee: r.u32()?,
    })
}
fn fees(r: &mut Reader<'_>) -> Result<LoanFees, WireError> {
    Ok(LoanFees {
        origination: r.number()?,
        service: r.number()?,
        late_payment: r.number()?,
        close_payment: r.number()?,
    })
}
fn schedule(r: &mut Reader<'_>) -> Result<LoanSchedule, WireError> {
    Ok(LoanSchedule {
        payment_interval: r.u32()?,
        payment_total: r.u32()?,
        grace_period: r.u32()?,
        start_date: r.u32()?,
    })
}

fn rejected<T>(result: Result<T, u8>) -> Result<T, Outcome> {
    result.map_err(Outcome::Model)
}
fn rounded(
    nt: NumericType,
    value: NumberParts,
    scale: i32,
    mode: RoundingMode,
) -> Result<NumberParts, Outcome> {
    rejected(math::round(nt, value, mode, scale))
}
fn valid(v: VaultIdentity, b: BrokerIdentity, l: LoanIdentity) -> bool {
    let account = |x: AccountId| x.0 != 0;
    let object = |x: ObjectId| x.0 != 0;
    let issue = |x: IssueId| x.currency != 0 && account(x.issuer);
    object(v.vault_id)
        && account(v.owner)
        && account(v.account)
        && issue(v.issue)
        && v.config.lending_enabled
        && v.config.single_asset_vault_enabled
        && v.config.maximum_payments_per_transaction != 0
        && object(v.metadata.transaction_id)
        && object(b.broker_id)
        && object(b.vault_id)
        && account(b.owner)
        && account(b.account)
        && object(l.loan_id)
        && object(l.broker_id)
        && account(l.borrower)
        && account(l.counterparty)
        && issue(l.issue)
        && l.authorization.credential_authorized
        && l.authorization.deposit_authorized
        && object(l.metadata.transaction_id)
        && v.vault_id == b.vault_id
        && b.broker_id == l.broker_id
        && v.issue == l.issue
}
fn precisely(nt: NumericType, x: NumberParts, scale: i32) -> Result<bool, Outcome> {
    Ok(rounded(nt, x, scale, RoundingMode::Downward)?
        == rounded(nt, x, scale, RoundingMode::Upward)?)
}

include!("lwab_create_compute.rs");
include!("lwab_create_build.rs");
