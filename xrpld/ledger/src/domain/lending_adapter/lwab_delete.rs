//! Exact LWAB Loan.delete raw (5) and terminal (21) transitions.

use super::{
    lwab_create_math as math,
    lwab_primitive::{self as p, Reader, WireError},
    lwab_records as records,
    lwab_types::*,
};
use basics::number::{NumberArithmeticError, NumberParts, NumberRoundModeGuard, RoundingMode};

const OVERFLOW: u8 = 0;
const OUT_OF_RANGE: u8 = 2;
const NOT_LAWFUL: u8 = 8;

enum Outcome {
    Value(BrokerVault),
    Model(u8),
}

pub(super) fn dispatch(input: &[u8], terminal: bool) -> Vec<u8> {
    let route = if terminal { 21 } else { 5 };
    let request = match p::read_envelope(route, input).and_then(read_request) {
        Ok(value) => value,
        Err(error) => return super::finish(route, Err(error)),
    };
    let payload = match delete(request, terminal) {
        Outcome::Value(value) => {
            let mut payload = vec![0, 0];
            records::broker_vault(&mut payload, value).expect("delete result is canonical");
            payload
        }
        Outcome::Model(error) => vec![1, error],
    };
    super::finish(route, Ok(payload))
}

fn read_request(body: &[u8]) -> Result<BrokerRequest, WireError> {
    let mut reader = Reader::new(body);
    let request = BrokerRequest {
        loan: records::read_loan(&mut reader)?,
        vault: records::read_vault(&mut reader)?,
        broker: records::read_broker(&mut reader)?,
    };
    reader.done()?;
    Ok(request)
}

fn arithmetic(error: NumberArithmeticError) -> u8 {
    match error {
        NumberArithmeticError::Overflow | NumberArithmeticError::DivideByZero => OVERFLOW,
    }
}
fn nearest(run: impl FnOnce() -> Result<NumberParts, NumberArithmeticError>) -> Result<Number, u8> {
    let _rounding = NumberRoundModeGuard::new(RoundingMode::ToNearest);
    run().map(math::wire).map_err(arithmetic)
}
fn negate(value: Number) -> Result<NumberParts, u8> {
    let value = math::raw(value)?;
    Ok(NumberParts::unchecked(
        !value.negative && value.mantissa != 0,
        value.mantissa,
        value.exponent,
    ))
}
include!("lwab_delete_associate.rs");
fn delete(request: BrokerRequest, terminal: bool) -> Outcome {
    let mut vault = request.vault;
    let mut broker = request.broker;
    if !request.loan.pending {
        let count = broker.loan_count.wrapping_sub(1);
        broker.loan_count = count;
        if count == 0 {
            broker.debt_total = Number::ZERO;
        }
        return finish(request.loan.vault_identity, vault, broker, terminal);
    }
    let principal = match math::raw(request.loan.principal_outstanding) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let available = match math::raw(vault.assets_available) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let reserved = match math::raw(vault.assets_reserved) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    vault.assets_available = match nearest(|| available.try_add(principal)) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    vault.assets_reserved = match nearest(|| reserved.try_sub(principal)) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    if !math::lawful(vault) {
        return Outcome::Model(NOT_LAWFUL);
    }
    let total = match math::raw(vault.assets_total) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let scale = match math::exponent(vault.numeric_type, total) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let debt_before = match math::raw(broker.debt_total) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let adjustment = match negate(request.loan.principal_outstanding) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let debt = match nearest(|| debt_before.try_add(adjustment)) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let debt = match math::raw(debt)
        .and_then(|x| math::round(vault.numeric_type, x, RoundingMode::ToNearest, scale))
    {
        Ok(x) => math::wire(x),
        Err(e) => return Outcome::Model(e),
    };
    broker.debt_total = if debt.negative { Number::ZERO } else { debt };
    broker.loan_count = broker.loan_count.wrapping_sub(1);
    finish(request.loan.vault_identity, vault, broker, terminal)
}
fn finish(
    vault_identity: VaultIdentity,
    vault: Vault,
    broker: LoanBroker,
    terminal: bool,
) -> Outcome {
    let vault = if terminal {
        match associate(vault) {
            Ok(x) => x,
            Err(e) => return Outcome::Model(e),
        }
    } else {
        vault
    };
    Outcome::Value(BrokerVault {
        vault_identity,
        vault,
        broker,
    })
}
