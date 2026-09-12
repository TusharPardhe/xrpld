//! Exact LWAB impairment and unimpairment routes 9/10 and terminal 25/26.
use super::{
    accept::associate,
    lwab_manage_math as math,
    lwab_primitive::{self as p, Reader, WireError},
    lwab_records as records,
    lwab_types::*,
};
const BAD_LEDGER: u8 = 25;
const LIMIT: u8 = 38;
pub(super) enum Outcome {
    Vault(Vault),
    Broker(BrokerVault),
    Rejected(u8),
    Model(u8),
}
pub(super) enum Request {
    LoanVault(LoanVaultRequest),
    Default(DefaultRequest),
}

pub(super) fn dispatch(input: &[u8], kind: u8, terminal: bool) -> Vec<u8> {
    let route = if terminal { kind + 16 } else { kind };
    let payload = match p::read_envelope(route, input).and_then(|body| read(body, kind)) {
        Ok(request) => finish(apply(request, kind, terminal)),
        Err(error) => return super::finish(route, Err(error)),
    };
    super::finish(route, Ok(payload))
}
fn read(body: &[u8], kind: u8) -> Result<Request, WireError> {
    let mut r = Reader::new(body);
    let loan = records::read_loan(&mut r)?;
    let vault = records::read_vault(&mut r)?;
    let request = if kind == 11 {
        Request::Default(DefaultRequest {
            base: BrokerRequest {
                loan,
                vault,
                broker: records::read_broker(&mut r)?,
            },
            impaired: r.boolean()?,
        })
    } else {
        Request::LoanVault(LoanVaultRequest { loan, vault })
    };
    r.done()?;
    Ok(request)
}
fn finish(outcome: Outcome) -> Vec<u8> {
    match outcome {
        Outcome::Vault(vault) => {
            let mut out = vec![0, 0];
            records::vault(&mut out, vault).expect("canonical management vault");
            out
        }
        Outcome::Broker(value) => {
            let mut out = vec![0, 0];
            records::broker_vault(&mut out, value).expect("canonical management broker vault");
            out
        }
        Outcome::Rejected(ter) => vec![0, 1, ter],
        Outcome::Model(error) => vec![1, error],
    }
}
fn apply(request: Request, kind: u8, terminal: bool) -> Outcome {
    match request {
        Request::LoanVault(x) => manage_vault(x, kind, terminal),
        Request::Default(x) => super::lwab_manage_default::manage(x, terminal),
    }
}
fn manage_vault(request: LoanVaultRequest, kind: u8, terminal: bool) -> Outcome {
    let mut vault = request.vault;
    let scale = match math::scale(vault) {
        Ok(value) => value,
        Err(error) => return Outcome::Model(error),
    };
    let delta = if kind == 9 {
        request.loan.principal_outstanding
    } else {
        match math::negative(request.loan.principal_outstanding) {
            Ok(value) => value,
            Err(error) => return Outcome::Model(error),
        }
    };
    if kind == 10 {
        match math::less(vault.loss_unrealized, request.loan.principal_outstanding) {
            Ok(true) => return Outcome::Rejected(BAD_LEDGER),
            Ok(false) => {}
            Err(error) => return Outcome::Model(error),
        }
    }
    vault.loss_unrealized =
        match math::adjust(vault.numeric_type, vault.loss_unrealized, delta, scale) {
            Ok(value) => value,
            Err(error) => return Outcome::Model(error),
        };
    if kind == 9 {
        let gap = match math::sub(vault.assets_total, vault.assets_available) {
            Ok(value) => math::wire(value),
            Err(error) => return Outcome::Model(error),
        };
        match math::greater(vault.loss_unrealized, gap) {
            Ok(true) => return Outcome::Rejected(LIMIT),
            Ok(false) => {}
            Err(error) => return Outcome::Model(error),
        }
    }
    if !math::lawful(vault) {
        return Outcome::Model(math::NOT_LAWFUL);
    }
    if terminal {
        vault = match associate(vault) {
            Ok(value) => value,
            Err(error) => return Outcome::Model(error),
        };
    }
    Outcome::Vault(vault)
}
