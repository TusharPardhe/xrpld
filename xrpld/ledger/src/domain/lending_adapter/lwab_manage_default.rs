//! Exact LWAB default transition 11 and terminal default route 27.
use super::{accept::associate, lwab_manage_math as math, lwab_types::*, manage::Outcome};
use basics::number::RoundingMode;
const INTERNAL: u8 = 1;
const BAD_LEDGER: u8 = 25;

pub(super) fn manage(request: DefaultRequest, terminal: bool) -> Outcome {
    let mut vault = request.base.vault;
    let mut broker = request.base.broker;
    let loan = request.base.loan;
    let default = loan.principal_outstanding;
    let covered = match math::cover(
        broker.debt_total,
        broker.cover_rate_minimum,
        broker.cover_rate_liquidation,
        vault.numeric_type,
        loan.loan_scale as i32,
        default,
        broker.cover_available,
    ) {
        Ok(value) => value,
        Err(error) => return Outcome::Model(error),
    };
    let vault_default = match math::sub(default, covered) {
        Ok(value) => math::wire(value),
        Err(error) => return Outcome::Model(error),
    };
    match math::less(vault.assets_total, vault_default) {
        Ok(true) => return Outcome::Rejected(BAD_LEDGER),
        Ok(false) => {}
        Err(error) => return Outcome::Model(error),
    }
    let scale = match math::scale(vault) {
        Ok(value) => value,
        Err(error) => return Outcome::Model(error),
    };
    let rounded = match math::round(
        vault.numeric_type,
        match math::raw(vault_default) {
            Ok(value) => value,
            Err(error) => return Outcome::Model(error),
        },
        RoundingMode::Downward,
        scale,
    ) {
        Ok(value) => math::wire(value),
        Err(error) => return Outcome::Model(error),
    };
    vault.assets_total = match math::sub(vault.assets_total, rounded) {
        Ok(value) => math::wire(value),
        Err(error) => return Outcome::Model(error),
    };
    vault.assets_available = match math::add(vault.assets_available, covered) {
        Ok(value) => math::wire(value),
        Err(error) => return Outcome::Model(error),
    };
    vault.assets_total = match math::dust_adjust(vault.assets_available, vault.assets_total) {
        Ok(value) => value,
        Err(error) => return Outcome::Model(error),
    };
    match math::greater(vault.assets_available, vault.assets_total) {
        Ok(true) => return Outcome::Rejected(INTERNAL),
        Ok(false) => {}
        Err(error) => return Outcome::Model(error),
    }
    broker.debt_total = match math::negative(default)
        .and_then(|delta| math::adjust(vault.numeric_type, broker.debt_total, delta, scale))
    {
        Ok(value) => value,
        Err(error) => return Outcome::Model(error),
    };
    match math::less(broker.cover_available, covered) {
        Ok(true) => return Outcome::Rejected(BAD_LEDGER),
        Ok(false) => {}
        Err(error) => return Outcome::Model(error),
    }
    broker.cover_available = match math::sub(broker.cover_available, covered) {
        Ok(value) => math::wire(value),
        Err(error) => return Outcome::Model(error),
    };
    if request.impaired {
        vault.loss_unrealized = match math::negative(default)
            .and_then(|delta| math::adjust(vault.numeric_type, vault.loss_unrealized, delta, scale))
        {
            Ok(value) => value,
            Err(error) => return Outcome::Model(error),
        };
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
    Outcome::Broker(BrokerVault {
        vault_identity: loan.vault_identity,
        vault,
        broker,
    })
}
