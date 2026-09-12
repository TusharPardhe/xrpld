//! Pure, lossless Lending operation forms over `NumberParts`.

use super::terminal;
use super::{Broker, BrokerVault, LendingError, LendingState, LoanVault, Vault};
use super::{add_amount, has_expired, sub_amount, validate_guard};
use basics::number::NumberParts;
use protocol::AccountID;

fn zero() -> NumberParts {
    NumberParts::zero()
}
fn owner(s: &LendingState, a: AccountID) -> Result<(), LendingError> {
    validate_guard(s, a)?;
    if a == s.broker.identity.owner {
        Ok(())
    } else {
        Err(LendingError::Unauthorized)
    }
}
fn positive(x: NumberParts) -> Result<(), LendingError> {
    if x > zero() {
        Ok(())
    } else {
        Err(LendingError::PrecisionLoss)
    }
}

pub fn raw_create(
    mut s: LendingState,
    actor: AccountID,
    principal: NumberParts,
) -> Result<LendingState, LendingError> {
    owner(&s, actor)?;
    positive(principal)?;
    if s.vault.assets_available < principal {
        return Err(LendingError::InsufficientFunds);
    }
    let debt = add_amount(s.broker.debt_total, principal)?;
    if s.broker.debt_maximum != zero() && debt > s.broker.debt_maximum {
        return Err(LendingError::LimitExceeded);
    }
    s.vault.assets_available = sub_amount(s.vault.assets_available, principal)?;
    s.broker.debt_total = debt;
    s.broker.loan_count = s
        .broker
        .loan_count
        .checked_add(1)
        .ok_or(LendingError::Arithmetic)?;
    s.loan.principal_outstanding = principal;
    Ok(s)
}
pub fn raw_create_pending(
    mut s: LendingState,
    actor: AccountID,
    x: NumberParts,
) -> Result<LendingState, LendingError> {
    s.loan.is_pending = true;
    raw_create(s, actor, x)
}
pub fn raw_create_immediate(
    mut s: LendingState,
    actor: AccountID,
    x: NumberParts,
) -> Result<LendingState, LendingError> {
    s.loan.is_pending = false;
    raw_create(s, actor, x)
}
pub fn raw_accept(mut s: LendingState, actor: AccountID) -> Result<LendingState, LendingError> {
    validate_guard(&s, actor)?;
    if actor != s.loan.identity.counterparty
        || !s.loan.is_pending
        || !s.loan.identity.authorization.counterparty_signed
    {
        return Err(LendingError::CounterpartyMismatch);
    }
    if has_expired(
        s.loan.identity.metadata.ledger_close_time,
        s.loan.next_payment_due_date,
        false,
    ) {
        return Err(LendingError::Expired);
    }
    if s.vault.assets_reserved < s.loan.principal_outstanding {
        return Err(LendingError::InsufficientFunds);
    }
    s.vault.assets_reserved = sub_amount(s.vault.assets_reserved, s.loan.principal_outstanding)?;
    s.loan.is_pending = false;
    Ok(s)
}
pub fn raw_delete(mut s: LendingState, actor: AccountID) -> Result<LendingState, LendingError> {
    validate_guard(&s, actor)?;
    if !s.loan.is_pending && s.loan.payment_remaining != 0 {
        return Err(LendingError::HasObligations);
    }
    s.broker.loan_count = s
        .broker
        .loan_count
        .checked_sub(1)
        .ok_or(LendingError::NoEntry)?;
    if s.broker.loan_count == 0 {
        s.broker.debt_total = zero();
    }
    Ok(s)
}
fn payment(
    mut s: LendingState,
    actor: AccountID,
    amount: NumberParts,
    late: bool,
    full: bool,
) -> Result<LendingState, LendingError> {
    validate_guard(&s, actor)?;
    positive(amount)?;
    if actor != s.loan.identity.borrower || s.loan.is_pending || s.loan.is_default {
        return Err(LendingError::Unauthorized);
    }
    let expired = has_expired(
        s.loan.identity.metadata.ledger_close_time,
        s.loan.next_payment_due_date,
        false,
    );
    if late && !expired {
        return Err(LendingError::TooSoon);
    }
    if !late && expired {
        return Err(LendingError::Expired);
    }
    if (full && amount != s.loan.principal_outstanding)
        || amount > s.loan.principal_outstanding
        || s.loan.payment_remaining == 0
    {
        return Err(LendingError::PrecisionLoss);
    }
    s.loan.principal_outstanding = sub_amount(s.loan.principal_outstanding, amount)?;
    s.broker.debt_total = sub_amount(s.broker.debt_total, amount)?;
    s.vault.assets_available = add_amount(s.vault.assets_available, amount)?;
    if full {
        s.loan.payment_remaining = 0;
    } else {
        s.loan.payment_remaining -= 1;
    }
    Ok(s)
}
pub fn raw_regular_payment(
    s: LendingState,
    a: AccountID,
    x: NumberParts,
) -> Result<LendingState, LendingError> {
    payment(s, a, x, false, false)
}
pub fn raw_late_payment(
    s: LendingState,
    a: AccountID,
    x: NumberParts,
) -> Result<LendingState, LendingError> {
    payment(s, a, x, true, false)
}
pub fn raw_full_payment(
    s: LendingState,
    a: AccountID,
    x: NumberParts,
) -> Result<LendingState, LendingError> {
    payment(s, a, x, false, true)
}
pub fn raw_manage_impair(
    mut s: LendingState,
    actor: AccountID,
) -> Result<LendingState, LendingError> {
    owner(&s, actor)?;
    if s.loan.is_pending || s.loan.is_impaired || s.loan.is_default {
        return Err(LendingError::Unauthorized);
    }
    s.vault.loss_unrealized = add_amount(s.vault.loss_unrealized, s.loan.principal_outstanding)?;
    s.loan.is_impaired = true;
    Ok(s)
}
pub fn raw_manage_unimpair(
    mut s: LendingState,
    actor: AccountID,
) -> Result<LendingState, LendingError> {
    owner(&s, actor)?;
    if !s.loan.is_impaired || s.loan.is_default {
        return Err(LendingError::Unauthorized);
    }
    if s.vault.loss_unrealized < s.loan.principal_outstanding {
        return Err(LendingError::NoEntry);
    }
    s.vault.loss_unrealized = sub_amount(s.vault.loss_unrealized, s.loan.principal_outstanding)?;
    s.loan.is_impaired = false;
    Ok(s)
}
pub fn raw_manage_default(
    mut s: LendingState,
    actor: AccountID,
) -> Result<LendingState, LendingError> {
    owner(&s, actor)?;
    if s.loan.is_pending || s.loan.payment_remaining == 0 {
        return Err(LendingError::Unauthorized);
    }
    if !has_expired(
        s.loan.identity.metadata.ledger_close_time,
        s.loan.next_payment_due_date,
        true,
    ) {
        return Err(LendingError::TooSoon);
    }
    let covered = s.loan.principal_outstanding.min(s.broker.cover_available);
    let loss = sub_amount(s.loan.principal_outstanding, covered)?;
    if loss > s.vault.assets_total {
        return Err(LendingError::InsufficientFunds);
    }
    s.broker.cover_available = sub_amount(s.broker.cover_available, covered)?;
    s.broker.debt_total = sub_amount(s.broker.debt_total, s.loan.principal_outstanding)?;
    s.vault.assets_total = sub_amount(s.vault.assets_total, loss)?;
    s.vault.assets_available = add_amount(s.vault.assets_available, covered)?;
    s.loan.is_default = true;
    Ok(s)
}

pub fn raw_broker_create(mut b: Broker, debt_maximum: Option<NumberParts>) -> Broker {
    b.debt_maximum = debt_maximum.unwrap_or(zero());
    b.debt_total = zero();
    b.cover_available = zero();
    b.loan_count = 0;
    b
}
pub fn raw_broker_update(
    mut b: Broker,
    debt_maximum: Option<NumberParts>,
) -> Result<Broker, LendingError> {
    if let Some(x) = debt_maximum {
        if x != zero() && x < b.debt_total {
            return Err(LendingError::LimitExceeded);
        }
        b.debt_maximum = x;
    }
    Ok(b)
}
pub fn raw_cover_validate(cover: NumberParts, amount: NumberParts) -> Result<(), LendingError> {
    positive(amount)?;
    if amount > cover {
        Err(LendingError::InsufficientFunds)
    } else {
        Ok(())
    }
}
pub fn raw_cover_deposit(mut b: Broker, x: NumberParts) -> Result<Broker, LendingError> {
    positive(x)?;
    b.cover_available = add_amount(b.cover_available, x)?;
    Ok(b)
}
pub fn raw_cover_withdraw(mut b: Broker, x: NumberParts) -> Result<Broker, LendingError> {
    raw_cover_validate(b.cover_available, x)?;
    b.cover_available = sub_amount(b.cover_available, x)?;
    Ok(b)
}

macro_rules! terminal_state {($n:ident,$r:ident $(,$a:ident:$t:ty)*)=>{pub fn $n(s:LendingState,actor:AccountID $(,$a:$t)*)->Result<LendingState,LendingError>{terminal::state($r(s,actor $(,$a)*))}};}
terminal_state!(terminal_create,raw_create,x:NumberParts);
terminal_state!(terminal_create_pending,raw_create_pending,x:NumberParts);
terminal_state!(terminal_create_immediate,raw_create_immediate,x:NumberParts);
terminal_state!(terminal_accept, raw_accept);
terminal_state!(terminal_delete, raw_delete);
terminal_state!(terminal_regular_payment,raw_regular_payment,x:NumberParts);
terminal_state!(terminal_late_payment,raw_late_payment,x:NumberParts);
terminal_state!(terminal_full_payment,raw_full_payment,x:NumberParts);
terminal_state!(terminal_manage_impair, raw_manage_impair);
terminal_state!(terminal_manage_unimpair, raw_manage_unimpair);
terminal_state!(terminal_manage_default, raw_manage_default);

pub fn broker_vault(
    vault_identity: super::VaultIdentity,
    vault: Vault,
    broker: Broker,
) -> BrokerVault {
    BrokerVault {
        vault_identity,
        vault,
        broker,
    }
}
pub fn loan_vault(
    vault_identity: super::VaultIdentity,
    loan: super::Loan,
    vault: Vault,
) -> LoanVault {
    LoanVault {
        vault_identity,
        loan,
        vault,
    }
}
