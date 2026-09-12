//! Shared pure Lending kernels. These retain NumberParts amounts end-to-end.

use super::model::{LendingError, LendingState, LoanSchedule, Number};

pub fn validate_guard(
    state: &LendingState,
    actor: protocol::AccountID,
) -> Result<(), LendingError> {
    let v = &state.vault.identity;
    let b = &state.broker.identity;
    let l = &state.loan.identity;
    if !v.config.lending_enabled || !v.config.single_asset_vault_enabled {
        return Err(LendingError::Disabled);
    }
    if v.vault_id.is_zero()
        || b.broker_id.is_zero()
        || l.loan_id.is_zero()
        || v.owner.is_zero()
        || v.account.is_zero()
        || b.owner.is_zero()
        || b.account.is_zero()
        || l.borrower.is_zero()
        || l.counterparty.is_zero()
    {
        return Err(LendingError::InvalidIdentity);
    }
    if v.vault_id != b.vault_id || b.broker_id != l.broker_id {
        return Err(LendingError::InvalidIdentity);
    }
    if v.issue != l.issue {
        return Err(LendingError::WrongAsset);
    }
    if actor != b.owner && actor != l.borrower {
        return Err(LendingError::Unauthorized);
    }
    if !l.authorization.credential_authorized || !l.authorization.deposit_authorized {
        return Err(LendingError::MissingCredential);
    }
    Ok(())
}

pub fn has_expired(now: u32, expiry: u32, exclusive: bool) -> bool {
    if exclusive {
        now > expiry
    } else {
        now >= expiry
    }
}

pub fn build_schedule(
    interval: Option<u32>,
    total: Option<u32>,
    grace: Option<u32>,
    start: u32,
    close: u32,
    two_step: bool,
) -> LoanSchedule {
    LoanSchedule {
        payment_interval: interval.unwrap_or(60),
        payment_total: total.unwrap_or(1),
        grace_period: grace.unwrap_or(60),
        start_date: if two_step { start } else { close },
    }
}

pub fn schedule_available(schedule: &LoanSchedule) -> bool {
    let available = u32::MAX.saturating_sub(schedule.start_date);
    schedule.grace_period <= available
        && schedule.payment_interval != 0
        && schedule.payment_interval <= available
        && schedule.payment_total <= available
        && available.saturating_sub(schedule.grace_period) / schedule.payment_interval
            >= schedule.payment_total
}

pub fn add_amount(a: Number, b: Number) -> Result<Number, LendingError> {
    a.try_add(b).map_err(|_| LendingError::Arithmetic)
}
pub fn sub_amount(a: Number, b: Number) -> Result<Number, LendingError> {
    a.try_sub(b).map_err(|_| LendingError::Arithmetic)
}

pub fn apply_principal_delta(state: &mut LendingState, delta: Number) -> Result<(), LendingError> {
    state.loan.principal_outstanding = add_amount(state.loan.principal_outstanding, delta)?;
    state.broker.debt_total = add_amount(state.broker.debt_total, delta)?;
    Ok(())
}

/// The terminal pass is deliberately separate: it runs only after a raw core
/// succeeds and records exactly one Vault association.
pub fn associate_vault_terminal(mut state: LendingState) -> Result<LendingState, LendingError> {
    state.vault.associations = state
        .vault
        .associations
        .checked_add(1)
        .ok_or(LendingError::Arithmetic)?;
    Ok(state)
}
