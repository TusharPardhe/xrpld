//! Atomic terminal association for the typed lossless Lending result forms.
//!
//! A terminal transition owns no arithmetic: it executes a raw operation first
//! and, only on success, associates the Vault exactly once. Returning the raw
//! error before cloning/mutating a value keeps failures atomic.

use super::{BrokerVault, LendingError, LendingState, LoanVault, Vault};

fn associate(mut vault: Vault) -> Result<Vault, LendingError> {
    vault.associations = vault
        .associations
        .checked_add(1)
        .ok_or(LendingError::Arithmetic)?;
    Ok(vault)
}

pub fn state(raw: Result<LendingState, LendingError>) -> Result<LendingState, LendingError> {
    let mut state = raw?;
    state.vault = associate(state.vault)?;
    Ok(state)
}

pub fn vault(raw: Result<Vault, LendingError>) -> Result<Vault, LendingError> {
    associate(raw?)
}

pub fn broker_vault(raw: Result<BrokerVault, LendingError>) -> Result<BrokerVault, LendingError> {
    let mut result = raw?;
    result.vault = associate(result.vault)?;
    Ok(result)
}

pub fn loan_vault(raw: Result<LoanVault, LendingError>) -> Result<LoanVault, LendingError> {
    let mut result = raw?;
    result.vault = associate(result.vault)?;
    Ok(result)
}
