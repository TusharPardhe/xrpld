use ledger::vault_adapter::{RawVault, VaultAdapterError, WithdrawAmount};

#[test]
fn terminal_deposit_keeps_raw_and_clamped_amounts_distinct() {
    let vault = RawVault::new(100, 100, 100, 0, 1)
        .expect("lawful raw vault")
        .associate_terminal();
    let result = vault.deposit(17, false).expect("bounded deposit");

    assert_eq!(result.amount.raw, 17);
    assert_eq!(result.amount.clamped, 10);
    assert_eq!(result.amount.correction, 7);
    assert_eq!(result.vault.raw().dilution_correction, 7);
    assert_eq!(result.vault.raw().assets_total, 110);
    assert_eq!(result.vault.raw().shares_total, 110);
}

#[test]
fn terminal_withdraw_accumulates_correction_and_rejects_unavailable_assets() {
    let vault = RawVault::new(110, 110, 110, 0, 1)
        .expect("lawful raw vault")
        .associate_terminal();
    let result = vault
        .withdraw(WithdrawAmount::Assets(17), false)
        .expect("bounded withdrawal");

    assert_eq!(result.assets.raw, 17);
    assert_eq!(result.assets.clamped, 10);
    assert_eq!(result.vault.raw().dilution_correction, 7);
    assert_eq!(result.vault.raw().assets_total, 100);
    assert_eq!(
        result.vault.withdraw(WithdrawAmount::Assets(1_000), false),
        Err(VaultAdapterError::InsufficientFunds)
    );
}

#[test]
fn raw_burn_is_separate_from_terminal_burn_and_delete_checks() {
    let vault = RawVault::new(0, 0, 10, 0, 0)
        .expect("lawful raw vault")
        .associate_terminal();
    assert!(vault.can_burn_shares());
    let raw = vault.burn_shares_raw(10).expect("raw burn");
    assert!(raw.associate_terminal().can_delete());
    assert!(vault.burn_shares(10).expect("terminal burn").can_delete());
}
