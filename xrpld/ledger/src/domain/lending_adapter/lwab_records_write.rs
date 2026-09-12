fn account(o: &mut Vec<u8>, x: AccountId) {
    p::u64(o, x.0)
}
fn object(o: &mut Vec<u8>, x: ObjectId) {
    p::u64(o, x.0)
}
fn issue(o: &mut Vec<u8>, x: IssueId) {
    p::u64(o, x.currency);
    account(o, x.issuer)
}
fn auth(o: &mut Vec<u8>, x: CredentialAuth) {
    p::boolean(o, x.counterparty_signed);
    p::boolean(o, x.deposit_authorized);
    p::boolean(o, x.credential_authorized)
}
fn config(o: &mut Vec<u8>, x: LendingConfig) {
    p::boolean(o, x.lending_enabled);
    p::boolean(o, x.single_asset_vault_enabled);
    p::u32(o, x.maximum_payments_per_transaction)
}
fn meta(o: &mut Vec<u8>, x: TransactionMetadata) {
    object(o, x.transaction_id);
    p::u32(o, x.sequence);
    p::u32(o, x.ledger_close_time)
}
pub(crate) fn vault_identity(o: &mut Vec<u8>, x: VaultIdentity) {
    object(o, x.vault_id);
    account(o, x.owner);
    account(o, x.account);
    issue(o, x.issue);
    config(o, x.config);
    meta(o, x.metadata)
}
pub(crate) fn broker_identity(o: &mut Vec<u8>, x: BrokerIdentity) {
    object(o, x.broker_id);
    object(o, x.vault_id);
    account(o, x.owner);
    account(o, x.account)
}
fn loan_identity(o: &mut Vec<u8>, x: LoanIdentity) {
    object(o, x.loan_id);
    object(o, x.broker_id);
    account(o, x.borrower);
    account(o, x.counterparty);
    issue(o, x.issue);
    auth(o, x.authorization);
    meta(o, x.metadata)
}
pub(crate) fn vault(o: &mut Vec<u8>, x: Vault) -> Result<(), WireError> {
    p::number(o, x.assets_total)?;
    p::number(o, x.assets_available)?;
    p::number(o, x.assets_reserved)?;
    p::option(o, x.assets_maximum, p::number)?;
    p::numeric_type(o, x.numeric_type);
    p::u8(o, x.scale);
    p::number(o, x.shares_total)?;
    p::number(o, x.loss_unrealized)
}
pub(crate) fn broker(o: &mut Vec<u8>, x: LoanBroker) -> Result<(), WireError> {
    broker_identity(o, x.identity);
    p::u16(o, x.management_fee_rate);
    p::u32(o, x.cover_rate_minimum);
    p::u32(o, x.cover_rate_liquidation);
    p::number(o, x.debt_total)?;
    p::number(o, x.debt_maximum)?;
    p::number(o, x.cover_available)?;
    p::u32(o, x.loan_count);
    Ok(())
}
fn rates(o: &mut Vec<u8>, x: LoanRates) {
    for n in [
        x.interest,
        x.late_interest,
        x.close_interest,
        x.overpayment_interest,
        x.overpayment_fee,
    ] {
        p::u32(o, n)
    }
}
fn fees(o: &mut Vec<u8>, x: LoanFees) -> Result<(), WireError> {
    for n in [x.origination, x.service, x.late_payment, x.close_payment] {
        p::number(o, n)?
    }
    Ok(())
}
fn schedule(o: &mut Vec<u8>, x: LoanSchedule) {
    for n in [
        x.payment_interval,
        x.payment_total,
        x.grace_period,
        x.start_date,
    ] {
        p::u32(o, n)
    }
}
pub(crate) fn loan(o: &mut Vec<u8>, x: Loan) -> Result<(), WireError> {
    loan_identity(o, x.identity);
    vault_identity(o, x.vault_identity);
    rates(o, x.rates);
    fees(o, x.fees)?;
    schedule(o, x.schedule);
    p::u32(o, x.payment_remaining);
    for n in [
        x.periodic_payment,
        x.principal_outstanding,
        x.total_value_outstanding,
        x.management_fee_outstanding,
    ] {
        p::number(o, n)?
    }
    p::int(o, x.loan_scale);
    p::u32(o, x.previous_payment_due_date);
    p::u32(o, x.next_payment_due_date);
    for b in [x.pending, x.impaired, x.defaulted, x.allows_overpayment] {
        p::boolean(o, b)
    }
    Ok(())
}
pub(crate) fn state(o: &mut Vec<u8>, x: LendingState) -> Result<(), WireError> {
    vault_identity(o, x.vault_identity);
    vault(o, x.vault)?;
    broker(o, x.broker)?;
    loan(o, x.loan)
}
pub(crate) fn broker_vault(o: &mut Vec<u8>, x: BrokerVault) -> Result<(), WireError> {
    vault_identity(o, x.vault_identity);
    vault(o, x.vault)?;
    broker(o, x.broker)
}
pub(crate) fn loan_vault(o: &mut Vec<u8>, x: LoanVault) -> Result<(), WireError> {
    vault_identity(o, x.vault_identity);
    loan(o, x.loan)?;
    vault(o, x.vault)
}
