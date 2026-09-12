pub(crate) fn aid(r: &mut Reader) -> Result<AccountId, WireError> {
    Ok(AccountId(r.u64()?))
}
pub(crate) fn oid(r: &mut Reader) -> Result<ObjectId, WireError> {
    Ok(ObjectId(r.u64()?))
}
pub(crate) fn iid(r: &mut Reader) -> Result<IssueId, WireError> {
    Ok(IssueId {
        currency: r.u64()?,
        issuer: aid(r)?,
    })
}
pub(crate) fn vi(r: &mut Reader) -> Result<VaultIdentity, WireError> {
    Ok(VaultIdentity {
        vault_id: oid(r)?,
        owner: aid(r)?,
        account: aid(r)?,
        issue: iid(r)?,
        config: LendingConfig {
            lending_enabled: r.boolean()?,
            single_asset_vault_enabled: r.boolean()?,
            maximum_payments_per_transaction: r.u32()?,
        },
        metadata: TransactionMetadata {
            transaction_id: oid(r)?,
            sequence: r.u32()?,
            ledger_close_time: r.u32()?,
        },
    })
}
pub(crate) fn bi(r: &mut Reader) -> Result<BrokerIdentity, WireError> {
    Ok(BrokerIdentity {
        broker_id: oid(r)?,
        vault_id: oid(r)?,
        owner: aid(r)?,
        account: aid(r)?,
    })
}
pub(crate) fn li(r: &mut Reader) -> Result<LoanIdentity, WireError> {
    Ok(LoanIdentity {
        loan_id: oid(r)?,
        broker_id: oid(r)?,
        borrower: aid(r)?,
        counterparty: aid(r)?,
        issue: iid(r)?,
        authorization: CredentialAuth {
            counterparty_signed: r.boolean()?,
            deposit_authorized: r.boolean()?,
            credential_authorized: r.boolean()?,
        },
        metadata: TransactionMetadata {
            transaction_id: oid(r)?,
            sequence: r.u32()?,
            ledger_close_time: r.u32()?,
        },
    })
}
fn optnum(r: &mut Reader) -> Result<Option<Number>, WireError> {
    let offset = r.position();
    match r.u8()? {
        0 => Ok(None),
        1 => Ok(Some(r.number()?)),
        actual => Err(WireError::BadOption { offset, actual }),
    }
}
pub(crate) fn read_vault(r: &mut Reader) -> Result<Vault, WireError> {
    let offset = r.position();
    let vault = Vault {
        assets_total: r.number()?,
        assets_available: r.number()?,
        assets_reserved: r.number()?,
        assets_maximum: optnum(r)?,
        numeric_type: r.numeric_type()?,
        scale: r.u8()?,
        shares_total: r.number()?,
        loss_unrealized: r.number()?,
    };
    super::lwab_create_math::lawful(vault)
        .then_some(vault)
        .ok_or(WireError::NonCanonical(offset))
}
pub(crate) fn read_broker(r: &mut Reader) -> Result<LoanBroker, WireError> {
    Ok(LoanBroker {
        identity: bi(r)?,
        management_fee_rate: r.u16()?,
        cover_rate_minimum: r.u32()?,
        cover_rate_liquidation: r.u32()?,
        debt_total: r.number()?,
        debt_maximum: r.number()?,
        cover_available: r.number()?,
        loan_count: r.u32()?,
    })
}
pub(crate) fn read_loan(r: &mut Reader) -> Result<Loan, WireError> {
    Ok(Loan {
        identity: li(r)?,
        vault_identity: vi(r)?,
        rates: LoanRates {
            interest: r.u32()?,
            late_interest: r.u32()?,
            close_interest: r.u32()?,
            overpayment_interest: r.u32()?,
            overpayment_fee: r.u32()?,
        },
        fees: LoanFees {
            origination: r.number()?,
            service: r.number()?,
            late_payment: r.number()?,
            close_payment: r.number()?,
        },
        schedule: LoanSchedule {
            payment_interval: r.u32()?,
            payment_total: r.u32()?,
            grace_period: r.u32()?,
            start_date: r.u32()?,
        },
        payment_remaining: r.u32()?,
        periodic_payment: r.number()?,
        principal_outstanding: r.number()?,
        total_value_outstanding: r.number()?,
        management_fee_outstanding: r.number()?,
        loan_scale: r.int()?,
        previous_payment_due_date: r.u32()?,
        next_payment_due_date: r.u32()?,
        pending: r.boolean()?,
        impaired: r.boolean()?,
        defaulted: r.boolean()?,
        allows_overpayment: r.boolean()?,
    })
}
pub(crate) fn read_state(r: &mut Reader) -> Result<LendingState, WireError> {
    Ok(LendingState {
        vault_identity: vi(r)?,
        vault: read_vault(r)?,
        broker: read_broker(r)?,
        loan: read_loan(r)?,
    })
}
pub(crate) fn read_broker_vault(r: &mut Reader) -> Result<BrokerVault, WireError> {
    Ok(BrokerVault {
        vault_identity: vi(r)?,
        vault: read_vault(r)?,
        broker: read_broker(r)?,
    })
}
pub(crate) fn read_loan_vault(r: &mut Reader) -> Result<LoanVault, WireError> {
    Ok(LoanVault {
        vault_identity: vi(r)?,
        loan: read_loan(r)?,
        vault: read_vault(r)?,
    })
}
pub fn decode_broker(input: &[u8]) -> Result<LoanBroker, WireError> {
    let mut r = Reader::new(input);
    let x = read_broker(&mut r)?;
    r.done()?;
    Ok(x)
}
pub fn encode_broker(x: LoanBroker) -> Result<Vec<u8>, WireError> {
    let mut o = Vec::new();
    broker(&mut o, x)?;
    Ok(o)
}
pub fn encode_state(x: LendingState) -> Result<Vec<u8>, WireError> {
    let mut o = Vec::new();
    state(&mut o, x)?;
    Ok(o)
}
pub fn encode_broker_vault(x: BrokerVault) -> Result<Vec<u8>, WireError> {
    let mut o = Vec::new();
    broker_vault(&mut o, x)?;
    Ok(o)
}
pub fn encode_loan_vault(x: LoanVault) -> Result<Vec<u8>, WireError> {
    let mut o = Vec::new();
    loan_vault(&mut o, x)?;
    Ok(o)
}
