use crate::lending_wire::*;

pub(super) fn number(exponent: i64) -> Number {
    Number {
        negative: false,
        mantissa: 1_000_000_000_000_000_000,
        exponent,
    }
}

pub(super) fn request(
    pending: bool,
    reserved: Number,
    principal: Number,
    exponent: i64,
) -> Request {
    request_with_type(
        pending,
        reserved,
        principal,
        exponent,
        NumericType::Fractional,
    )
}

pub(super) fn request_with_type(
    pending: bool,
    reserved: Number,
    principal: Number,
    exponent: i64,
    numeric_type: NumericType,
) -> Request {
    let zero = Number::ZERO;
    let issue = IssueId {
        currency: 1,
        issuer: AccountId(2),
    };
    let meta = TransactionMetadata {
        transaction_id: ObjectId(9),
        sequence: 1,
        ledger_close_time: 1,
    };
    let vault_identity = VaultIdentity {
        vault_id: ObjectId(1),
        owner: AccountId(2),
        account: AccountId(3),
        issue,
        config: LendingConfig {
            lending_enabled: true,
            single_asset_vault_enabled: true,
            maximum_payments_per_transaction: 1,
        },
        metadata: meta,
    };
    let loan = Loan {
        identity: LoanIdentity {
            loan_id: ObjectId(6),
            broker_id: ObjectId(4),
            borrower: AccountId(7),
            counterparty: AccountId(7),
            issue,
            authorization: CredentialAuth {
                counterparty_signed: true,
                deposit_authorized: true,
                credential_authorized: true,
            },
            metadata: meta,
        },
        vault_identity,
        rates: LoanRates {
            interest: 0,
            late_interest: 0,
            close_interest: 0,
            overpayment_interest: 0,
            overpayment_fee: 0,
        },
        fees: LoanFees {
            origination: zero,
            service: zero,
            late_payment: zero,
            close_payment: zero,
        },
        schedule: LoanSchedule {
            payment_interval: 1,
            payment_total: 1,
            grace_period: 0,
            start_date: 1,
        },
        payment_remaining: 1,
        periodic_payment: principal,
        principal_outstanding: principal,
        total_value_outstanding: principal,
        management_fee_outstanding: zero,
        loan_scale: 0,
        previous_payment_due_date: 0,
        next_payment_due_date: 2,
        pending,
        impaired: false,
        defaulted: false,
        allows_overpayment: false,
    };
    Request::LoanVault(LoanVaultRequest {
        loan,
        vault: Vault {
            assets_total: number(exponent),
            assets_available: number(exponent),
            assets_reserved: reserved,
            assets_maximum: None,
            numeric_type,
            scale: 0,
            shares_total: number(0),
            loss_unrealized: zero,
        },
    })
}
