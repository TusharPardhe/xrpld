use crate::lending_wire::*;

pub(crate) fn number(mantissa: u64, exponent: i64) -> Number {
    Number {
        negative: false,
        mantissa,
        exponent,
    }
}
pub(crate) fn create(pending: bool, interest: u32) -> CreateRequest {
    let zero = Number::ZERO;
    let issue = IssueId {
        currency: 1,
        issuer: AccountId(2),
    };
    let metadata = TransactionMetadata {
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
        metadata,
    };
    let broker_identity = BrokerIdentity {
        broker_id: ObjectId(4),
        vault_id: ObjectId(1),
        owner: AccountId(2),
        account: AccountId(5),
    };
    let loan_identity = LoanIdentity {
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
        metadata,
    };
    CreateRequest {
        vault_identity,
        loan_identity,
        vault: Vault {
            assets_total: number(1_000_000_000_000_000_000, -16),
            assets_available: number(1_000_000_000_000_000_000, -16),
            assets_reserved: zero,
            assets_maximum: None,
            numeric_type: NumericType::Fractional,
            scale: 0,
            shares_total: number(1_000_000_000_000_000_000, -18),
            loss_unrealized: zero,
        },
        broker: LoanBroker {
            identity: broker_identity,
            management_fee_rate: 0,
            cover_rate_minimum: 0,
            cover_rate_liquidation: 0,
            debt_total: zero,
            debt_maximum: zero,
            cover_available: zero,
            loan_count: 0,
        },
        principal: number(1_000_000_000_000_000_000, -17),
        rates: LoanRates {
            interest,
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
            payment_interval: 31_536_000,
            payment_total: 2,
            grace_period: 0,
            start_date: 1,
        },
        allows_overpayment: true,
        pending,
    }
}
