use crate::lending_wire::*;

pub(super) fn n(exponent: i64) -> Number {
    Number {
        negative: false,
        mantissa: 1_000_000_000_000_000_000,
        exponent,
    }
}
pub(super) fn request(pending: bool, exponent: i64) -> Request {
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
    let vi = VaultIdentity {
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
            counterparty: AccountId(8),
            issue,
            authorization: CredentialAuth {
                counterparty_signed: false,
                deposit_authorized: false,
                credential_authorized: false,
            },
            metadata: meta,
        },
        vault_identity: vi,
        rates: LoanRates {
            interest: 1,
            late_interest: 2,
            close_interest: 3,
            overpayment_interest: 4,
            overpayment_fee: 5,
        },
        fees: LoanFees {
            origination: n(exponent),
            service: n(exponent),
            late_payment: n(exponent),
            close_payment: n(exponent),
        },
        schedule: LoanSchedule {
            payment_interval: 1,
            payment_total: 1,
            grace_period: 0,
            start_date: 1,
        },
        payment_remaining: 1,
        periodic_payment: n(exponent),
        principal_outstanding: n(exponent),
        total_value_outstanding: n(exponent),
        management_fee_outstanding: n(exponent),
        loan_scale: 0,
        previous_payment_due_date: 0,
        next_payment_due_date: 2,
        pending,
        impaired: true,
        defaulted: true,
        allows_overpayment: true,
    };
    Request::Broker(BrokerRequest {
        loan,
        vault: Vault {
            assets_total: n(exponent),
            assets_available: if pending { zero } else { n(exponent) },
            assets_reserved: n(exponent),
            assets_maximum: Some(n(exponent)),
            numeric_type: NumericType::Fractional,
            scale: 0,
            shares_total: n(exponent),
            loss_unrealized: zero,
        },
        broker: LoanBroker {
            identity: BrokerIdentity {
                broker_id: ObjectId(4),
                vault_id: ObjectId(1),
                owner: AccountId(5),
                account: AccountId(6),
            },
            management_fee_rate: 9,
            cover_rate_minimum: 10,
            cover_rate_liquidation: 11,
            debt_total: n(exponent),
            debt_maximum: n(exponent),
            cover_available: n(exponent),
            loan_count: 1,
        },
    })
}
