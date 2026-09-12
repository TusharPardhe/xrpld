use ledger::lending_lwab::{
    self as lwab, AccountId, CredentialAuth, IssueId, LendingConfig, Lifecycle, Loan, LoanFees,
    LoanIdentity, LoanRates, LoanSchedule, LoanVaultRequest, Number, NumericType, ObjectId,
    Payload, Request, Response, TransactionMetadata, Vault, VaultIdentity,
};

fn number(exponent: i64) -> Number {
    Number {
        negative: false,
        mantissa: 1_000_000_000_000_000_000,
        exponent,
    }
}

fn request(exponent: i64) -> Request {
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
    let identity = VaultIdentity {
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
    Request::LoanVault(LoanVaultRequest {
        loan: Loan {
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
                metadata,
            },
            vault_identity: identity,
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
            periodic_payment: number(exponent),
            principal_outstanding: number(exponent),
            total_value_outstanding: number(exponent),
            management_fee_outstanding: zero,
            loan_scale: 0,
            previous_payment_due_date: 0,
            next_payment_due_date: 2,
            pending: true,
            impaired: false,
            defaulted: false,
            allows_overpayment: false,
        },
        vault: Vault {
            assets_total: number(exponent),
            assets_available: number(exponent),
            assets_reserved: number(exponent),
            assets_maximum: None,
            numeric_type: NumericType::Fractional,
            scale: 0,
            shares_total: number(0),
            loss_unrealized: zero,
        },
    })
}

#[test]
fn lwab_accept_is_lossless_raw_then_atomic_terminal_association() {
    let raw_input = lwab::encode_request(4, request(-18)).unwrap();
    let raw = lwab::dispatch_route(4, &raw_input);
    let Response::Ok(Payload::LoanVault(Lifecycle::Value(value))) =
        lwab::decode_response(4, &raw).unwrap()
    else {
        panic!("raw accept succeeds")
    };
    assert!(!value.loan.pending);
    assert_eq!(value.vault.assets_reserved, Number::ZERO);
    assert_eq!(lwab::dispatch_route(4, &raw_input), raw);

    let terminal_input = lwab::encode_request(20, request(81)).unwrap();
    assert_eq!(
        lwab::decode_response(20, &lwab::dispatch_route(20, &terminal_input)).unwrap(),
        Response::Ok(Payload::LoanVault(Lifecycle::ModelError(0))),
        "failed association returns no raw result, so the transition is atomic"
    );
    let malformed = lwab::dispatch_route(4, b"NOPE");
    assert_eq!(malformed, lwab::dispatch_route(4, b"NOPE"));
    assert_eq!(
        lwab::decode_response(4, &malformed),
        Ok(Response::DecodeError(2))
    );
}
