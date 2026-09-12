use ledger::lending_lwab::{
    self as lwab, AccountId, BrokerIdentity, BrokerRequest, CredentialAuth, IssueId, LendingConfig,
    Lifecycle, Loan, LoanBroker, LoanFees, LoanIdentity, LoanRates, LoanSchedule, Number,
    NumericType, ObjectId, Payload, Request, Response, TransactionMetadata, Vault, VaultIdentity,
};

fn n(exp: i64) -> Number {
    Number {
        negative: false,
        mantissa: 1_000_000_000_000_000_000,
        exponent: exp,
    }
}
fn request(pending: bool, exponent: i64) -> Request {
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
            counterparty: AccountId(8),
            issue,
            authorization: CredentialAuth {
                counterparty_signed: false,
                deposit_authorized: false,
                credential_authorized: false,
            },
            metadata: meta,
        },
        vault_identity,
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

#[test]
fn lwab_delete_preserves_complete_raw_and_atomic_terminal_semantics() {
    let raw = lwab::encode_request(5, request(true, -18)).unwrap();
    let Response::Ok(Payload::BrokerVault(Lifecycle::Value(value))) =
        lwab::decode_response(5, &lwab::dispatch_route(5, &raw)).unwrap()
    else {
        panic!("pending delete succeeds")
    };
    assert_eq!(value.vault.assets_available, n(-18));
    assert_eq!(value.vault.assets_reserved, Number::ZERO);
    assert_eq!(value.broker.debt_total, Number::ZERO);
    assert_eq!(value.broker.loan_count, 0);
    assert_eq!(value.broker.cover_available, n(-18));
    assert_eq!(lwab::dispatch_route(5, &raw), lwab::dispatch_route(5, &raw));

    let active = lwab::encode_request(5, request(false, -18)).unwrap();
    let Response::Ok(Payload::BrokerVault(Lifecycle::Value(value))) =
        lwab::decode_response(5, &lwab::dispatch_route(5, &active)).unwrap()
    else {
        panic!("active delete succeeds")
    };
    assert_eq!(value.vault.assets_reserved, n(-18));
    assert_eq!(
        value.broker.debt_total,
        Number::ZERO,
        "last active loan clears debt"
    );

    let terminal = lwab::encode_request(21, request(true, 81)).unwrap();
    assert_eq!(
        lwab::decode_response(21, &lwab::dispatch_route(21, &terminal)),
        Ok(Response::Ok(Payload::BrokerVault(Lifecycle::ModelError(0))))
    );
    for (tag, input) in [(5, b"NOPE".as_slice()), (21, b"NOPE".as_slice())] {
        assert_eq!(
            lwab::decode_response(tag, &lwab::dispatch_route(tag, input)),
            Ok(Response::DecodeError(2))
        );
    }
    let mut malformed = raw.clone();
    malformed.push(0);
    assert!(matches!(
        lwab::decode_response(5, &lwab::dispatch_route(5, &malformed)),
        Ok(Response::DecodeError(1))
    ));
    let body = (10..raw.len())
        .find_map(|at| {
            let mut candidate = raw.clone();
            candidate[at] = 2;
            matches!(
                lwab::decode_response(5, &lwab::dispatch_route(5, &candidate)),
                Ok(Response::DecodeError(5))
            )
            .then_some(candidate)
        })
        .expect("reachable body boolean");
    assert!(matches!(
        lwab::decode_response(5, &lwab::dispatch_route(5, &body)),
        Ok(Response::DecodeError(5))
    ));
}
