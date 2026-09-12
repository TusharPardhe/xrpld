use crate::lending_wire::*;

pub(crate) fn complete_requests() -> Vec<(u32, Request)> {
    let zero = Number::ZERO;
    let issue = IssueId {
        currency: 1,
        issuer: AccountId(2),
    };
    let config = LendingConfig {
        lending_enabled: true,
        single_asset_vault_enabled: true,
        maximum_payments_per_transaction: 1,
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
        config,
        metadata: meta,
    };
    let bi = BrokerIdentity {
        broker_id: ObjectId(4),
        vault_id: ObjectId(1),
        owner: AccountId(2),
        account: AccountId(5),
    };
    let li = LoanIdentity {
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
    };
    let vault = Vault {
        assets_total: zero,
        assets_available: zero,
        assets_reserved: zero,
        assets_maximum: None,
        numeric_type: NumericType::Fractional,
        scale: 0,
        shares_total: zero,
        loss_unrealized: zero,
    };
    let broker = LoanBroker {
        identity: bi,
        management_fee_rate: 0,
        cover_rate_minimum: 0,
        cover_rate_liquidation: 0,
        debt_total: zero,
        debt_maximum: zero,
        cover_available: zero,
        loan_count: 0,
    };
    let rates = LoanRates {
        interest: 0,
        late_interest: 0,
        close_interest: 0,
        overpayment_interest: 0,
        overpayment_fee: 0,
    };
    let fees = LoanFees {
        origination: zero,
        service: zero,
        late_payment: zero,
        close_payment: zero,
    };
    let schedule = LoanSchedule {
        payment_interval: 1,
        payment_total: 1,
        grace_period: 0,
        start_date: 1,
    };
    let loan = Loan {
        identity: li,
        vault_identity: vi,
        rates,
        fees,
        schedule,
        payment_remaining: 0,
        periodic_payment: zero,
        principal_outstanding: zero,
        total_value_outstanding: zero,
        management_fee_outstanding: zero,
        loan_scale: 0,
        previous_payment_due_date: 0,
        next_payment_due_date: 1,
        pending: false,
        impaired: false,
        defaulted: false,
        allows_overpayment: false,
    };
    let create = Request::Create(CreateRequest {
        vault_identity: vi,
        loan_identity: li,
        vault,
        broker,
        principal: zero,
        rates,
        fees,
        schedule,
        allows_overpayment: false,
        pending: false,
    });
    let lv = Request::LoanVault(LoanVaultRequest { loan, vault });
    let base = BrokerRequest {
        loan,
        vault,
        broker,
    };
    let amount = Request::Amount(AmountRequest {
        base,
        amount: zero,
        now: 1,
    });
    let payment = Request::Payment(PaymentRequest {
        base,
        payment_type: PaymentType::Regular,
        amount: zero,
        now: 1,
    });
    let default = Request::Default(DefaultRequest {
        base,
        impaired: false,
    });
    let cover_amount = STAmount {
        numeric_type: NumericType::Fractional,
        mantissa: 1_000_000_000_000_000,
        exponent: -15,
        negative: false,
    };
    let cover = Request::Cover(CoverRequest {
        broker,
        numeric_type: NumericType::Fractional,
        amount: cover_amount,
    });
    let validate = Request::CoverValidate(CoverValidateRequest {
        numeric_type: NumericType::Fractional,
        cover_available: zero,
        amount: cover_amount,
    });
    let broker_create = Request::BrokerCreate(BrokerCreateRequest {
        identity: bi,
        debt_maximum: None,
        management_fee_rate: None,
        cover_rate_minimum: None,
        cover_rate_liquidation: None,
    });
    let broker_update = Request::BrokerUpdate(BrokerUpdateRequest {
        broker,
        debt_maximum: None,
    });
    vec![
        (1, create),
        (2, create),
        (3, create),
        (4, lv),
        (5, Request::Broker(base)),
        (6, payment),
        (7, amount),
        (8, amount),
        (9, lv),
        (10, lv),
        (11, default),
        (12, broker_create),
        (13, broker_update),
        (14, validate),
        (15, cover),
        (16, cover),
        (17, create),
        (18, create),
        (19, create),
        (20, lv),
        (21, Request::Broker(base)),
        (22, payment),
        (23, amount),
        (24, amount),
        (25, lv),
        (26, lv),
        (27, default),
    ]
}
