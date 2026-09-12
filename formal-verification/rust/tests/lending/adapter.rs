use basics::{base_uint::Uint256, number::NumberParts};
use ledger::lending_adapter::*;
use protocol::{AccountID, Issue, xrp_issue};

fn id(x: u64) -> Uint256 {
    Uint256::from_u64(x)
}
fn account(x: u64) -> AccountID {
    AccountID::from_u64(x)
}
fn n(x: i64) -> NumberParts {
    NumberParts::from_i64(x)
}
fn state() -> LendingState {
    let issue: Issue = xrp_issue();
    let owner = account(1);
    let borrower = account(6);
    let config = LendingConfig {
        lending_enabled: true,
        single_asset_vault_enabled: true,
        maximum_payments_per_transaction: 100,
    };
    let meta = TransactionMetadata {
        transaction_id: ObjectIdLike::object(7),
        sequence: 1,
        ledger_close_time: 10,
    };
    let vi = VaultIdentity {
        vault_id: ObjectIdLike::object(1),
        owner,
        account: account(2),
        issue,
        config,
        metadata: meta.clone(),
    };
    let bi = BrokerIdentity {
        broker_id: ObjectIdLike::object(3),
        vault_id: vi.vault_id,
        owner,
        account: account(4),
    };
    let li = LoanIdentity {
        loan_id: ObjectIdLike::object(5),
        broker_id: bi.broker_id,
        borrower,
        counterparty: borrower,
        issue,
        authorization: Credentials {
            counterparty_signed: true,
            deposit_authorized: true,
            credential_authorized: true,
        },
        metadata: meta,
    };
    let vault = Vault {
        identity: vi.clone(),
        assets_total: n(1000),
        assets_available: n(1000),
        assets_reserved: n(0),
        assets_maximum: None,
        numeric_type: NumericType::Fractional,
        scale: 0,
        shares_total: n(0),
        loss_unrealized: n(0),
        associations: 0,
    };
    let broker = Broker {
        identity: bi,
        management_fee_rate: 0,
        cover_rate_minimum: 0,
        cover_rate_liquidation: 0,
        debt_total: n(0),
        debt_maximum: n(900),
        cover_available: n(1000),
        loan_count: 0,
    };
    let loan = Loan {
        identity: li,
        vault_identity: vi.clone(),
        rates: LoanRates {
            interest: 0,
            late_interest: 0,
            close_interest: 0,
            overpayment_interest: 0,
            overpayment_fee: 0,
        },
        fees: LoanFees {
            origination: n(0),
            service: n(0),
            late_payment: n(0),
            close_payment: n(0),
        },
        schedule: LoanSchedule {
            payment_interval: 60,
            payment_total: 2,
            grace_period: 10,
            start_date: 0,
        },
        payment_remaining: 2,
        periodic_payment: n(0),
        principal_outstanding: n(0),
        total_value_outstanding: n(0),
        management_fee_outstanding: n(0),
        loan_scale: 0,
        previous_payment_due_date: 0,
        next_payment_due_date: 100,
        is_pending: false,
        is_impaired: false,
        is_default: false,
        allows_overpayment: false,
    };
    LendingState {
        vault_identity: vi,
        vault,
        broker,
        loan,
    }
}

/// Local helper only bridges the test's 256-bit fixture to the lossless ObjectId
/// field; production paths retain full `Uint256` records in the Quaxar core.
struct ObjectIdLike;
impl ObjectIdLike {
    fn object(x: u64) -> Uint256 {
        id(x)
    }
}

fn payable() -> LendingState {
    let mut s = state();
    s.loan.principal_outstanding = n(100);
    s.broker.debt_total = n(100);
    s.vault.assets_available = n(900);
    s
}

#[test]
fn raw_forms_preserve_identity_and_cover_each_operation() {
    let owner = account(1);
    let borrower = account(6);
    let before = state();
    let created = raw_create(before.clone(), owner, n(100)).unwrap();
    assert_eq!(created.loan.identity.loan_id, before.loan.identity.loan_id);
    assert!(raw_create_pending(before.clone(), owner, n(100)).is_ok());
    assert!(raw_create_immediate(before.clone(), owner, n(100)).is_ok());
    let mut pending = raw_create_pending(before.clone(), owner, n(100)).unwrap();
    pending.vault.assets_reserved = n(100);
    assert!(raw_accept(pending, borrower).is_ok());
    let mut done = before.clone();
    done.loan.payment_remaining = 0;
    done.broker.loan_count = 1;
    assert!(raw_delete(done, owner).is_ok());
    assert!(raw_regular_payment(payable(), borrower, n(50)).is_ok());
    let mut late = payable();
    late.loan.identity.metadata.ledger_close_time = 101;
    assert!(raw_late_payment(late.clone(), borrower, n(50)).is_ok());
    assert!(raw_full_payment(payable(), borrower, n(100)).is_ok());
    let impaired = raw_manage_impair(payable(), owner).unwrap();
    assert!(raw_manage_unimpair(impaired, owner).is_ok());
    assert!(raw_manage_default(late, owner).is_ok());
    assert_eq!(
        raw_broker_create(before.broker.clone(), Some(n(200))).loan_count,
        0
    );
    assert!(raw_broker_update(before.broker.clone(), Some(n(900))).is_ok());
    assert!(raw_cover_validate(n(100), n(10)).is_ok());
    assert!(raw_cover_deposit(before.broker.clone(), n(10)).is_ok());
    assert!(raw_cover_withdraw(before.broker, n(10)).is_ok());
}

#[test]
fn terminal_forms_associate_exactly_once_after_raw_success() {
    let owner = account(1);
    let borrower = account(6);
    let s = state();
    assert_eq!(
        terminal_create(s.clone(), owner, n(100))
            .unwrap()
            .vault
            .associations,
        1
    );
    assert_eq!(
        terminal_create_pending(s.clone(), owner, n(100))
            .unwrap()
            .vault
            .associations,
        1
    );
    assert_eq!(
        terminal_create_immediate(s.clone(), owner, n(100))
            .unwrap()
            .vault
            .associations,
        1
    );
    let mut pending = raw_create_pending(s.clone(), owner, n(100)).unwrap();
    pending.vault.assets_reserved = n(100);
    assert_eq!(
        terminal_accept(pending, borrower)
            .unwrap()
            .vault
            .associations,
        1
    );
    let mut done = s.clone();
    done.loan.payment_remaining = 0;
    done.broker.loan_count = 1;
    assert_eq!(terminal_delete(done, owner).unwrap().vault.associations, 1);
    assert_eq!(
        terminal_regular_payment(payable(), borrower, n(50))
            .unwrap()
            .vault
            .associations,
        1
    );
    let mut late = payable();
    late.loan.identity.metadata.ledger_close_time = 101;
    assert_eq!(
        terminal_late_payment(late.clone(), borrower, n(50))
            .unwrap()
            .vault
            .associations,
        1
    );
    assert_eq!(
        terminal_full_payment(payable(), borrower, n(100))
            .unwrap()
            .vault
            .associations,
        1
    );
    assert_eq!(
        terminal_manage_impair(payable(), owner)
            .unwrap()
            .vault
            .associations,
        1
    );
    let impaired = raw_manage_impair(payable(), owner).unwrap();
    assert_eq!(
        terminal_manage_unimpair(impaired, owner)
            .unwrap()
            .vault
            .associations,
        1
    );
    assert_eq!(
        terminal_manage_default(late, owner)
            .unwrap()
            .vault
            .associations,
        1
    );
}

#[test]
fn guard_failures_are_atomic_and_number_backed() {
    let s = state();
    assert_eq!(
        raw_create(s.clone(), account(6), n(1)),
        Err(LendingError::Unauthorized)
    );
    let mut disabled = s.clone();
    disabled.vault.identity.config.lending_enabled = false;
    assert_eq!(
        raw_create(disabled, account(1), n(1)),
        Err(LendingError::Disabled)
    );
    let mut no_auth = s.clone();
    no_auth.loan.identity.authorization.credential_authorized = false;
    assert_eq!(
        raw_create(no_auth, account(1), n(1)),
        Err(LendingError::MissingCredential)
    );
    assert_eq!(
        raw_cover_validate(n(1), n(2)),
        Err(LendingError::InsufficientFunds)
    );
}
