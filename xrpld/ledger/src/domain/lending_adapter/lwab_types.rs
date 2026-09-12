//! Exact value types for version-one Lean Lending wire frames.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AccountId(pub u64);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ObjectId(pub u64);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IssueId {
    pub currency: u64,
    pub issuer: AccountId,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CredentialAuth {
    pub counterparty_signed: bool,
    pub deposit_authorized: bool,
    pub credential_authorized: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LendingConfig {
    pub lending_enabled: bool,
    pub single_asset_vault_enabled: bool,
    pub maximum_payments_per_transaction: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TransactionMetadata {
    pub transaction_id: ObjectId,
    pub sequence: u32,
    pub ledger_close_time: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VaultIdentity {
    pub vault_id: ObjectId,
    pub owner: AccountId,
    pub account: AccountId,
    pub issue: IssueId,
    pub config: LendingConfig,
    pub metadata: TransactionMetadata,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BrokerIdentity {
    pub broker_id: ObjectId,
    pub vault_id: ObjectId,
    pub owner: AccountId,
    pub account: AccountId,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoanIdentity {
    pub loan_id: ObjectId,
    pub broker_id: ObjectId,
    pub borrower: AccountId,
    pub counterparty: AccountId,
    pub issue: IssueId,
    pub authorization: CredentialAuth,
    pub metadata: TransactionMetadata,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Number {
    pub negative: bool,
    pub mantissa: u64,
    pub exponent: i64,
}
impl Number {
    pub const ZERO: Self = Self {
        negative: false,
        mantissa: 0,
        exponent: i32::MIN as i64,
    };
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumericType {
    Fractional,
    Integral {
        maximum: u64,
        offset: i64,
        sqrt: u64,
        shift: u64,
    },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct STAmount {
    pub numeric_type: NumericType,
    pub mantissa: u64,
    pub exponent: i64,
    pub negative: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Vault {
    pub assets_total: Number,
    pub assets_available: Number,
    pub assets_reserved: Number,
    pub assets_maximum: Option<Number>,
    pub numeric_type: NumericType,
    pub scale: u8,
    pub shares_total: Number,
    pub loss_unrealized: Number,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoanBroker {
    pub identity: BrokerIdentity,
    pub management_fee_rate: u16,
    pub cover_rate_minimum: u32,
    pub cover_rate_liquidation: u32,
    pub debt_total: Number,
    pub debt_maximum: Number,
    pub cover_available: Number,
    pub loan_count: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoanRates {
    pub interest: u32,
    pub late_interest: u32,
    pub close_interest: u32,
    pub overpayment_interest: u32,
    pub overpayment_fee: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoanFees {
    pub origination: Number,
    pub service: Number,
    pub late_payment: Number,
    pub close_payment: Number,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoanSchedule {
    pub payment_interval: u32,
    pub payment_total: u32,
    pub grace_period: u32,
    pub start_date: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Loan {
    pub identity: LoanIdentity,
    pub vault_identity: VaultIdentity,
    pub rates: LoanRates,
    pub fees: LoanFees,
    pub schedule: LoanSchedule,
    pub payment_remaining: u32,
    pub periodic_payment: Number,
    pub principal_outstanding: Number,
    pub total_value_outstanding: Number,
    pub management_fee_outstanding: Number,
    pub loan_scale: i64,
    pub previous_payment_due_date: u32,
    pub next_payment_due_date: u32,
    pub pending: bool,
    pub impaired: bool,
    pub defaulted: bool,
    pub allows_overpayment: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LendingState {
    pub vault_identity: VaultIdentity,
    pub vault: Vault,
    pub broker: LoanBroker,
    pub loan: Loan,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BrokerVault {
    pub vault_identity: VaultIdentity,
    pub vault: Vault,
    pub broker: LoanBroker,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoanVault {
    pub vault_identity: VaultIdentity,
    pub loan: Loan,
    pub vault: Vault,
}

include!("lwab_types_requests.rs");
