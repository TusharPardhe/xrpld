//! Lossless XLS-66 domain records for verification and handler extraction.
//!
//! Amounts retain the protocol `NumberParts` sign/mantissa/exponent triple;
//! this module deliberately has no `i64` amount projection.

use basics::{base_uint::Uint256, number::NumberParts};
use protocol::{AccountID, Issue, STAmount};

pub type Number = NumberParts;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumericType {
    Native,
    Int64,
    Fractional,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Credentials {
    pub counterparty_signed: bool,
    pub deposit_authorized: bool,
    pub credential_authorized: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LendingConfig {
    pub lending_enabled: bool,
    pub single_asset_vault_enabled: bool,
    pub maximum_payments_per_transaction: u32,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransactionMetadata {
    pub transaction_id: Uint256,
    pub sequence: u32,
    pub ledger_close_time: u32,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VaultIdentity {
    pub vault_id: Uint256,
    pub owner: AccountID,
    pub account: AccountID,
    pub issue: Issue,
    pub config: LendingConfig,
    pub metadata: TransactionMetadata,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BrokerIdentity {
    pub broker_id: Uint256,
    pub vault_id: Uint256,
    pub owner: AccountID,
    pub account: AccountID,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoanIdentity {
    pub loan_id: Uint256,
    pub broker_id: Uint256,
    pub borrower: AccountID,
    pub counterparty: AccountID,
    pub issue: Issue,
    pub authorization: Credentials,
    pub metadata: TransactionMetadata,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Vault {
    pub identity: VaultIdentity,
    pub assets_total: Number,
    pub assets_available: Number,
    pub assets_reserved: Number,
    pub assets_maximum: Option<Number>,
    pub numeric_type: NumericType,
    pub scale: u8,
    pub shares_total: Number,
    pub loss_unrealized: Number,
    pub associations: u32,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Broker {
    pub identity: BrokerIdentity,
    pub management_fee_rate: u16,
    pub cover_rate_minimum: u32,
    pub cover_rate_liquidation: u32,
    pub debt_total: Number,
    pub debt_maximum: Number,
    pub cover_available: Number,
    pub loan_count: u32,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoanRates {
    pub interest: u32,
    pub late_interest: u32,
    pub close_interest: u32,
    pub overpayment_interest: u32,
    pub overpayment_fee: u32,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoanFees {
    pub origination: Number,
    pub service: Number,
    pub late_payment: Number,
    pub close_payment: Number,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoanSchedule {
    pub payment_interval: u32,
    pub payment_total: u32,
    pub grace_period: u32,
    pub start_date: u32,
}
#[derive(Clone, Debug, PartialEq, Eq)]
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
    pub loan_scale: i32,
    pub previous_payment_due_date: u32,
    pub next_payment_due_date: u32,
    pub is_pending: bool,
    pub is_impaired: bool,
    pub is_default: bool,
    pub allows_overpayment: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BrokerVault {
    pub vault_identity: VaultIdentity,
    pub vault: Vault,
    pub broker: Broker,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoanVault {
    pub vault_identity: VaultIdentity,
    pub loan: Loan,
    pub vault: Vault,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LendingState {
    pub vault_identity: VaultIdentity,
    pub vault: Vault,
    pub broker: Broker,
    pub loan: Loan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LendingError {
    Disabled,
    InvalidIdentity,
    WrongAsset,
    Unauthorized,
    MissingCredential,
    CounterpartyMismatch,
    InsufficientFunds,
    LimitExceeded,
    NoEntry,
    HasObligations,
    TooSoon,
    Expired,
    PrecisionLoss,
    Arithmetic,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LendingResult<T> {
    Ok(T),
    Rejected(LendingError),
}

/// An explicitly asset-associated amount preserves both XRPL wire amount and
/// the numeric triple used by Lending accounting; neither is a projection.
#[derive(Clone, Debug)]
pub struct AssociatedAmount {
    pub amount: STAmount,
    pub number: Number,
}
