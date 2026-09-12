use super::lending_wire_types_identity::*;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CreateRequest {
    pub vault_identity: VaultIdentity,
    pub loan_identity: LoanIdentity,
    pub vault: Vault,
    pub broker: LoanBroker,
    pub principal: Number,
    pub rates: LoanRates,
    pub fees: LoanFees,
    pub schedule: LoanSchedule,
    pub allows_overpayment: bool,
    pub pending: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoanVaultRequest {
    pub loan: Loan,
    pub vault: Vault,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BrokerRequest {
    pub loan: Loan,
    pub vault: Vault,
    pub broker: LoanBroker,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PaymentType {
    Regular,
    Late,
    Full,
    Overpayment,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaymentRequest {
    pub base: BrokerRequest,
    pub payment_type: PaymentType,
    pub amount: Number,
    pub now: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AmountRequest {
    pub base: BrokerRequest,
    pub amount: Number,
    pub now: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DefaultRequest {
    pub base: BrokerRequest,
    pub impaired: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BrokerCreateRequest {
    pub identity: BrokerIdentity,
    pub debt_maximum: Option<Number>,
    pub management_fee_rate: Option<u16>,
    pub cover_rate_minimum: Option<u32>,
    pub cover_rate_liquidation: Option<u32>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BrokerUpdateRequest {
    pub broker: LoanBroker,
    pub debt_maximum: Option<Number>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CoverRequest {
    pub broker: LoanBroker,
    pub numeric_type: NumericType,
    pub amount: STAmount,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CoverValidateRequest {
    pub numeric_type: NumericType,
    pub cover_available: Number,
    pub amount: STAmount,
}
