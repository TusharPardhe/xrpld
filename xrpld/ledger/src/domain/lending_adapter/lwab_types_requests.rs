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
