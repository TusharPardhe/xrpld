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
