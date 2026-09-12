//! Lossless field types used by the Vault version-one wire codec.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Number {
    pub negative: bool,
    pub mantissa: u64,
    pub exponent: i32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumericType {
    Native,
    Int64,
    Fractional,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Amount {
    pub numeric_type: NumericType,
    pub number: Number,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Vault {
    pub vault_id: [u8; 32],
    pub owner: [u8; 20],
    pub account: [u8; 20],
    pub asset: Amount,
    pub assets_total: Number,
    pub assets_available: Number,
    pub assets_reserved: Number,
    pub assets_maximum: Option<Number>,
    pub numeric_type: NumericType,
    pub scale: u8,
    pub shares_total: Number,
    pub loss_unrealized: Number,
    /// `false` is raw/internal; `true` is a terminal/public association.
    pub terminal: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    PrecisionLoss,
    InsufficientFunds,
    InvalidState,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Ok(Vault),
    Error(Error),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CodecError {
    Truncated,
    Trailing,
    BadVersion,
    BadTag,
    BadBoolean,
    BadOption,
}
