//! Lawful Vault record validation shared by strict LWAB decoding and transitions.

use super::types::{NumericType, Vault, zero_number};

pub(super) fn lawful(value: Vault) -> bool {
    let zero = zero_number();
    let common = value.total >= zero
        && value.available >= zero
        && value.available <= value.total
        && value.shares >= zero
        && value.loss >= zero
        && value
            .total
            .try_sub(value.available)
            .is_ok_and(|reserved| value.loss <= reserved)
        && value.maximum.is_none_or(|x| x > zero && value.total <= x)
        && (value.shares != zero || (value.total == zero && value.available == zero));
    match value.numeric_type {
        NumericType::Fractional => value.scale <= 18 && common,
        NumericType::Integral { .. } => value.scale == 0 && common,
    }
}
