use crate::{
    lending_create,
    lending_wire::{LoanBroker, Number, NumericType, STAmount},
};

pub(crate) fn n(mantissa: u64, exponent: i64) -> Number {
    Number {
        negative: false,
        mantissa,
        exponent,
    }
}
pub(crate) fn broker() -> LoanBroker {
    let mut value = lending_create::create(false, 0).broker;
    value.cover_available = n(1_000_000_000_000_000_000, -18);
    value.debt_total = n(1_000_000_000_000_000_000, -18);
    value.loan_count = 1;
    value
}
pub(crate) fn fractional(mantissa: u64, exponent: i64) -> STAmount {
    STAmount {
        numeric_type: NumericType::Fractional,
        mantissa,
        exponent,
        negative: false,
    }
}
pub(crate) fn integral(mantissa: u64) -> STAmount {
    STAmount {
        numeric_type: NumericType::Integral {
            maximum: 100_000_000_000_000_000,
            offset: 17,
            sqrt: 3_000_000_000,
            shift: 2_095_475_792,
        },
        mantissa,
        exponent: 0,
        negative: false,
    }
}
