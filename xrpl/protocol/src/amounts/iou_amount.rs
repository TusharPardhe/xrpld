//! `IOUAmount` port from `xrpl/protocol/IOUAmount.h`.

use basics::number::{
    NumberArithmeticError, NumberParts as RuntimeNumber,
    current_mantissa_range as current_runtime_mantissa_range,
};

mod mul_ratio;
mod normalization;
mod operators;
mod rounding;
mod traits;

use normalization::{
    normalize_runtime_number_to_range, runtime_number_from_external_parts, signed_runtime_mantissa,
};
use rounding::IouRoundGuard;

pub use mul_ratio::mul_ratio;

pub const MIN_IOU_EXPONENT: i32 = -96;
pub const MAX_IOU_EXPONENT: i32 = 80;
pub const MIN_IOU_MANTISSA: i64 = 1_000_000_000_000_000;
pub const MAX_IOU_MANTISSA: i64 = 9_999_999_999_999_999;
pub const IOU_ZERO_EXPONENT: i32 = -100;

/// Converts a `Number` using rippled's raw `IOUAmount::fromNumber` scaling.
///
/// This deliberately does not impose IOU exponent bounds or canonicalize zero,
/// so callers that need the raw C++ conversion can inspect its normalized parts.
pub fn raw_iou_parts_from_number(
    number: RuntimeNumber,
) -> Result<(i64, i32), NumberArithmeticError> {
    let normalized = normalize_runtime_number_to_range(
        number,
        MIN_IOU_MANTISSA as u64,
        MAX_IOU_MANTISSA as u64,
    )?;
    Ok((signed_runtime_mantissa(normalized)?, normalized.exponent))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IOUAmount {
    mantissa: i64,
    exponent: i32,
}

impl Default for IOUAmount {
    fn default() -> Self {
        Self::new()
    }
}

impl IOUAmount {
    pub const fn new() -> Self {
        Self {
            mantissa: 0,
            exponent: IOU_ZERO_EXPONENT,
        }
    }

    pub fn from_parts(mantissa: i64, exponent: i32) -> Result<Self, NumberArithmeticError> {
        let mut value = Self { mantissa, exponent };
        value.normalize()?;
        Ok(value)
    }

    /// Constructs a canonical, invariant-bearing IOU amount from a `Number`.
    pub fn from_number(number: RuntimeNumber) -> Result<Self, NumberArithmeticError> {
        let (mantissa, exponent) = raw_iou_parts_from_number(number)?;
        if mantissa == 0 || exponent < MIN_IOU_EXPONENT {
            return Ok(Self::new());
        }
        if exponent > MAX_IOU_EXPONENT {
            return Err(NumberArithmeticError::Overflow);
        }
        Ok(Self { mantissa, exponent })
    }

    pub const fn mantissa(self) -> i64 {
        self.mantissa
    }

    pub const fn exponent(self) -> i32 {
        self.exponent
    }

    pub const fn is_zero(self) -> bool {
        self.mantissa == 0
    }

    pub const fn signum(self) -> i32 {
        if self.mantissa < 0 {
            -1
        } else if self.mantissa == 0 {
            0
        } else {
            1
        }
    }

    pub const fn min_positive_amount() -> Self {
        Self {
            mantissa: MIN_IOU_MANTISSA,
            exponent: MIN_IOU_EXPONENT,
        }
    }

    pub fn checked_add(self, rhs: Self) -> Result<Self, NumberArithmeticError> {
        let mut value = self;
        value.checked_add_assign(rhs)?;
        Ok(value)
    }

    pub fn checked_sub(self, rhs: Self) -> Result<Self, NumberArithmeticError> {
        self.checked_add(-rhs)
    }

    pub fn checked_add_assign(&mut self, rhs: Self) -> Result<(), NumberArithmeticError> {
        if rhs.is_zero() {
            return Ok(());
        }
        if self.is_zero() {
            *self = rhs;
            return Ok(());
        }
        let sum = RuntimeNumber::from(*self).try_add(RuntimeNumber::from(rhs))?;
        *self = Self::from_number(sum)?;
        Ok(())
    }

    pub fn checked_sub_assign(&mut self, rhs: Self) -> Result<(), NumberArithmeticError> {
        self.checked_add_assign(-rhs)
    }

    fn normalize(&mut self) -> Result<(), NumberArithmeticError> {
        if self.mantissa == 0 {
            *self = Self::new();
            return Ok(());
        }
        let runtime = runtime_number_from_external_parts(
            self.mantissa,
            self.exponent,
            current_runtime_mantissa_range().scale,
        )?;
        *self = Self::from_number(runtime)?;
        Ok(())
    }
}

impl TryFrom<RuntimeNumber> for IOUAmount {
    type Error = NumberArithmeticError;

    fn try_from(value: RuntimeNumber) -> Result<Self, Self::Error> {
        Self::from_number(value)
    }
}

impl From<IOUAmount> for RuntimeNumber {
    fn from(value: IOUAmount) -> Self {
        runtime_number_from_external_parts(
            value.mantissa,
            value.exponent,
            current_runtime_mantissa_range().scale,
        )
        .expect("IOUAmount should remain representable in the current Number runtime")
    }
}

impl From<IOUAmount> for bool {
    fn from(value: IOUAmount) -> Self {
        !value.is_zero()
    }
}
