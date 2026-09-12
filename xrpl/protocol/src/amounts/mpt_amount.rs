//! `MPTAmount` port from `xrpl/protocol/MPTAmount.h`.

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use basics::number::{NumberArithmeticError, NumberParts, get_mantissa_scale};

pub const MAX_MP_TOKEN_AMOUNT: i64 = 0x7FFF_FFFF_FFFF_FFFF;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct MPTAmount {
    value: i64,
}

impl MPTAmount {
    pub const fn new() -> Self {
        Self::from_value(0)
    }

    pub const fn from_value(value: i64) -> Self {
        Self { value }
    }

    pub fn from_number(value: NumberParts) -> Result<Self, NumberArithmeticError> {
        Ok(Self::from_value(value.try_to_i64()?))
    }

    pub const fn signum(self) -> i32 {
        if self.value < 0 {
            -1
        } else if self.value == 0 {
            0
        } else {
            1
        }
    }

    pub const fn value(self) -> i64 {
        self.value
    }

    pub const fn is_zero(self) -> bool {
        self.value == 0
    }

    pub const fn min_positive_amount() -> Self {
        Self::from_value(1)
    }
}

impl From<i64> for MPTAmount {
    fn from(value: i64) -> Self {
        Self::from_value(value)
    }
}

impl TryFrom<NumberParts> for MPTAmount {
    type Error = NumberArithmeticError;

    fn try_from(value: NumberParts) -> Result<Self, Self::Error> {
        Self::from_number(value)
    }
}

impl From<MPTAmount> for NumberParts {
    fn from(value: MPTAmount) -> Self {
        NumberParts::try_from_external_parts(value.value, 0, get_mantissa_scale())
            .expect("MPTAmount should normalize into current Number range")
    }
}

impl From<MPTAmount> for bool {
    fn from(value: MPTAmount) -> Self {
        !value.is_zero()
    }
}

impl AddAssign for MPTAmount {
    fn add_assign(&mut self, rhs: Self) {
        self.value = self.value.wrapping_add(rhs.value);
    }
}

impl Add for MPTAmount {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl SubAssign for MPTAmount {
    fn sub_assign(&mut self, rhs: Self) {
        self.value = self.value.wrapping_sub(rhs.value);
    }
}

impl Sub for MPTAmount {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl Mul<i64> for MPTAmount {
    type Output = Self;

    fn mul(self, rhs: i64) -> Self::Output {
        Self::from_value(self.value.wrapping_mul(rhs))
    }
}

impl MulAssign<i64> for MPTAmount {
    fn mul_assign(&mut self, rhs: i64) {
        self.value = self.value.wrapping_mul(rhs);
    }
}

impl Div<i64> for MPTAmount {
    type Output = Self;

    fn div(self, rhs: i64) -> Self::Output {
        Self::from_value(self.value / rhs)
    }
}

impl DivAssign<i64> for MPTAmount {
    fn div_assign(&mut self, rhs: i64) {
        self.value /= rhs;
    }
}

impl Mul<MPTAmount> for i64 {
    type Output = MPTAmount;

    fn mul(self, rhs: MPTAmount) -> Self::Output {
        rhs * self
    }
}

impl Neg for MPTAmount {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::from_value(self.value.wrapping_neg())
    }
}

pub fn mul_ratio(
    amount: MPTAmount,
    num: u32,
    den: u32,
    round_up: bool,
) -> Result<MPTAmount, NumberArithmeticError> {
    if den == 0 {
        return Err(NumberArithmeticError::DivideByZero);
    }

    let amount128 = i128::from(amount.value());
    let negative = amount.value() < 0;
    let multiplied = amount128
        .checked_mul(i128::from(num))
        .ok_or(NumberArithmeticError::Overflow)?;
    let mut result = multiplied / i128::from(den);

    if multiplied % i128::from(den) != 0 {
        if !negative && round_up {
            result += 1;
        }
        if negative && !round_up {
            result -= 1;
        }
    }

    let result = i64::try_from(result).map_err(|_| NumberArithmeticError::Overflow)?;
    Ok(MPTAmount::from_value(result))
}
