use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use basics::number::{RoundingMode, get_rounding_mode};

use super::{IOUAmount, mul_ratio};

impl AddAssign for IOUAmount {
    fn add_assign(&mut self, rhs: Self) {
        self.checked_add_assign(rhs).expect(
            "IOUAmount addition should preserve the reference implementation overflow behavior",
        );
    }
}

impl Add for IOUAmount {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl SubAssign for IOUAmount {
    fn sub_assign(&mut self, rhs: Self) {
        self.checked_sub_assign(rhs).expect(
            "IOUAmount subtraction should preserve the reference implementation overflow behavior",
        );
    }
}

impl Sub for IOUAmount {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl Mul<i64> for IOUAmount {
    type Output = Self;

    fn mul(self, rhs: i64) -> Self::Output {
        let mut result = mul_ratio(
            self,
            rhs.unsigned_abs() as u32,
            1,
            get_rounding_mode() == RoundingMode::Upward,
        )
        .expect("IOUAmount multiplication overflow");
        if rhs < 0 {
            result = -result;
        }
        result
    }
}

impl MulAssign<i64> for IOUAmount {
    fn mul_assign(&mut self, rhs: i64) {
        *self = *self * rhs;
    }
}

impl Div<i64> for IOUAmount {
    type Output = Self;

    fn div(self, rhs: i64) -> Self::Output {
        let mut result = mul_ratio(
            self,
            1,
            rhs.unsigned_abs() as u32,
            get_rounding_mode() == RoundingMode::Upward,
        )
        .expect("IOUAmount division overflow");
        if rhs < 0 {
            result = -result;
        }
        result
    }
}

impl DivAssign<i64> for IOUAmount {
    fn div_assign(&mut self, rhs: i64) {
        *self = *self / rhs;
    }
}

impl Mul<IOUAmount> for i64 {
    type Output = IOUAmount;

    fn mul(self, rhs: IOUAmount) -> Self::Output {
        rhs * self
    }
}

impl Neg for IOUAmount {
    type Output = Self;

    fn neg(self) -> Self::Output {
        if self.is_zero() {
            self
        } else {
            Self {
                mantissa: -self.mantissa,
                exponent: self.exponent,
            }
        }
    }
}
