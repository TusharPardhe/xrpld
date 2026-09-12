//! `XRPAmount` port from `xrpl/protocol/XRPAmount.h`.

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use basics::number::{NumberArithmeticError, NumberParts, get_mantissa_scale};

use crate::JsonValue;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct XRPAmount {
    drops: i64,
}

pub const DROPS_PER_XRP: XRPAmount = XRPAmount::from_drops(1_000_000);

impl XRPAmount {
    pub const fn new() -> Self {
        Self::from_drops(0)
    }

    pub const fn from_drops(drops: i64) -> Self {
        Self { drops }
    }

    pub fn from_number(value: NumberParts) -> Result<Self, NumberArithmeticError> {
        Ok(Self::from_drops(value.try_to_i64()?))
    }

    pub const fn signum(self) -> i32 {
        if self.drops < 0 {
            -1
        } else if self.drops == 0 {
            0
        } else {
            1
        }
    }

    pub const fn drops(self) -> i64 {
        self.drops
    }

    pub const fn value(self) -> i64 {
        self.drops
    }

    pub const fn is_zero(self) -> bool {
        self.drops == 0
    }

    pub const fn min_positive_amount() -> Self {
        Self::from_drops(1)
    }

    pub fn decimal_xrp(self) -> f64 {
        self.drops as f64 / DROPS_PER_XRP.drops as f64
    }

    pub fn drops_as<Dest>(self) -> Option<Dest>
    where
        Dest: TryFrom<i64>,
    {
        Dest::try_from(self.drops).ok()
    }

    pub fn json_clipped(self) -> JsonValue {
        let min = i64::from(i32::MIN);
        let max = i64::from(i32::MAX);

        if self.drops < min {
            JsonValue::Signed(min)
        } else if self.drops > max {
            JsonValue::Signed(max)
        } else {
            JsonValue::Signed(self.drops)
        }
    }
}

impl From<i64> for XRPAmount {
    fn from(value: i64) -> Self {
        Self::from_drops(value)
    }
}

impl TryFrom<NumberParts> for XRPAmount {
    type Error = NumberArithmeticError;

    fn try_from(value: NumberParts) -> Result<Self, Self::Error> {
        Self::from_number(value)
    }
}

impl From<XRPAmount> for NumberParts {
    fn from(value: XRPAmount) -> Self {
        // XRP drops are always exact integers (max 10^17). Use try_normalize_exact
        // with the current scale. If it fails (e.g. after fee subtraction produces a
        // non-round value like 99999999999999988), fall back to the unchecked path
        // which preserves the exact integer without loss.
        let scale = get_mantissa_scale();
        NumberParts::try_from_external_parts(value.drops, 0, scale).unwrap_or_else(|_| {
            NumberParts::unchecked(value.drops < 0, value.drops.unsigned_abs(), 0)
        })
    }
}

impl From<XRPAmount> for bool {
    fn from(value: XRPAmount) -> Self {
        !value.is_zero()
    }
}

impl AddAssign for XRPAmount {
    fn add_assign(&mut self, rhs: Self) {
        self.drops = self.drops.wrapping_add(rhs.drops);
    }
}

impl Add for XRPAmount {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl SubAssign for XRPAmount {
    fn sub_assign(&mut self, rhs: Self) {
        self.drops = self.drops.wrapping_sub(rhs.drops);
    }
}

impl Sub for XRPAmount {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl AddAssign<i64> for XRPAmount {
    fn add_assign(&mut self, rhs: i64) {
        self.drops = self.drops.wrapping_add(rhs);
    }
}

impl SubAssign<i64> for XRPAmount {
    fn sub_assign(&mut self, rhs: i64) {
        self.drops = self.drops.wrapping_sub(rhs);
    }
}

impl Mul<i64> for XRPAmount {
    type Output = Self;

    fn mul(self, rhs: i64) -> Self::Output {
        Self::from_drops(self.drops.wrapping_mul(rhs))
    }
}

impl Mul<XRPAmount> for i64 {
    type Output = XRPAmount;

    fn mul(self, rhs: XRPAmount) -> Self::Output {
        rhs * self
    }
}

impl MulAssign<i64> for XRPAmount {
    fn mul_assign(&mut self, rhs: i64) {
        self.drops = self.drops.wrapping_mul(rhs);
    }
}

impl Div<i64> for XRPAmount {
    type Output = Self;

    fn div(self, rhs: i64) -> Self::Output {
        Self::from_drops(self.drops / rhs)
    }
}

impl DivAssign<i64> for XRPAmount {
    fn div_assign(&mut self, rhs: i64) {
        self.drops /= rhs;
    }
}

impl Neg for XRPAmount {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::from_drops(self.drops.wrapping_neg())
    }
}

pub fn mul_ratio(
    amount: XRPAmount,
    num: u32,
    den: u32,
    round_up: bool,
) -> Result<XRPAmount, NumberArithmeticError> {
    if den == 0 {
        return Err(NumberArithmeticError::DivideByZero);
    }

    let amount128 = i128::from(amount.drops());
    let negative = amount.drops() < 0;
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
    Ok(XRPAmount::from_drops(result))
}
