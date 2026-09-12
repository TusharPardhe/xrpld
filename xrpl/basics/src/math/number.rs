//! Runtime `Number` policy surface.
//!
//! This now ports the core `Number` arithmetic surface:
//! - thread-local mantissa-scale and rounding-mode state,
//! - normalization and conversion helpers,
//! - reference-style guarded add / subtract / multiply / divide, and
//! - rounded integer conversion and human formatting.
//!
//! It now also ports the root / power helpers that sit on top of those
//! arithmetic primitives.

use std::{
    cell::Cell,
    cmp::Ordering,
    convert::TryFrom,
    fmt,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

pub const NUMBER_MIN_EXPONENT: i32 = -32_768;
pub const NUMBER_MAX_EXPONENT: i32 = 32_768;
pub const NUMBER_MAX_REP: i64 = i64::MAX;
pub const NUMBER_MAX_REP_UP: u64 = NUMBER_MAX_REP as u64 + 3;
pub const NUMBER_ZERO_EXPONENT: i32 = i32::MIN;

pub const MANTISSA_SMALL_MIN: u64 = 1_000_000_000_000_000;
pub const MANTISSA_SMALL_MAX: u64 = 9_999_999_999_999_999;
pub const MANTISSA_LARGE_MIN: u64 = 1_000_000_000_000_000_000;
pub const MANTISSA_LARGE_MAX: u64 = 9_999_999_999_999_999_999;

pub const fn log_ten(mut value: u64) -> Option<i32> {
    let mut log = 0;
    while value >= 10 {
        if !value.is_multiple_of(10) {
            return None;
        }
        value /= 10;
        log += 1;
    }
    if value == 1 { Some(log) } else { None }
}

pub const fn is_power_of_ten(value: u64) -> bool {
    log_ten(value).is_some()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MantissaScale {
    Small,
    LargeLegacy,
    Large320,
    Large330,
}

impl MantissaScale {
    #[allow(non_upper_case_globals)]
    pub const Large: Self = Self::Large330;

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Small => "small",
            Self::LargeLegacy => "largeLegacy",
            Self::Large320 => "large320",
            Self::Large330 => "large330",
        }
    }
}

impl std::fmt::Display for MantissaScale {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MantissaRange {
    pub min: u64,
    pub max: u64,
    pub log: i32,
    pub scale: MantissaScale,
}

impl MantissaRange {
    pub const fn new(scale: MantissaScale) -> Self {
        let min = mantissa_range_min(scale);

        Self {
            min,
            max: mantissa_range_max(scale),
            log: mantissa_range_log(scale),
            scale,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoundingMode {
    ToNearest,
    TowardsZero,
    Downward,
    Upward,
}

thread_local! {
    static CURRENT_MANTISSA_SCALE: Cell<MantissaScale> = const { Cell::new(MantissaScale::Large) };
    static CURRENT_ROUNDING_MODE: Cell<RoundingMode> = const { Cell::new(RoundingMode::ToNearest) };
}

pub fn get_mantissa_scale() -> MantissaScale {
    CURRENT_MANTISSA_SCALE.with(Cell::get)
}

pub fn set_mantissa_scale(scale: MantissaScale) {
    CURRENT_MANTISSA_SCALE.with(|current| current.set(scale));
}

pub fn get_rounding_mode() -> RoundingMode {
    CURRENT_ROUNDING_MODE.with(Cell::get)
}

pub fn set_rounding_mode(mode: RoundingMode) -> RoundingMode {
    CURRENT_ROUNDING_MODE.with(|current| current.replace(mode))
}

pub fn current_mantissa_range() -> MantissaRange {
    MantissaRange::new(get_mantissa_scale())
}

pub const fn mantissa_range_min(scale: MantissaScale) -> u64 {
    match scale {
        MantissaScale::Small => MANTISSA_SMALL_MIN,
        MantissaScale::LargeLegacy | MantissaScale::Large320 | MantissaScale::Large330 => {
            MANTISSA_LARGE_MIN
        }
    }
}

pub const fn mantissa_range_max(scale: MantissaScale) -> u64 {
    match scale {
        MantissaScale::Small => MANTISSA_SMALL_MAX,
        MantissaScale::LargeLegacy | MantissaScale::Large320 | MantissaScale::Large330 => {
            MANTISSA_LARGE_MAX
        }
    }
}

pub const fn mantissa_range_log(scale: MantissaScale) -> i32 {
    match scale {
        MantissaScale::Small => 15,
        MantissaScale::LargeLegacy | MantissaScale::Large320 | MantissaScale::Large330 => 18,
    }
}

pub const fn signed_external_mantissa_bounds(scale: MantissaScale) -> (i64, i64) {
    match scale {
        MantissaScale::Small => (-(MANTISSA_SMALL_MAX as i64), MANTISSA_SMALL_MAX as i64),
        MantissaScale::LargeLegacy | MantissaScale::Large320 | MantissaScale::Large330 => {
            (-NUMBER_MAX_REP, NUMBER_MAX_REP)
        }
    }
}

pub const fn external_mantissa_in_range(scale: MantissaScale, value: i64) -> bool {
    let (min, max) = signed_external_mantissa_bounds(scale);
    value >= min && value <= max
}

const fn cusp_rounding_320_enabled(scale: MantissaScale) -> bool {
    matches!(scale, MantissaScale::Large320 | MantissaScale::Large330)
}

const fn cusp_rounding_330_enabled(scale: MantissaScale) -> bool {
    matches!(scale, MantissaScale::Large330)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NumberParts {
    pub negative: bool,
    pub mantissa: u64,
    pub exponent: i32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumberShiftExponentError {
    Overflow,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumberNormalizeError {
    ExponentOverflow,
    RequiresRounding,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumberArithmeticError {
    Overflow,
    DivideByZero,
}

impl NumberParts {
    pub const fn zero() -> Self {
        Self {
            negative: false,
            mantissa: 0,
            exponent: NUMBER_ZERO_EXPONENT,
        }
    }

    pub const fn min(scale: MantissaScale) -> Self {
        Self {
            negative: false,
            mantissa: mantissa_range_min(scale),
            exponent: NUMBER_MIN_EXPONENT,
        }
    }

    pub const fn max(scale: MantissaScale) -> Self {
        let mantissa = mantissa_range_max(scale);
        Self {
            negative: false,
            mantissa: if mantissa > NUMBER_MAX_REP as u64 {
                NUMBER_MAX_REP as u64
            } else {
                mantissa
            },
            exponent: NUMBER_MAX_EXPONENT,
        }
    }

    pub const fn lowest(scale: MantissaScale) -> Self {
        let mantissa = mantissa_range_max(scale);
        Self {
            negative: true,
            mantissa: if mantissa > NUMBER_MAX_REP as u64 {
                NUMBER_MAX_REP as u64
            } else {
                mantissa
            },
            exponent: NUMBER_MAX_EXPONENT,
        }
    }

    pub const fn unchecked(negative: bool, mantissa: u64, exponent: i32) -> Self {
        Self {
            negative,
            mantissa,
            exponent,
        }
    }

    pub const fn one_small() -> Self {
        Self {
            negative: false,
            mantissa: MANTISSA_SMALL_MIN,
            exponent: -mantissa_range_log(MantissaScale::Small),
        }
    }

    pub const fn one_large() -> Self {
        Self {
            negative: false,
            mantissa: MANTISSA_LARGE_MIN,
            exponent: -mantissa_range_log(MantissaScale::Large),
        }
    }

    pub const fn one(scale: MantissaScale) -> Self {
        match scale {
            MantissaScale::Small => Self::one_small(),
            MantissaScale::LargeLegacy | MantissaScale::Large320 | MantissaScale::Large330 => {
                Self::one_large()
            }
        }
    }

    pub fn from_i64(mantissa: i64) -> Self {
        Self::try_from_external_parts(mantissa, 0, get_mantissa_scale())
            .expect("NumberParts from_i64 should not overflow")
    }

    pub fn from_i64_and_exponent(mantissa: i64, exponent: i32) -> Self {
        Self::try_from_external_parts(mantissa, exponent, get_mantissa_scale())
            .expect("NumberParts from_i64_and_exponent should not overflow")
    }

    pub const fn isnormal(self, scale: MantissaScale) -> bool {
        self.is_normalized(scale)
    }

    pub const fn is_normalized(self, scale: MantissaScale) -> bool {
        if self.mantissa == 0 {
            return !self.negative && self.exponent == NUMBER_ZERO_EXPONENT;
        }

        let min = mantissa_range_min(scale);
        let max = mantissa_range_max(scale);

        self.mantissa >= min
            && self.mantissa <= max
            && (self.mantissa <= NUMBER_MAX_REP as u64 || self.mantissa.is_multiple_of(10))
            && self.exponent >= NUMBER_MIN_EXPONENT
            && self.exponent <= NUMBER_MAX_EXPONENT
    }

    pub fn normalize_to_range(
        self,
        min_mantissa: u64,
        max_mantissa: u64,
    ) -> Result<Self, NumberNormalizeError> {
        if self.mantissa == 0 {
            return Ok(Self::zero());
        }

        let mut mantissa = self.mantissa as u128;
        let mut exponent = self.exponent;
        let min_mantissa = min_mantissa as u128;
        let max_mantissa = max_mantissa as u128;

        while mantissa < min_mantissa && exponent > NUMBER_MIN_EXPONENT {
            mantissa = mantissa
                .checked_mul(10)
                .ok_or(NumberNormalizeError::RequiresRounding)?;
            exponent -= 1;
        }

        while mantissa > max_mantissa {
            if exponent >= NUMBER_MAX_EXPONENT {
                return Err(NumberNormalizeError::ExponentOverflow);
            }
            if !mantissa.is_multiple_of(10) {
                return Err(NumberNormalizeError::RequiresRounding);
            }
            mantissa /= 10;
            exponent += 1;
        }

        if exponent < NUMBER_MIN_EXPONENT || mantissa < min_mantissa {
            return Ok(Self::zero());
        }

        let mantissa =
            u64::try_from(mantissa).map_err(|_| NumberNormalizeError::RequiresRounding)?;
        Ok(Self {
            negative: self.negative && mantissa != 0,
            mantissa,
            exponent,
        })
    }

    pub fn try_normalize_exact(self, scale: MantissaScale) -> Result<Self, NumberNormalizeError> {
        self.normalize_to_range(mantissa_range_min(scale), mantissa_range_max(scale))
    }

    pub fn try_normalize_exact_to_range(
        self,
        min_mantissa: u64,
        max_mantissa: u64,
    ) -> Result<Self, NumberNormalizeError> {
        self.normalize_to_range(min_mantissa, max_mantissa)
    }

    pub fn try_from_external_parts(
        mantissa: i64,
        exponent: i32,
        scale: MantissaScale,
    ) -> Result<Self, NumberNormalizeError> {
        let negative = mantissa < 0;
        let mantissa = external_to_internal_mantissa(mantissa);
        if mantissa <= NUMBER_MAX_REP as u64 {
            return Self::unchecked(negative, mantissa, exponent).try_normalize_exact(scale);
        }

        // INT64_MIN is the only external i64 whose magnitude exceeds Number::rep.
        // Mirror rippled Number(rep, exponent): externalToInternal then doNormalize.
        Self::normalize_arithmetic_parts(
            negative,
            u128::from(mantissa),
            exponent,
            mantissa_range_min(scale),
            mantissa_range_max(scale),
            scale,
        )
        .map_err(|_| NumberNormalizeError::ExponentOverflow)
    }

    pub fn external_parts(self) -> Result<(i64, i32), NumberNormalizeError> {
        if self.mantissa == 0 {
            return Ok((0, self.exponent));
        }

        let mut mantissa = self.mantissa;
        let mut exponent = self.exponent;

        if mantissa > NUMBER_MAX_REP as u64 {
            if !mantissa.is_multiple_of(10) {
                return Err(NumberNormalizeError::RequiresRounding);
            }
            mantissa /= 10;
            exponent = exponent
                .checked_add(1)
                .ok_or(NumberNormalizeError::ExponentOverflow)?;
        }

        let mantissa =
            i64::try_from(mantissa).map_err(|_| NumberNormalizeError::RequiresRounding)?;
        let signed = if self.negative { -mantissa } else { mantissa };
        Ok((signed, exponent))
    }

    pub const fn signum(self) -> i8 {
        if self.negative {
            -1
        } else if self.mantissa == 0 {
            0
        } else {
            1
        }
    }

    pub fn compare(self, other: Self) -> Ordering {
        if self.negative != other.negative {
            return if self.negative {
                Ordering::Less
            } else {
                Ordering::Greater
            };
        }

        if self.mantissa == 0 {
            return if other.mantissa > 0 {
                Ordering::Less
            } else {
                Ordering::Equal
            };
        }

        if other.mantissa == 0 {
            return Ordering::Greater;
        }

        if self.exponent != other.exponent {
            return if self.exponent > other.exponent {
                if self.negative {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            } else if self.negative {
                Ordering::Greater
            } else {
                Ordering::Less
            };
        }

        // When both values share the same sign and exponent, compare
        // mantissas directly. For negative numbers, a larger mantissa means
        // a MORE negative (lesser) value, so the comparison reverses.
        if self.negative {
            other.mantissa.cmp(&self.mantissa)
        } else {
            self.mantissa.cmp(&other.mantissa)
        }
    }

    pub fn shift_exponent(
        self,
        exponent_delta: i32,
        scale: MantissaScale,
    ) -> Result<Self, NumberShiftExponentError> {
        debug_assert!(self.is_normalized(scale));

        let Some(new_exponent) = self.exponent.checked_add(exponent_delta) else {
            return Err(NumberShiftExponentError::Overflow);
        };

        if new_exponent >= NUMBER_MAX_EXPONENT {
            return Err(NumberShiftExponentError::Overflow);
        }

        if new_exponent < NUMBER_MIN_EXPONENT {
            return Ok(Self::zero());
        }

        Ok(Self {
            exponent: new_exponent,
            ..self
        })
    }

    pub fn truncate(self, scale: MantissaScale) -> Self {
        if self.exponent >= 0 || self.mantissa == 0 {
            return self
                .normalize_to_range(mantissa_range_min(scale), mantissa_range_max(scale))
                .unwrap_or(self);
        }

        let mut mantissa = self.mantissa;
        let mut exponent = self.exponent;
        while exponent < 0 && mantissa != 0 {
            exponent += 1;
            mantissa /= 10;
        }

        Self {
            negative: self.negative && mantissa != 0,
            mantissa,
            exponent,
        }
        .normalize_to_range(mantissa_range_min(scale), mantissa_range_max(scale))
        .unwrap_or(Self {
            negative: self.negative && mantissa != 0,
            mantissa,
            exponent,
        })
    }

    /// Prefix-style increment equivalent to reference `operator++()`.
    pub fn increment(&mut self) -> &mut Self {
        *self += Self::one(get_mantissa_scale());
        self
    }

    /// Postfix-style increment equivalent to reference `operator++(int)`.
    pub fn post_increment(&mut self) -> Self {
        let previous = *self;
        self.increment();
        previous
    }

    /// Prefix-style decrement equivalent to reference `operator--()`.
    pub fn decrement(&mut self) -> &mut Self {
        *self -= Self::one(get_mantissa_scale());
        self
    }

    /// Postfix-style decrement equivalent to reference `operator--(int)`.
    pub fn post_decrement(&mut self) -> Self {
        let previous = *self;
        self.decrement();
        previous
    }

    pub fn try_add(self, other: Self) -> Result<Self, NumberArithmeticError> {
        let mut value = self;
        value.try_add_assign(other)?;
        Ok(value)
    }

    pub fn try_sub(self, other: Self) -> Result<Self, NumberArithmeticError> {
        let mut value = self;
        value.try_sub_assign(other)?;
        Ok(value)
    }

    pub fn try_mul(self, other: Self) -> Result<Self, NumberArithmeticError> {
        let mut value = self;
        value.try_mul_assign(other)?;
        Ok(value)
    }

    pub fn try_div(self, other: Self) -> Result<Self, NumberArithmeticError> {
        let mut value = self;
        value.try_div_assign(other)?;
        Ok(value)
    }

    pub fn try_add_assign(&mut self, other: Self) -> Result<(), NumberArithmeticError> {
        let zero = Self::zero();
        if other == zero {
            return Ok(());
        }
        if *self == zero {
            *self = other;
            return Ok(());
        }
        if *self == -other {
            *self = zero;
            return Ok(());
        }

        let scale = get_mantissa_scale();
        let min_mantissa = mantissa_range_min(scale);
        let max_mantissa = mantissa_range_max(scale);

        let mut xn = self.negative;
        let mut xm = u128::from(self.mantissa);
        let mut xe = self.exponent;

        let yn = other.negative;
        let mut ym = u128::from(other.mantissa);
        let mut ye = other.exponent;

        let mut guard = ArithmeticGuard::default();
        let rep_limit = if cusp_rounding_330_enabled(scale) {
            NUMBER_MAX_REP_UP
        } else {
            NUMBER_MAX_REP as u64
        };
        let upper_limit = u128::from(min_mantissa) * 1_000;

        // Pinned Number::operator+= uses a three-stage exponent alignment for
        // fixCleanup3_3: first discard exact trailing zeroes, then expand the
        // smaller mantissa (bounded to three guard digits beyond the range),
        // and only then discard significant digits into the Guard.  The older
        // modes intentionally retain the legacy shrink-only behavior.
        let adjust = |guard: &mut ArithmeticGuard,
                      expand_m: &mut u128,
                      expand_e: &mut i32,
                      shrink_m: &mut u128,
                      shrink_e: &mut i32|
         -> Result<(), NumberArithmeticError> {
            if cusp_rounding_330_enabled(scale) {
                while *shrink_e < *expand_e && *shrink_m % 10 == 0 {
                    guard.push((*shrink_m % 10) as u8);
                    *shrink_m /= 10;
                    *shrink_e = shrink_e
                        .checked_add(1)
                        .ok_or(NumberArithmeticError::Overflow)?;
                }
                while *shrink_e < *expand_e
                    && *expand_e > NUMBER_MIN_EXPONENT
                    && *expand_m < upper_limit
                {
                    *expand_m = expand_m
                        .checked_mul(10)
                        .ok_or(NumberArithmeticError::Overflow)?;
                    *expand_e = expand_e
                        .checked_sub(1)
                        .ok_or(NumberArithmeticError::Overflow)?;
                }
            }
            while *shrink_e < *expand_e {
                guard.push((*shrink_m % 10) as u8);
                *shrink_m /= 10;
                *shrink_e = shrink_e
                    .checked_add(1)
                    .ok_or(NumberArithmeticError::Overflow)?;
            }
            Ok(())
        };
        if xe < ye {
            if xn {
                guard.set_negative();
            }
            adjust(&mut guard, &mut ym, &mut ye, &mut xm, &mut xe)?;
        } else if xe > ye {
            if yn {
                guard.set_negative();
            }
            adjust(&mut guard, &mut xm, &mut xe, &mut ym, &mut ye)?;
        } else if cusp_rounding_330_enabled(scale) && ((xm < ym && xn) || (ym < xm && yn)) {
            guard.set_negative();
        }

        if xn == yn {
            xm = xm.checked_add(ym).ok_or(NumberArithmeticError::Overflow)?;
            if !cusp_rounding_330_enabled(scale) {
                if xm > u128::from(max_mantissa) || xm > u128::from(rep_limit) {
                    guard.push((xm % 10) as u8);
                    xm /= 10;
                    xe = xe.checked_add(1).ok_or(NumberArithmeticError::Overflow)?;
                }
                guard.do_round_up(&mut xn, &mut xm, &mut xe, min_mantissa, max_mantissa, scale)?;
            }
        } else {
            if xm > ym {
                xm -= ym;
            } else {
                xm = ym - xm;
                xe = ye;
                xn = yn;
            }

            if cusp_rounding_330_enabled(scale) {
                while xm < upper_limit && !guard.empty() {
                    xm = xm.checked_mul(10).ok_or(NumberArithmeticError::Overflow)?;
                    xm = xm.saturating_sub(u128::from(guard.pop()));
                    xe = xe.checked_sub(1).ok_or(NumberArithmeticError::Overflow)?;
                }
            } else {
                while xm < u128::from(min_mantissa)
                    && xm.saturating_mul(10) <= u128::from(rep_limit)
                {
                    xm *= 10;
                    xm = xm.saturating_sub(u128::from(guard.pop()));
                    xe = xe.checked_sub(1).ok_or(NumberArithmeticError::Overflow)?;
                }
            }
            guard.do_round_down(&mut xn, &mut xm, &mut xe, min_mantissa, max_mantissa, scale);
        }

        *self = Self::normalize_arithmetic_parts_with_dropped(
            xn,
            xm,
            xe,
            min_mantissa,
            max_mantissa,
            scale,
            cusp_rounding_330_enabled(scale) && !guard.empty(),
        )?;
        Ok(())
    }

    pub fn try_sub_assign(&mut self, other: Self) -> Result<(), NumberArithmeticError> {
        self.try_add_assign(-other)
    }

    pub fn try_mul_assign(&mut self, other: Self) -> Result<(), NumberArithmeticError> {
        let zero = Self::zero();
        if *self == zero {
            return Ok(());
        }
        if other == zero {
            *self = zero;
            return Ok(());
        }

        let scale = get_mantissa_scale();
        let min_mantissa = mantissa_range_min(scale);
        let max_mantissa = mantissa_range_max(scale);

        let mut zm = u128::from(self.mantissa)
            .checked_mul(u128::from(other.mantissa))
            .ok_or(NumberArithmeticError::Overflow)?;
        let mut ze = self
            .exponent
            .checked_add(other.exponent)
            .ok_or(NumberArithmeticError::Overflow)?;
        let mut zn = self.negative ^ other.negative;

        let mut guard = ArithmeticGuard::default();
        if zn {
            guard.set_negative();
        }

        let rep_limit = if cusp_rounding_330_enabled(scale) {
            NUMBER_MAX_REP_UP
        } else {
            NUMBER_MAX_REP as u64
        };
        while zm > u128::from(max_mantissa) || zm > u128::from(rep_limit) {
            guard.push((zm % 10) as u8);
            zm /= 10;
            ze = ze.checked_add(1).ok_or(NumberArithmeticError::Overflow)?;
        }

        guard.do_round_up(&mut zn, &mut zm, &mut ze, min_mantissa, max_mantissa, scale)?;
        // Pinned operator*= invokes normalize(g), which reuses only the
        // Guard's mantissa range/amendment mode; unlike operator+= it does not
        // propagate the old guard's trailing-digit bit into doNormalize.
        *self = Self::finish_arithmetic_result(zn, zm, ze, scale)?;
        Ok(())
    }

    pub fn try_div_assign(&mut self, other: Self) -> Result<(), NumberArithmeticError> {
        let zero = Self::zero();
        if other == zero {
            return Err(NumberArithmeticError::DivideByZero);
        }
        if *self == zero {
            return Ok(());
        }

        let scale = get_mantissa_scale();
        let min_mantissa = mantissa_range_min(scale);
        let max_mantissa = mantissa_range_max(scale);
        let cusp_fix = cusp_rounding_320_enabled(scale);

        // Stage 1: initial division with factor of 10^17
        const FACTOR_EXPONENT: i32 = 17;
        let factor: u128 = 100_000_000_000_000_000; // 10^17
        let numerator = u128::from(self.mantissa)
            .checked_mul(factor)
            .ok_or(NumberArithmeticError::Overflow)?;
        let dm = u128::from(other.mantissa);

        let mut zm = numerator / dm;
        let mut ze = self
            .exponent
            .checked_sub(other.exponent)
            .and_then(|v| v.checked_sub(FACTOR_EXPONENT))
            .ok_or(NumberArithmeticError::Overflow)?;
        let zn = self.negative ^ other.negative;
        let mut dropped = false;

        if scale != MantissaScale::Small {
            // Stage 2: if there's a remainder, use correctionFactor = 10^5
            const CORRECTION_EXPONENT: i32 = 5;
            let correction_factor: u128 = 100_000; // 10^5
            let remainder = numerator % dm;
            if remainder != 0 {
                let partial_numerator = remainder * correction_factor;
                let correction = partial_numerator / dm;

                if correction != 0 {
                    zm = zm
                        .checked_mul(correction_factor)
                        .ok_or(NumberArithmeticError::Overflow)?;
                    ze = ze
                        .checked_sub(CORRECTION_EXPONENT)
                        .ok_or(NumberArithmeticError::Overflow)?;
                    zm = zm
                        .checked_add(correction)
                        .ok_or(NumberArithmeticError::Overflow)?;
                }

                // Stage 3: flag trailing remainder for cusp rounding
                if cusp_fix {
                    dropped = !partial_numerator.is_multiple_of(dm);
                }
            }
        }

        *self = Self::normalize_arithmetic_parts_with_dropped(
            zn,
            zm,
            ze,
            min_mantissa,
            max_mantissa,
            scale,
            dropped,
        )?;
        Ok(())
    }

    pub fn try_to_i64(self) -> Result<i64, NumberArithmeticError> {
        let (external_mantissa, mut offset) = self
            .external_parts()
            .map_err(|_| NumberArithmeticError::Overflow)?;
        if external_mantissa == 0 {
            return Ok(0);
        }

        let mut guard = ArithmeticGuard::default();
        let mut drops = external_mantissa;
        if self.negative {
            guard.set_negative();
            drops = drops.checked_neg().ok_or(NumberArithmeticError::Overflow)?;
        }

        while offset < 0 {
            guard.push((drops % 10) as u8);
            drops /= 10;
            offset += 1;
        }
        while offset > 0 {
            if drops > NUMBER_MAX_REP / 10 {
                return Err(NumberArithmeticError::Overflow);
            }
            drops *= 10;
            offset -= 1;
        }

        guard.do_round_i64(&mut drops)?;
        Ok(drops)
    }

    fn normalize_arithmetic_parts(
        negative: bool,
        mantissa: u128,
        exponent: i32,
        min_mantissa: u64,
        max_mantissa: u64,
        scale: MantissaScale,
    ) -> Result<Self, NumberArithmeticError> {
        Self::normalize_arithmetic_parts_with_dropped(
            negative,
            mantissa,
            exponent,
            min_mantissa,
            max_mantissa,
            scale,
            false,
        )
    }

    fn normalize_arithmetic_parts_with_dropped(
        mut negative: bool,
        mut mantissa: u128,
        mut exponent: i32,
        min_mantissa: u64,
        max_mantissa: u64,
        scale: MantissaScale,
        dropped: bool,
    ) -> Result<Self, NumberArithmeticError> {
        if mantissa == 0 {
            return Ok(Self::zero());
        }
        let rep_limit = if cusp_rounding_330_enabled(scale) {
            NUMBER_MAX_REP_UP
        } else {
            NUMBER_MAX_REP as u64
        };

        while mantissa < u128::from(min_mantissa) && exponent > NUMBER_MIN_EXPONENT {
            mantissa = mantissa
                .checked_mul(10)
                .ok_or(NumberArithmeticError::Overflow)?;
            exponent -= 1;
        }

        let mut guard = ArithmeticGuard::default();
        if negative {
            guard.set_negative();
        }
        if dropped {
            guard.has_extra = true;
        }

        while mantissa > u128::from(max_mantissa) {
            if exponent >= NUMBER_MAX_EXPONENT {
                return Err(NumberArithmeticError::Overflow);
            }
            guard.push((mantissa % 10) as u8);
            mantissa /= 10;
            exponent += 1;
        }

        if exponent < NUMBER_MIN_EXPONENT || mantissa < u128::from(min_mantissa) {
            return Ok(Self::zero());
        }

        if mantissa > u128::from(rep_limit) {
            if exponent >= NUMBER_MAX_EXPONENT {
                return Err(NumberArithmeticError::Overflow);
            }
            guard.push((mantissa % 10) as u8);
            mantissa /= 10;
            exponent += 1;
        }

        guard.do_round_up(
            &mut negative,
            &mut mantissa,
            &mut exponent,
            min_mantissa,
            max_mantissa,
            scale,
        )?;

        Self::finish_arithmetic_result(negative, mantissa, exponent, scale)
    }

    fn finish_arithmetic_result(
        negative: bool,
        mantissa: u128,
        exponent: i32,
        scale: MantissaScale,
    ) -> Result<Self, NumberArithmeticError> {
        if mantissa == 0 || exponent < NUMBER_MIN_EXPONENT {
            return Ok(Self::zero());
        }
        if exponent > NUMBER_MAX_EXPONENT {
            return Err(NumberArithmeticError::Overflow);
        }

        let mantissa = u64::try_from(mantissa).map_err(|_| NumberArithmeticError::Overflow)?;
        let result = Self {
            negative: negative && mantissa != 0,
            mantissa,
            exponent,
        };
        if result.is_normalized(scale) {
            Ok(result)
        } else {
            Self::normalize_arithmetic_parts(
                result.negative,
                u128::from(result.mantissa),
                result.exponent,
                mantissa_range_min(scale),
                mantissa_range_max(scale),
                scale,
            )
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct ArithmeticGuard {
    digits: u64,
    has_extra: bool,
    negative: bool,
}

impl ArithmeticGuard {
    fn set_negative(&mut self) {
        self.negative = true;
    }

    fn push(&mut self, digit: u8) {
        self.has_extra = self.has_extra || ((self.digits & 0xF) != 0);
        self.digits >>= 4;
        self.digits |= u64::from(digit & 0x0F) << 60;
    }

    fn pop(&mut self) -> u8 {
        let digit = ((self.digits & 0xF000_0000_0000_0000) >> 60) as u8;
        self.digits <<= 4;
        digit
    }

    fn empty(&self) -> bool {
        self.digits == 0 && !self.has_extra
    }

    fn round(&self) -> i8 {
        match get_rounding_mode() {
            RoundingMode::TowardsZero => -1,
            RoundingMode::Downward => {
                if self.negative && (self.digits > 0 || self.has_extra) {
                    1
                } else {
                    -1
                }
            }
            RoundingMode::Upward => {
                if self.negative {
                    -1
                } else if self.digits > 0 || self.has_extra {
                    1
                } else {
                    -1
                }
            }
            RoundingMode::ToNearest => {
                let half = 0x5000_0000_0000_0000;
                if self.digits > half {
                    1
                } else if self.digits < half {
                    -1
                } else if self.has_extra {
                    1
                } else {
                    0
                }
            }
        }
    }

    fn bring_into_range(
        &self,
        negative: &mut bool,
        mantissa: &mut u128,
        exponent: &mut i32,
        min_mantissa: u64,
        scale: MantissaScale,
    ) {
        if *mantissa < u128::from(min_mantissa)
            && (!cusp_rounding_330_enabled(scale) || *mantissa != 0)
        {
            *mantissa *= 10;
            *exponent -= 1;
        }
        if *exponent < NUMBER_MIN_EXPONENT || (cusp_rounding_330_enabled(scale) && *mantissa == 0) {
            *negative = false;
            *mantissa = 0;
            *exponent = NUMBER_ZERO_EXPONENT;
        }
    }

    fn do_round_up(
        &mut self,
        negative: &mut bool,
        mantissa: &mut u128,
        exponent: &mut i32,
        min_mantissa: u64,
        max_mantissa: u64,
        scale: MantissaScale,
    ) -> Result<(), NumberArithmeticError> {
        if cusp_rounding_330_enabled(scale)
            && *mantissa >= u128::from(NUMBER_MAX_REP as u64)
            && *mantissa < u128::from(NUMBER_MAX_REP_UP)
        {
            if *mantissa % 10 < 9 {
                let rounded = self.round();
                if rounded == 1
                    || (rounded == 0 && *mantissa == u128::from(NUMBER_MAX_REP as u64 + 1))
                {
                    *mantissa += 1;
                }
            }
            let diff = *mantissa - u128::from(NUMBER_MAX_REP as u64);
            let digit = (diff * 10 / u128::from(NUMBER_MAX_REP_UP - NUMBER_MAX_REP as u64)) as u8;
            self.push(digit);
        }
        let rounded = self.round();
        if rounded == 1 || (rounded == 0 && (*mantissa & 1) == 1) {
            let safe_to_increment = |mantissa: u128| {
                mantissa < u128::from(max_mantissa) && mantissa < u128::from(NUMBER_MAX_REP as u64)
            };

            if cusp_rounding_320_enabled(scale) {
                if safe_to_increment(*mantissa) {
                    *mantissa += 1;
                } else if cusp_rounding_330_enabled(scale)
                    && *mantissa > u128::from(NUMBER_MAX_REP as u64)
                    && *mantissa < u128::from(NUMBER_MAX_REP_UP)
                {
                    *mantissa = u128::from(NUMBER_MAX_REP_UP);
                } else {
                    self.push((*mantissa % 10) as u8);
                    *mantissa /= 10;
                    *exponent = exponent
                        .checked_add(1)
                        .ok_or(NumberArithmeticError::Overflow)?;
                    if !safe_to_increment(*mantissa) {
                        return Err(NumberArithmeticError::Overflow);
                    }
                    self.do_round_up(
                        negative,
                        mantissa,
                        exponent,
                        min_mantissa,
                        max_mantissa,
                        scale,
                    )?;
                    return Ok(());
                }
            } else {
                *mantissa = mantissa
                    .checked_add(1)
                    .ok_or(NumberArithmeticError::Overflow)?;
                if *mantissa > u128::from(max_mantissa)
                    || *mantissa > u128::from(NUMBER_MAX_REP as u64)
                {
                    *mantissa /= 10;
                    *exponent = exponent
                        .checked_add(1)
                        .ok_or(NumberArithmeticError::Overflow)?;
                }
            }
        } else if cusp_rounding_330_enabled(scale)
            && *mantissa > u128::from(NUMBER_MAX_REP as u64)
            && *mantissa < u128::from(NUMBER_MAX_REP_UP)
        {
            *mantissa = u128::from(NUMBER_MAX_REP as u64);
        }
        self.bring_into_range(negative, mantissa, exponent, min_mantissa, scale);
        if *exponent > NUMBER_MAX_EXPONENT {
            return Err(NumberArithmeticError::Overflow);
        }
        Ok(())
    }

    fn do_round_down(
        &self,
        negative: &mut bool,
        mantissa: &mut u128,
        exponent: &mut i32,
        min_mantissa: u64,
        max_mantissa: u64,
        scale: MantissaScale,
    ) {
        let rounded = self.round();
        if cusp_rounding_330_enabled(scale) {
            if !self.empty() {
                *mantissa -= 1;
            }
        } else if rounded == 1 || (rounded == 0 && (*mantissa & 1) == 1) {
            *mantissa -= 1;
            if *mantissa < u128::from(min_mantissa) {
                *mantissa *= 10;
                *exponent -= 1;
            }
        }
        let _ = (rounded, max_mantissa);
        self.bring_into_range(negative, mantissa, exponent, min_mantissa, scale);
    }

    fn do_round_i64(&self, drops: &mut i64) -> Result<(), NumberArithmeticError> {
        let rounded = self.round();
        if rounded == 1 || (rounded == 0 && (*drops & 1) == 1) {
            if *drops == NUMBER_MAX_REP {
                return Err(NumberArithmeticError::Overflow);
            }
            *drops += 1;
        }
        if self.negative {
            *drops = drops.checked_neg().ok_or(NumberArithmeticError::Overflow)?;
        }
        Ok(())
    }
}

impl Neg for NumberParts {
    type Output = Self;

    fn neg(self) -> Self::Output {
        if self.mantissa == 0 {
            Self::zero()
        } else {
            Self {
                negative: !self.negative,
                ..self
            }
        }
    }
}

impl AddAssign for NumberParts {
    fn add_assign(&mut self, rhs: Self) {
        self.try_add_assign(rhs).expect(
            "NumberParts addition should preserve the reference implementation overflow behavior",
        );
    }
}

impl Add for NumberParts {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl SubAssign for NumberParts {
    fn sub_assign(&mut self, rhs: Self) {
        self.try_sub_assign(rhs)
            .expect("NumberParts subtraction should preserve the reference implementation overflow behavior");
    }
}

impl Sub for NumberParts {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl MulAssign for NumberParts {
    fn mul_assign(&mut self, rhs: Self) {
        self.try_mul_assign(rhs)
            .expect("NumberParts multiplication should preserve the reference implementation overflow behavior");
    }
}

impl Mul for NumberParts {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl DivAssign for NumberParts {
    fn div_assign(&mut self, rhs: Self) {
        self.try_div_assign(rhs).expect(
            "NumberParts division should preserve the reference implementation overflow behavior",
        );
    }
}

impl Div for NumberParts {
    type Output = Self;

    fn div(mut self, rhs: Self) -> Self::Output {
        self /= rhs;
        self
    }
}

impl PartialOrd for NumberParts {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NumberParts {
    fn cmp(&self, other: &Self) -> Ordering {
        (*self).compare(*other)
    }
}

impl fmt::Display for NumberParts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&to_string(*self))
    }
}

pub const fn external_to_internal_mantissa(mantissa: i64) -> u64 {
    if mantissa >= 0 {
        mantissa as u64
    } else if mantissa >= -i64::MAX {
        (-mantissa) as u64
    } else {
        (-(mantissa as i128)) as u64
    }
}

pub fn to_string(amount: NumberParts) -> String {
    if amount == NumberParts::zero() {
        return "0".to_owned();
    }

    let mut exponent = amount.exponent;
    let mut mantissa = amount.mantissa;
    let negative = amount.negative;
    let range_log = mantissa_range_log(get_mantissa_scale());

    if exponent != 0 && (exponent < -(range_log + 10) || exponent > -(range_log - 10)) {
        while mantissa != 0 && mantissa.is_multiple_of(10) && exponent < NUMBER_MAX_EXPONENT {
            mantissa /= 10;
            exponent += 1;
        }

        let mut ret = String::with_capacity(mantissa.to_string().len() + 2 + 12);
        if negative {
            ret.push('-');
        }
        ret.push_str(&mantissa.to_string());
        ret.push('e');
        ret.push_str(&exponent.to_string());
        return ret;
    }

    debug_assert!(
        exponent + 43 > 0,
        "xrpl::to_string(NumberParts) : minimum exponent",
    );

    let pad_prefix = (range_log + 12) as usize;
    let pad_suffix = (range_log + 8) as usize;
    let raw_value = mantissa.to_string();

    let mut val = String::with_capacity(raw_value.len() + pad_prefix + pad_suffix);
    val.push_str(&"0".repeat(pad_prefix));
    val.push_str(&raw_value);
    val.push_str(&"0".repeat(pad_suffix));

    let offset = (exponent + 2 * range_log + 13) as usize;
    let bytes = val.as_bytes();

    let mut pre_from = 0usize;
    let pre_to = offset;
    let post_from = offset;
    let mut post_to = bytes.len();

    if pre_to.saturating_sub(pre_from) > pad_prefix {
        pre_from += pad_prefix;
    }

    if let Some(pos) = bytes[pre_from..pre_to].iter().position(|&c| c != b'0') {
        pre_from += pos;
    } else {
        pre_from = pre_to;
    }

    if post_to.saturating_sub(post_from) > pad_suffix {
        post_to -= pad_suffix;
    }

    if let Some(pos) = bytes[post_from..post_to].iter().rposition(|&c| c != b'0') {
        post_to = post_from + pos + 1;
    } else {
        post_to = post_from;
    }

    let mut ret = String::new();
    if negative {
        ret.push('-');
    }

    if pre_from == pre_to {
        ret.push('0');
    } else {
        ret.push_str(std::str::from_utf8(&bytes[pre_from..pre_to]).expect("ASCII digits"));
    }

    if post_to != post_from {
        ret.push('.');
        ret.push_str(std::str::from_utf8(&bytes[post_from..post_to]).expect("ASCII digits"));
    }

    ret
}

pub fn current_number_one() -> NumberParts {
    NumberParts::one(get_mantissa_scale())
}

pub fn current_number_min() -> NumberParts {
    NumberParts::min(get_mantissa_scale())
}

pub fn current_number_max() -> NumberParts {
    NumberParts::max(get_mantissa_scale())
}

pub fn current_number_lowest() -> NumberParts {
    NumberParts::lowest(get_mantissa_scale())
}

pub fn current_mantissa_min() -> u64 {
    current_mantissa_range().min
}

pub fn current_mantissa_max() -> u64 {
    current_mantissa_range().max
}

pub fn current_mantissa_log() -> i32 {
    current_mantissa_range().log
}

pub fn mantissa_scale_to_string(scale: MantissaScale) -> String {
    scale.to_string()
}

fn exact_number(value: i64, scale: MantissaScale) -> Result<NumberParts, NumberArithmeticError> {
    NumberParts::try_from_external_parts(value, 0, scale)
        .map_err(|_| NumberArithmeticError::Overflow)
}

pub fn abs_number(value: NumberParts) -> NumberParts {
    if value < NumberParts::zero() {
        -value
    } else {
        value
    }
}

pub fn squelch_number(value: NumberParts, limit: NumberParts) -> NumberParts {
    if abs_number(value) < limit {
        NumberParts::zero()
    } else {
        value
    }
}

fn gcd_u32(mut lhs: u32, mut rhs: u32) -> u32 {
    while rhs != 0 {
        let remainder = lhs % rhs;
        lhs = rhs;
        rhs = remainder;
    }
    lhs
}

fn euclidean_remainder_adjust(exponent: i32, divisor: i32) -> i32 {
    let remainder = exponent.rem_euclid(divisor);
    if remainder == 0 {
        0
    } else {
        divisor - remainder
    }
}

fn power_impl(
    f: NumberParts,
    n: u32,
    scale: MantissaScale,
) -> Result<NumberParts, NumberArithmeticError> {
    if n == 0 {
        return Ok(NumberParts::one(scale));
    }
    if n == 1 {
        return Ok(f);
    }

    let mut r = power_impl(f, n / 2, scale)?;
    let squared = r;
    r = r.try_mul(squared)?;
    if !n.is_multiple_of(2) {
        r = r.try_mul(f)?;
    }
    Ok(r)
}

pub fn power(f: NumberParts, n: u32) -> Result<NumberParts, NumberArithmeticError> {
    power_impl(f, n, get_mantissa_scale())
}

pub fn root(f: NumberParts, d: u32) -> Result<NumberParts, NumberArithmeticError> {
    let scale = get_mantissa_scale();
    let zero = NumberParts::zero();
    let one = NumberParts::one(scale);

    if f == one || d == 1 {
        return Ok(f);
    }
    if d == 0 {
        if f == -one {
            return Ok(one);
        }
        if abs_number(f) < one {
            return Ok(zero);
        }
        return Err(NumberArithmeticError::Overflow);
    }
    if f < zero && d.is_multiple_of(2) {
        return Err(NumberArithmeticError::Overflow);
    }
    if f == zero {
        return Ok(f);
    }

    let di = i32::try_from(d).map_err(|_| NumberArithmeticError::Overflow)?;

    // Scale f into the range (0, 1) such that f's exponent is a multiple of d.
    let mut e = f.exponent + mantissa_range_log(scale) + 1;
    let ex = euclidean_remainder_adjust(e, di);
    e += ex;
    let mut f = f
        .shift_exponent(-e, scale)
        .map_err(|_| NumberArithmeticError::Overflow)?;

    debug_assert!(f.is_normalized(scale));
    let mut neg = false;
    if f < zero {
        neg = true;
        f = -f;
    }

    // Quadratic least-squares curve fit of f^(1/d) in the range [0, 1].
    let to_number = |value: i128| -> Result<NumberParts, NumberArithmeticError> {
        exact_number(
            i64::try_from(value).map_err(|_| NumberArithmeticError::Overflow)?,
            scale,
        )
    };
    let di128 = i128::from(di);
    let a0 = to_number(3 * di128 * ((2 * di128 - 3) * di128 + 1))?;
    let a1 = to_number(24 * di128 * (2 * di128 - 1))?;
    let a2 = to_number(-30 * (di128 - 1) * di128)?;
    let denom = to_number((((6 * di128 + 11) * di128 + 6) * di128) + 1)?;
    let d_number = exact_number(i64::from(d), scale)?;
    let d_minus_one = exact_number(i64::from(d - 1), scale)?;

    let mut r = a2
        .try_mul(f)?
        .try_add(a1)?
        .try_mul(f)?
        .try_add(a0)?
        .try_div(denom)?;
    if neg {
        f = -f;
        r = -r;
    }

    // Newton-Raphson iteration of f^(1/d) with the initial guess r.
    let mut rm1 = NumberParts::zero();
    let mut rm2 = None;
    loop {
        let next = d_minus_one
            .try_mul(r)?
            .try_add(f.try_div(power_impl(r, d - 1, scale)?)?)?
            .try_div(d_number)?;
        if next == rm1 || rm2 == Some(next) {
            r = next;
            break;
        }
        rm2 = Some(rm1);
        rm1 = r;
        r = next;
    }

    // Return r * 10^(e/d) to reverse scaling.
    r.shift_exponent(e / di, scale)
        .map_err(|_| NumberArithmeticError::Overflow)
}

pub fn root2(f: NumberParts) -> Result<NumberParts, NumberArithmeticError> {
    let scale = get_mantissa_scale();
    let zero = NumberParts::zero();
    let one = NumberParts::one(scale);

    if f == one {
        return Ok(f);
    }
    if f < zero {
        return Err(NumberArithmeticError::Overflow);
    }
    if f == zero {
        return Ok(f);
    }

    // Scale f into the range (0, 1) such that f's exponent is a multiple of 2.
    let mut e = f.exponent + mantissa_range_log(scale) + 1;
    if e % 2 != 0 {
        e += 1;
    }
    let f = f
        .shift_exponent(-e, scale)
        .map_err(|_| NumberArithmeticError::Overflow)?;

    debug_assert!(f.is_normalized(scale));

    // Quadratic least-squares curve fit of f^(1/2) in the range [0, 1].
    let a0 = exact_number(18, scale)?;
    let a1 = exact_number(144, scale)?;
    let a2 = exact_number(-60, scale)?;
    let denom = exact_number(105, scale)?;
    let two = exact_number(2, scale)?;
    let mut r = a2
        .try_mul(f)?
        .try_add(a1)?
        .try_mul(f)?
        .try_add(a0)?
        .try_div(denom)?;

    // Newton-Raphson iteration of f^(1/2) with the initial guess r.
    let mut rm1 = NumberParts::zero();
    let mut rm2 = None;
    loop {
        let next = r.try_add(f.try_div(r)?)?.try_div(two)?;
        if next == rm1 || rm2 == Some(next) {
            r = next;
            break;
        }
        rm2 = Some(rm1);
        rm1 = r;
        r = next;
    }

    // Return r * 10^(e/2) to reverse scaling.
    r.shift_exponent(e / 2, scale)
        .map_err(|_| NumberArithmeticError::Overflow)
}

pub fn power_fraction(
    f: NumberParts,
    n: u32,
    d: u32,
) -> Result<NumberParts, NumberArithmeticError> {
    let scale = get_mantissa_scale();
    let zero = NumberParts::zero();
    let one = NumberParts::one(scale);

    if f == one {
        return Ok(f);
    }

    let g = gcd_u32(n, d);
    if g == 0 {
        return Err(NumberArithmeticError::Overflow);
    }
    if d == 0 {
        if f == -one {
            return Ok(one);
        }
        if abs_number(f) < one {
            return Ok(zero);
        }
        return Err(NumberArithmeticError::Overflow);
    }
    if n == 0 {
        return Ok(one);
    }

    let n = n / g;
    let d = d / g;
    if !n.is_multiple_of(2) && d.is_multiple_of(2) && f < zero {
        return Err(NumberArithmeticError::Overflow);
    }
    root(power_impl(f, n, scale)?, d)
}

#[derive(Debug)]
pub struct SaveNumberRoundMode {
    saved: RoundingMode,
}

impl SaveNumberRoundMode {
    pub fn new(mode: RoundingMode) -> Self {
        Self { saved: mode }
    }
}

impl Drop for SaveNumberRoundMode {
    fn drop(&mut self) {
        set_rounding_mode(self.saved);
    }
}

#[derive(Debug)]
pub struct NumberRoundModeGuard {
    _saved: SaveNumberRoundMode,
}

impl NumberRoundModeGuard {
    pub fn new(mode: RoundingMode) -> Self {
        Self {
            _saved: SaveNumberRoundMode::new(set_rounding_mode(mode)),
        }
    }
}

#[derive(Debug)]
pub struct NumberMantissaScaleGuard {
    saved: MantissaScale,
}

impl NumberMantissaScaleGuard {
    pub fn new(scale: MantissaScale) -> Self {
        let saved = get_mantissa_scale();
        set_mantissa_scale(scale);
        Self { saved }
    }
}

impl Drop for NumberMantissaScaleGuard {
    fn drop(&mut self) {
        set_mantissa_scale(self.saved);
    }
}

#[cfg(test)]
mod tests {
    use super::{
        MANTISSA_LARGE_MAX, MANTISSA_LARGE_MIN, MANTISSA_SMALL_MAX, MANTISSA_SMALL_MIN,
        MantissaRange, MantissaScale, NUMBER_MAX_EXPONENT, NUMBER_MAX_REP, NUMBER_MAX_REP_UP,
        NUMBER_MIN_EXPONENT, NUMBER_ZERO_EXPONENT, NumberMantissaScaleGuard, NumberNormalizeError,
        NumberParts, NumberRoundModeGuard, NumberShiftExponentError, RoundingMode,
        SaveNumberRoundMode, abs_number, current_mantissa_log, current_mantissa_max,
        current_mantissa_min, current_mantissa_range, current_number_lowest, current_number_max,
        current_number_min, current_number_one, external_mantissa_in_range,
        external_to_internal_mantissa, get_mantissa_scale, get_rounding_mode, is_power_of_ten,
        log_ten, mantissa_range_log, mantissa_range_max, mantissa_range_min,
        mantissa_scale_to_string, set_mantissa_scale, set_rounding_mode,
        signed_external_mantissa_bounds, squelch_number,
    };
    use std::cmp::Ordering;
    use std::thread;

    #[test]
    fn mantissa_ranges_match_current_cpp_constants() {
        assert_eq!(
            MantissaRange::new(MantissaScale::Small),
            MantissaRange {
                min: 1_000_000_000_000_000,
                max: 9_999_999_999_999_999,
                log: 15,
                scale: MantissaScale::Small,
            }
        );
        assert_eq!(
            MantissaRange::new(MantissaScale::Large),
            MantissaRange {
                min: 1_000_000_000_000_000_000,
                max: 9_999_999_999_999_999_999,
                log: 18,
                scale: MantissaScale::Large,
            }
        );
        assert_eq!(
            MantissaRange::new(MantissaScale::LargeLegacy),
            MantissaRange {
                min: 1_000_000_000_000_000_000,
                max: 9_999_999_999_999_999_999,
                log: 18,
                scale: MantissaScale::LargeLegacy,
            }
        );
    }

    #[test]
    fn cleanup_3_2_and_3_3_cusp_addition_are_distinct() {
        fn value(mantissa: i64, exponent: i32, scale: MantissaScale) -> NumberParts {
            NumberParts::try_from_external_parts(mantissa, exponent, scale).unwrap()
        }

        let lhs_legacy = value(NUMBER_MAX_REP, 0, MantissaScale::LargeLegacy);
        let rhs_legacy = value(6, -1, MantissaScale::LargeLegacy);
        let legacy_guard = NumberMantissaScaleGuard::new(MantissaScale::LargeLegacy);
        assert_eq!(
            lhs_legacy + rhs_legacy,
            value(NUMBER_MAX_REP / 10, 1, MantissaScale::LargeLegacy)
        );
        drop(legacy_guard);

        let lhs_320 = value(NUMBER_MAX_REP, 0, MantissaScale::Large320);
        let rhs_320 = value(6, -1, MantissaScale::Large320);
        let v320_guard = NumberMantissaScaleGuard::new(MantissaScale::Large320);
        assert_eq!(
            lhs_320 + rhs_320,
            value((NUMBER_MAX_REP / 10) + 1, 1, MantissaScale::Large320)
        );
        drop(v320_guard);

        let lhs_330 = value(NUMBER_MAX_REP, 0, MantissaScale::Large330);
        let rhs_330 = value(6, -1, MantissaScale::Large330);
        let _v330_guard = NumberMantissaScaleGuard::new(MantissaScale::Large330);
        assert_eq!(lhs_330 + rhs_330, lhs_330);
    }

    #[test]
    fn cleanup_3_3_cusp_normalization_and_subtraction_match_pinned_boundaries() {
        let scale = MantissaScale::Large330;
        let min = mantissa_range_min(scale);
        let max = mantissa_range_max(scale);
        let normalize = |mantissa: u128| {
            NumberParts::normalize_arithmetic_parts(false, mantissa, 0, min, max, scale).unwrap()
        };
        let one = NumberParts::try_from_external_parts(1, 0, scale).unwrap();
        let three = NumberParts::try_from_external_parts(3, 0, scale).unwrap();
        let guard = NumberMantissaScaleGuard::new(scale);

        let below_midpoint = normalize(NUMBER_MAX_REP as u128 + 1);
        assert_eq!(below_midpoint.mantissa, NUMBER_MAX_REP as u64);
        assert_eq!(below_midpoint - one, normalize(NUMBER_MAX_REP as u128 - 1));
        assert_eq!(
            below_midpoint - three,
            normalize(NUMBER_MAX_REP as u128 - 3)
        );

        let above_midpoint = normalize(NUMBER_MAX_REP_UP as u128 - 1);
        assert_eq!(above_midpoint.mantissa, NUMBER_MAX_REP_UP);
        assert_eq!(
            above_midpoint - one,
            normalize(((NUMBER_MAX_REP / 10) + 1) as u128 * 10)
        );
        assert_eq!(above_midpoint - three, normalize(NUMBER_MAX_REP as u128));
        drop(guard);
    }

    #[test]
    fn cleanup_3_3_operator_differentials_match_pinned_all_rounding_modes() {
        let _scale = NumberMantissaScaleGuard::new(MantissaScale::Large330);
        let unit = NumberParts::unchecked(false, 1_000_000_000_000_000_000, 0);
        let distant = NumberParts::unchecked(false, 1_234_567_890_123_456_789, -22);
        let exact_zero_tail = NumberParts::unchecked(false, 1_000_000_000_000_000_000, -20);
        let cusp = NumberParts::unchecked(false, NUMBER_MAX_REP as u64, 0);
        let factor = NumberParts::unchecked(false, 1_000_000_000_000_000_001, -18);
        let two = NumberParts::try_from_external_parts(2, 0, MantissaScale::Large330).unwrap();

        let cases = [
            (
                RoundingMode::ToNearest,
                [
                    (1_000_000_000_000_000_000, 0),
                    (1_000_000_000_000_000_000, 0),
                    (5_000_000_000_000_000_000, -1),
                    (922_337_203_685_477_582, 1),
                    (-1_000_000_000_000_000_000, 0),
                ],
            ),
            (
                RoundingMode::TowardsZero,
                [
                    (1_000_000_000_000_000_000, 0),
                    (999_999_999_999_999_999, 0),
                    (5_000_000_000_000_000_000, -1),
                    (922_337_203_685_477_581, 1),
                    (-999_999_999_999_999_999, 0),
                ],
            ),
            (
                RoundingMode::Downward,
                [
                    (1_000_000_000_000_000_000, 0),
                    (999_999_999_999_999_999, 0),
                    (5_000_000_000_000_000_000, -1),
                    (922_337_203_685_477_581, 1),
                    (-1_000_000_000_000_000_000, 0),
                ],
            ),
            (
                RoundingMode::Upward,
                [
                    (1_000_000_000_000_000_001, 0),
                    (1_000_000_000_000_000_000, 0),
                    (5_000_000_000_000_000_000, -1),
                    (922_337_203_685_477_582, 1),
                    (-999_999_999_999_999_999, 0),
                ],
            ),
        ];

        for (mode, expected) in cases {
            let _rounding = NumberRoundModeGuard::new(mode);
            let actual = [
                unit + exact_zero_tail,
                unit - distant,
                unit - unit / two,
                cusp * factor,
                -unit + distant,
            ];
            for (value, expected_parts) in actual.into_iter().zip(expected) {
                assert_eq!(
                    value.external_parts().unwrap(),
                    expected_parts,
                    "mode={mode:?}"
                );
            }
        }
    }

    #[test]
    fn helper_constants_match_current_cpp_semantics() {
        assert_eq!(NUMBER_MIN_EXPONENT, -32_768);
        assert_eq!(NUMBER_MAX_EXPONENT, 32_768);
        assert_eq!(NUMBER_MAX_REP, i64::MAX);
        assert_eq!(NUMBER_ZERO_EXPONENT, i32::MIN);
        assert_eq!(MANTISSA_SMALL_MIN, 1_000_000_000_000_000);
        assert_eq!(MANTISSA_SMALL_MAX, 9_999_999_999_999_999);
        assert_eq!(MANTISSA_LARGE_MIN, 1_000_000_000_000_000_000);
        assert_eq!(MANTISSA_LARGE_MAX, 9_999_999_999_999_999_999);
        assert_eq!(mantissa_range_min(MantissaScale::Small), MANTISSA_SMALL_MIN);
        assert_eq!(mantissa_range_max(MantissaScale::Small), MANTISSA_SMALL_MAX);
        assert_eq!(mantissa_range_min(MantissaScale::Large), MANTISSA_LARGE_MIN);
        assert_eq!(mantissa_range_max(MantissaScale::Large), MANTISSA_LARGE_MAX);
        assert_eq!(
            mantissa_range_min(MantissaScale::LargeLegacy),
            MANTISSA_LARGE_MIN
        );
        assert_eq!(
            mantissa_range_max(MantissaScale::LargeLegacy),
            MANTISSA_LARGE_MAX
        );
        assert_eq!(mantissa_range_log(MantissaScale::Small), 15);
        assert_eq!(mantissa_range_log(MantissaScale::Large), 18);
        assert_eq!(mantissa_range_log(MantissaScale::LargeLegacy), 18);
        assert_eq!(
            signed_external_mantissa_bounds(MantissaScale::Small),
            (-(MANTISSA_SMALL_MAX as i64), MANTISSA_SMALL_MAX as i64)
        );
        assert_eq!(
            signed_external_mantissa_bounds(MantissaScale::Large),
            (-i64::MAX, i64::MAX)
        );
        assert_eq!(
            signed_external_mantissa_bounds(MantissaScale::LargeLegacy),
            (-i64::MAX, i64::MAX)
        );
    }

    #[test]
    fn external_to_internal_mantissa_edge_cases() {
        assert_eq!(external_to_internal_mantissa(0), 0);
        assert_eq!(external_to_internal_mantissa(42), 42);
        assert_eq!(external_to_internal_mantissa(-42), 42);
        assert_eq!(
            external_to_internal_mantissa(i64::MIN),
            9_223_372_036_854_775_808
        );
    }

    #[test]
    fn unchecked_constructor_preserves_raw_fields() {
        assert_eq!(
            NumberParts::unchecked(true, 123, -7),
            NumberParts {
                negative: true,
                mantissa: 123,
                exponent: -7,
            }
        );
    }

    #[test]
    fn number_parts_zero_and_one_match_cpp_helpers() {
        let _scale_guard = NumberMantissaScaleGuard::new(MantissaScale::Large);

        assert_eq!(NumberParts::zero(), NumberParts::zero());
        assert_eq!(
            NumberParts::zero(),
            NumberParts {
                negative: false,
                mantissa: 0,
                exponent: NUMBER_ZERO_EXPONENT,
            }
        );
        assert!(NumberParts::zero().is_normalized(MantissaScale::Small));
        assert!(NumberParts::zero().is_normalized(MantissaScale::Large));

        assert_eq!(
            NumberParts::one_small(),
            NumberParts {
                negative: false,
                mantissa: MANTISSA_SMALL_MIN,
                exponent: -15,
            }
        );
        assert_eq!(
            NumberParts::one_large(),
            NumberParts {
                negative: false,
                mantissa: MANTISSA_LARGE_MIN,
                exponent: -18,
            }
        );
        assert_eq!(
            NumberParts::one(MantissaScale::Small),
            NumberParts::one_small()
        );
        assert_eq!(
            NumberParts::one(MantissaScale::Large),
            NumberParts::one_large()
        );
        assert_eq!(current_number_one(), NumberParts::one(MantissaScale::Large));
        assert!(NumberParts::one_small().is_normalized(MantissaScale::Small));
        assert!(NumberParts::one_large().is_normalized(MantissaScale::Large));
    }

    #[test]
    fn range_helpers_match_current_cpp_bounds() {
        assert_eq!(
            NumberParts::min(MantissaScale::Small),
            NumberParts {
                negative: false,
                mantissa: MANTISSA_SMALL_MIN,
                exponent: NUMBER_MIN_EXPONENT,
            }
        );
        assert_eq!(
            NumberParts::max(MantissaScale::Small),
            NumberParts {
                negative: false,
                mantissa: MANTISSA_SMALL_MAX,
                exponent: NUMBER_MAX_EXPONENT,
            }
        );
        assert_eq!(
            NumberParts::lowest(MantissaScale::Small),
            NumberParts {
                negative: true,
                mantissa: MANTISSA_SMALL_MAX,
                exponent: NUMBER_MAX_EXPONENT,
            }
        );
        assert_eq!(
            NumberParts::min(MantissaScale::Large),
            NumberParts {
                negative: false,
                mantissa: MANTISSA_LARGE_MIN,
                exponent: NUMBER_MIN_EXPONENT,
            }
        );
        assert_eq!(
            NumberParts::max(MantissaScale::Large),
            NumberParts {
                negative: false,
                mantissa: NUMBER_MAX_REP as u64,
                exponent: NUMBER_MAX_EXPONENT,
            }
        );
        assert_eq!(
            NumberParts::lowest(MantissaScale::Large),
            NumberParts {
                negative: true,
                mantissa: NUMBER_MAX_REP as u64,
                exponent: NUMBER_MAX_EXPONENT,
            }
        );
    }

    #[test]
    fn exact_normalization_construction_boundaries() {
        assert_eq!(
            NumberParts::unchecked(false, 1, 0)
                .try_normalize_exact(MantissaScale::Small)
                .expect("small normalization should be exact"),
            NumberParts {
                negative: false,
                mantissa: MANTISSA_SMALL_MIN,
                exponent: -15,
            }
        );
        assert_eq!(
            NumberParts::unchecked(false, 1, 0)
                .try_normalize_exact(MantissaScale::Large)
                .expect("large normalization should be exact"),
            NumberParts {
                negative: false,
                mantissa: MANTISSA_LARGE_MIN,
                exponent: -18,
            }
        );
        assert_eq!(
            NumberParts::unchecked(true, 0, 99)
                .try_normalize_exact(MantissaScale::Large)
                .expect("zero should canonicalize"),
            NumberParts::zero()
        );
        assert_eq!(
            NumberParts::try_from_external_parts(1, 0, MantissaScale::Small)
                .expect("construction should be exact"),
            NumberParts::one_small()
        );
        assert_eq!(
            NumberParts::try_from_external_parts(1, 0, MantissaScale::Large)
                .expect("construction should be exact"),
            NumberParts::one_large()
        );
    }

    #[test]
    fn normalize_to_range_exact_helper() {
        assert_eq!(
            NumberParts::unchecked(false, 1, 0)
                .normalize_to_range(MANTISSA_SMALL_MIN, MANTISSA_SMALL_MAX)
                .expect("small normalization should be exact"),
            NumberParts::one_small()
        );
        assert_eq!(
            NumberParts::unchecked(false, 1, 0)
                .normalize_to_range(MANTISSA_LARGE_MIN, MANTISSA_LARGE_MAX)
                .expect("large normalization should be exact"),
            NumberParts::one_large()
        );
        assert_eq!(
            NumberParts::unchecked(true, 0, 99)
                .normalize_to_range(MANTISSA_LARGE_MIN, MANTISSA_LARGE_MAX)
                .expect("zero should canonicalize"),
            NumberParts::zero()
        );
    }

    #[test]
    fn normalized_range_checks_match_cpp_rules() {
        let large_normalized = NumberParts {
            negative: false,
            mantissa: 9_999_999_999_999_999_990,
            exponent: 0,
        };
        let negative_zero = NumberParts {
            negative: true,
            mantissa: 0,
            exponent: NUMBER_ZERO_EXPONENT,
        };

        assert!(large_normalized.is_normalized(MantissaScale::Large));
        assert!(!large_normalized.is_normalized(MantissaScale::Small));
        assert!(!negative_zero.is_normalized(MantissaScale::Large));
    }

    #[test]
    fn external_parts_match_cpp_accessor_behavior() {
        assert_eq!(
            NumberParts::one_small()
                .external_parts()
                .expect("small one is exact"),
            (1_000_000_000_000_000, -15)
        );
        assert_eq!(
            NumberParts::one_large()
                .external_parts()
                .expect("large one is exact"),
            (1_000_000_000_000_000_000, -18)
        );
        assert_eq!(
            NumberParts::unchecked(false, 9_900_000_000_000_123_450, 0)
                .external_parts()
                .expect("large internal mantissa with trailing zero is exact"),
            (990_000_000_000_012_345, 1)
        );
        assert_eq!(
            NumberParts::unchecked(true, 9_223_372_036_854_775_808, 0).external_parts(),
            Err(NumberNormalizeError::RequiresRounding)
        );
    }

    #[test]
    fn number_parts_ordering_comparison_rules() {
        assert_eq!(NumberParts::zero().signum(), 0);
        assert_eq!(NumberParts::unchecked(true, 1, 0).signum(), -1);
        assert_eq!(NumberParts::unchecked(false, 1, 0).signum(), 1);

        assert!(NumberParts::unchecked(true, 1, 0) < NumberParts::zero());
        assert!(NumberParts::zero() < NumberParts::unchecked(false, 1, 0));
        assert!(NumberParts::unchecked(false, 1, 1) > NumberParts::unchecked(false, 1, 0));
        assert!(NumberParts::unchecked(true, 1, 1) < NumberParts::unchecked(true, 1, 0));
        assert!(NumberParts::unchecked(false, 12, 0) > NumberParts::unchecked(false, 11, 0));
        assert_eq!(
            NumberParts::unchecked(true, 0, 99).compare(NumberParts::zero()),
            Ordering::Less
        );
    }

    #[test]
    fn truncate_matches_current_cpp_integer_drop_behavior() {
        let small = NumberParts::try_from_external_parts(12_345, -2, MantissaScale::Small)
            .expect("construction should be exact");
        let large = NumberParts::try_from_external_parts(12_345, -2, MantissaScale::Large)
            .expect("construction should be exact");

        assert_eq!(
            small.truncate(MantissaScale::Small),
            NumberParts::try_from_external_parts(123, 0, MantissaScale::Small)
                .expect("truncation result should normalize exactly")
        );
        assert_eq!(
            large.truncate(MantissaScale::Large),
            NumberParts::try_from_external_parts(123, 0, MantissaScale::Large)
                .expect("truncation result should normalize exactly")
        );
        assert_eq!(
            NumberParts::try_from_external_parts(-9, -1, MantissaScale::Large)
                .expect("construction should be exact")
                .truncate(MantissaScale::Large),
            NumberParts::zero()
        );
    }

    #[test]
    fn shift_exponent_boundary_behavior() {
        let shifted = NumberParts::one_small()
            .shift_exponent(3, MantissaScale::Small)
            .expect("shift should stay in range");
        assert_eq!(
            shifted,
            NumberParts {
                negative: false,
                mantissa: MANTISSA_SMALL_MIN,
                exponent: -12,
            }
        );

        let underflow = NumberParts::one_small()
            .shift_exponent(NUMBER_MIN_EXPONENT - (-15) - 1, MantissaScale::Small)
            .expect("underflow should normalize to zero");
        assert_eq!(underflow, NumberParts::zero());

        let overflow = NumberParts {
            negative: false,
            mantissa: MANTISSA_SMALL_MIN,
            exponent: NUMBER_MAX_EXPONENT,
        }
        .shift_exponent(0, MantissaScale::Small);
        assert_eq!(overflow, Err(NumberShiftExponentError::Overflow));
    }

    #[test]
    fn log_ten_and_power_of_ten_match_cpp_helpers() {
        assert_eq!(log_ten(1), Some(0));
        assert_eq!(log_ten(10), Some(1));
        assert_eq!(log_ten(1_000_000_000_000_000), Some(15));
        assert_eq!(log_ten(1_000_000_000_000_000_000), Some(18));
        assert_eq!(log_ten(12), None);
        assert_eq!(log_ten(0), None);
        assert!(is_power_of_ten(1));
        assert!(is_power_of_ten(1_000));
        assert!(!is_power_of_ten(12));
    }

    #[test]
    fn external_mantissa_bounds_match_current_scale_rules() {
        assert!(external_mantissa_in_range(
            MantissaScale::Small,
            9_999_999_999_999_999
        ));
        assert!(external_mantissa_in_range(
            MantissaScale::Small,
            -9_999_999_999_999_999
        ));
        assert!(!external_mantissa_in_range(
            MantissaScale::Small,
            10_000_000_000_000_000
        ));
        assert!(external_mantissa_in_range(MantissaScale::Large, i64::MAX));
        assert!(external_mantissa_in_range(
            MantissaScale::Large,
            i64::MIN + 1
        ));
        assert!(!external_mantissa_in_range(MantissaScale::Large, i64::MIN));
    }

    #[test]
    fn default_mantissa_scale_is_large() {
        set_mantissa_scale(MantissaScale::Large);
        assert_eq!(get_mantissa_scale(), MantissaScale::Large);
        assert_eq!(
            current_mantissa_range(),
            MantissaRange::new(MantissaScale::Large)
        );
        assert_eq!(current_number_one(), NumberParts::one(MantissaScale::Large));
        assert_eq!(current_mantissa_min(), MANTISSA_LARGE_MIN);
        assert_eq!(current_mantissa_max(), MANTISSA_LARGE_MAX);
        assert_eq!(current_mantissa_log(), 18);
        assert_eq!(current_number_min(), NumberParts::min(MantissaScale::Large));
        assert_eq!(current_number_max(), NumberParts::max(MantissaScale::Large));
        assert_eq!(
            current_number_lowest(),
            NumberParts::lowest(MantissaScale::Large)
        );
    }

    #[test]
    fn mantissa_scale_guard_restores_previous_scale() {
        set_mantissa_scale(MantissaScale::Large);

        {
            let _guard = NumberMantissaScaleGuard::new(MantissaScale::Small);
            assert_eq!(get_mantissa_scale(), MantissaScale::Small);
            assert_eq!(current_mantissa_min(), MANTISSA_SMALL_MIN);
            assert_eq!(current_mantissa_max(), MANTISSA_SMALL_MAX);
            assert_eq!(current_mantissa_log(), 15);
            assert_eq!(current_number_min(), NumberParts::min(MantissaScale::Small));
            assert_eq!(current_number_max(), NumberParts::max(MantissaScale::Small));
            assert_eq!(
                current_number_lowest(),
                NumberParts::lowest(MantissaScale::Small)
            );
        }

        assert_eq!(get_mantissa_scale(), MantissaScale::Large);
    }

    #[test]
    fn abs_and_squelch_helpers_match_cpp_roles() {
        let negative = NumberParts::unchecked(true, 1_000_000_000_000_000, -15);
        let small = NumberParts::unchecked(false, 1_000_000_000_000_000, -15);
        let limit = NumberParts::unchecked(false, 2_000_000_000_000_000, -15);

        assert_eq!(abs_number(negative), small);
        assert_eq!(abs_number(NumberParts::zero()), NumberParts::zero());
        assert_eq!(squelch_number(negative, limit), NumberParts::zero());
        assert_eq!(
            squelch_number(limit, limit),
            NumberParts::unchecked(false, 2_000_000_000_000_000, -15)
        );
    }

    #[test]
    fn mantissa_scale_is_thread_local() {
        set_mantissa_scale(MantissaScale::Small);

        let worker_scale = thread::spawn(get_mantissa_scale)
            .join()
            .expect("thread should complete");

        assert_eq!(worker_scale, MantissaScale::Large);
        assert_eq!(get_mantissa_scale(), MantissaScale::Small);

        set_mantissa_scale(MantissaScale::Large);
    }

    #[test]
    fn scale_display_strings() {
        assert_eq!(MantissaScale::Small.to_string(), "small");
        assert_eq!(MantissaScale::Large320.to_string(), "large320");
        assert_eq!(MantissaScale::Large330.to_string(), "large330");
        assert_eq!(MantissaScale::LargeLegacy.to_string(), "largeLegacy");
        assert_eq!(mantissa_scale_to_string(MantissaScale::Small), "small");
        assert_eq!(
            mantissa_scale_to_string(MantissaScale::Large320),
            "large320"
        );
        assert_eq!(
            mantissa_scale_to_string(MantissaScale::Large330),
            "large330"
        );
        assert_eq!(
            mantissa_scale_to_string(MantissaScale::LargeLegacy),
            "largeLegacy"
        );
    }

    #[test]
    fn default_rounding_mode_is_to_nearest() {
        set_rounding_mode(RoundingMode::ToNearest);
        assert_eq!(get_rounding_mode(), RoundingMode::ToNearest);
    }

    #[test]
    fn set_rounding_mode_returns_previous_value() {
        set_rounding_mode(RoundingMode::ToNearest);
        assert_eq!(
            set_rounding_mode(RoundingMode::Downward),
            RoundingMode::ToNearest
        );
        assert_eq!(get_rounding_mode(), RoundingMode::Downward);
        set_rounding_mode(RoundingMode::ToNearest);
    }

    #[test]
    fn save_number_round_mode_restores_saved_value_on_drop() {
        set_rounding_mode(RoundingMode::Upward);

        {
            let _saved = SaveNumberRoundMode::new(RoundingMode::Upward);
            set_rounding_mode(RoundingMode::TowardsZero);
            assert_eq!(get_rounding_mode(), RoundingMode::TowardsZero);
        }

        assert_eq!(get_rounding_mode(), RoundingMode::Upward);
        set_rounding_mode(RoundingMode::ToNearest);
    }

    #[test]
    fn number_round_mode_guard_sets_new_mode_and_restores_old_one() {
        set_rounding_mode(RoundingMode::ToNearest);

        {
            let _guard = NumberRoundModeGuard::new(RoundingMode::Downward);
            assert_eq!(get_rounding_mode(), RoundingMode::Downward);
        }

        assert_eq!(get_rounding_mode(), RoundingMode::ToNearest);
    }

    #[test]
    fn rounding_mode_is_thread_local() {
        set_rounding_mode(RoundingMode::Upward);

        let worker_mode = thread::spawn(get_rounding_mode)
            .join()
            .expect("thread should complete");

        assert_eq!(worker_mode, RoundingMode::ToNearest);
        assert_eq!(get_rounding_mode(), RoundingMode::Upward);

        set_rounding_mode(RoundingMode::ToNearest);
    }
}
