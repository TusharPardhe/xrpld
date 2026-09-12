use basics::number::{
    NUMBER_MAX_EXPONENT, NUMBER_MAX_REP, NUMBER_MIN_EXPONENT, NUMBER_ZERO_EXPONENT,
    NumberArithmeticError, RoundingMode, get_rounding_mode,
};

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct IouRoundGuard {
    digits: u64,
    has_extra: bool,
    negative: bool,
}

impl IouRoundGuard {
    pub(super) fn set_negative(&mut self) {
        self.negative = true;
    }

    pub(super) fn push(&mut self, digit: u8) {
        self.has_extra = self.has_extra || ((self.digits & 0xF) != 0);
        self.digits >>= 4;
        self.digits |= u64::from(digit & 0x0F) << 60;
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
    ) {
        if *mantissa < u128::from(min_mantissa) {
            *mantissa *= 10;
            *exponent -= 1;
        }
        if *exponent < NUMBER_MIN_EXPONENT {
            *negative = false;
            *mantissa = 0;
            *exponent = NUMBER_ZERO_EXPONENT;
        }
    }

    pub(super) fn do_round_up(
        &self,
        negative: &mut bool,
        mantissa: &mut u128,
        exponent: &mut i32,
        min_mantissa: u64,
        max_mantissa: u64,
    ) -> Result<(), NumberArithmeticError> {
        let rounded = self.round();
        if rounded == 1 || (rounded == 0 && (*mantissa & 1) == 1) {
            *mantissa = mantissa
                .checked_add(1)
                .ok_or(NumberArithmeticError::Overflow)?;
            if *mantissa > u128::from(max_mantissa) || *mantissa > u128::from(NUMBER_MAX_REP as u64)
            {
                *mantissa /= 10;
                *exponent = exponent
                    .checked_add(1)
                    .ok_or(NumberArithmeticError::Overflow)?;
            }
        }
        self.bring_into_range(negative, mantissa, exponent, min_mantissa);
        if *exponent > NUMBER_MAX_EXPONENT {
            return Err(NumberArithmeticError::Overflow);
        }
        Ok(())
    }
}
