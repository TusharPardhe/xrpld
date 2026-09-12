use basics::number::{
    MantissaRange, MantissaScale, NUMBER_MAX_EXPONENT, NUMBER_MAX_REP, NUMBER_MIN_EXPONENT,
    NumberArithmeticError, NumberParts as RuntimeNumber, external_to_internal_mantissa,
};

use super::IouRoundGuard;

pub(super) fn runtime_number_from_external_parts(
    mantissa: i64,
    exponent: i32,
    scale: MantissaScale,
) -> Result<RuntimeNumber, NumberArithmeticError> {
    let range = MantissaRange::new(scale);
    normalize_parts_to_range(
        mantissa < 0,
        external_to_internal_mantissa(mantissa),
        exponent,
        range.min,
        range.max,
    )
}

pub(super) fn normalize_runtime_number_to_range(
    number: RuntimeNumber,
    min_mantissa: u64,
    max_mantissa: u64,
) -> Result<RuntimeNumber, NumberArithmeticError> {
    normalize_parts_to_range(
        number.negative,
        number.mantissa,
        number.exponent,
        min_mantissa,
        max_mantissa,
    )
}

fn normalize_parts_to_range(
    mut negative: bool,
    mut mantissa: u64,
    mut exponent: i32,
    min_mantissa: u64,
    max_mantissa: u64,
) -> Result<RuntimeNumber, NumberArithmeticError> {
    if mantissa == 0 {
        return Ok(RuntimeNumber::zero());
    }
    while mantissa < min_mantissa && exponent > NUMBER_MIN_EXPONENT {
        mantissa = mantissa
            .checked_mul(10)
            .ok_or(NumberArithmeticError::Overflow)?;
        exponent -= 1;
    }

    let mut guard = IouRoundGuard::default();
    if negative {
        guard.set_negative();
    }
    while mantissa > max_mantissa {
        if exponent >= NUMBER_MAX_EXPONENT {
            return Err(NumberArithmeticError::Overflow);
        }
        guard.push((mantissa % 10) as u8);
        mantissa /= 10;
        exponent += 1;
    }
    if exponent < NUMBER_MIN_EXPONENT || mantissa < min_mantissa {
        return Ok(RuntimeNumber::zero());
    }
    if mantissa > NUMBER_MAX_REP as u64 {
        if exponent >= NUMBER_MAX_EXPONENT {
            return Err(NumberArithmeticError::Overflow);
        }
        guard.push((mantissa % 10) as u8);
        mantissa /= 10;
        exponent += 1;
    }

    let mut widened = u128::from(mantissa);
    guard.do_round_up(
        &mut negative,
        &mut widened,
        &mut exponent,
        min_mantissa,
        max_mantissa,
    )?;
    Ok(RuntimeNumber::unchecked(
        negative && widened != 0,
        u64::try_from(widened).map_err(|_| NumberArithmeticError::Overflow)?,
        exponent,
    ))
}

pub(super) fn signed_runtime_mantissa(number: RuntimeNumber) -> Result<i64, NumberArithmeticError> {
    let mantissa = i64::try_from(number.mantissa).map_err(|_| NumberArithmeticError::Overflow)?;
    if number.negative {
        mantissa
            .checked_neg()
            .ok_or(NumberArithmeticError::Overflow)
    } else {
        Ok(mantissa)
    }
}
