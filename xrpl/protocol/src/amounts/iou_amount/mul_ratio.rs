use basics::number::NumberArithmeticError;

use super::{IOUAmount, MIN_IOU_MANTISSA};

pub fn mul_ratio(
    amount: IOUAmount,
    num: u32,
    den: u32,
    round_up: bool,
) -> Result<IOUAmount, NumberArithmeticError> {
    if den == 0 {
        return Err(NumberArithmeticError::DivideByZero);
    }

    let negative = amount.mantissa() < 0;
    let denominator = u128::from(den);
    let multiplied = i128::from(amount.mantissa())
        .unsigned_abs()
        .checked_mul(u128::from(num))
        .ok_or(NumberArithmeticError::Overflow)?;
    let mut low = multiplied / denominator;
    let mut remainder = multiplied - low * denominator;
    let mut exponent = amount.exponent();

    if remainder != 0 {
        let room_to_grow =
            log10_floor_u128(basics::number::NUMBER_MAX_REP as u128) - log10_ceil_u128(low);
        if room_to_grow > 0 {
            let scale = pow10_u128(room_to_grow as u32)?;
            exponent = exponent
                .checked_sub(room_to_grow)
                .ok_or(NumberArithmeticError::Overflow)?;
            low = low
                .checked_mul(scale)
                .ok_or(NumberArithmeticError::Overflow)?;
            remainder = remainder
                .checked_mul(scale)
                .ok_or(NumberArithmeticError::Overflow)?;
        }
        let add_remainder = remainder / denominator;
        low = low
            .checked_add(add_remainder)
            .ok_or(NumberArithmeticError::Overflow)?;
        remainder -= add_remainder * denominator;
    }

    let mut has_remainder = remainder != 0;
    let must_shrink =
        log10_ceil_u128(low) - log10_floor_u128(basics::number::NUMBER_MAX_REP as u128);
    if must_shrink > 0 {
        let scale = pow10_u128(must_shrink as u32)?;
        let saved = low;
        exponent = exponent
            .checked_add(must_shrink)
            .ok_or(NumberArithmeticError::Overflow)?;
        low /= scale;
        if !has_remainder {
            has_remainder = saved - low * scale != 0;
        }
    }

    let mut mantissa = i64::try_from(low).map_err(|_| NumberArithmeticError::Overflow)?;
    if negative {
        mantissa = mantissa
            .checked_neg()
            .ok_or(NumberArithmeticError::Overflow)?;
    }
    let result = IOUAmount::from_parts(mantissa, exponent)?;
    if !has_remainder {
        return Ok(result);
    }
    if round_up && !negative {
        if result.is_zero() {
            return Ok(IOUAmount::min_positive_amount());
        }
        return IOUAmount::from_parts(
            result
                .mantissa()
                .checked_add(1)
                .ok_or(NumberArithmeticError::Overflow)?,
            result.exponent(),
        );
    }
    if !round_up && negative {
        if result.is_zero() {
            return IOUAmount::from_parts(-MIN_IOU_MANTISSA, super::MIN_IOU_EXPONENT);
        }
        return IOUAmount::from_parts(
            result
                .mantissa()
                .checked_sub(1)
                .ok_or(NumberArithmeticError::Overflow)?,
            result.exponent(),
        );
    }
    Ok(result)
}

fn pow10_u128(exponent: u32) -> Result<u128, NumberArithmeticError> {
    let mut value = 1u128;
    for _ in 0..exponent {
        value = value
            .checked_mul(10)
            .ok_or(NumberArithmeticError::Overflow)?;
    }
    Ok(value)
}

fn log10_floor_u128(mut value: u128) -> i32 {
    if value == 0 {
        return -1;
    }
    let mut log = 0i32;
    while value >= 10 {
        value /= 10;
        log += 1;
    }
    log
}

fn log10_ceil_u128(value: u128) -> i32 {
    if value == 0 {
        return 0;
    }
    let floor = log10_floor_u128(value);
    let power = pow10_u128(floor as u32).expect("log10 floor should fit u128");
    if power == value { floor } else { floor + 1 }
}
