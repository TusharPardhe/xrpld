//! Vault values encoded by Lean's shared Lending LWAB codec.

use super::primitive::{DecodeError, Reader};
use basics::number::{MantissaScale, NUMBER_ZERO_EXPONENT, NumberParts};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumericType {
    Fractional,
    Integral {
        maximum: u64,
        offset: i64,
        sqrt: u64,
        shift: u64,
    },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Amount {
    pub numeric_type: NumericType,
    pub mantissa: u64,
    pub exponent: i64,
    pub negative: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Vault {
    pub total: NumberParts,
    pub available: NumberParts,
    pub reserved: NumberParts,
    pub maximum: Option<NumberParts>,
    pub numeric_type: NumericType,
    pub scale: u8,
    pub shares: NumberParts,
    pub loss: NumberParts,
}

pub fn number(out: &mut Vec<u8>, value: NumberParts) -> Result<(), DecodeError> {
    if !value.is_normalized(MantissaScale::Large) {
        return Err(DecodeError::NonCanonical { offset: 0 });
    }
    out.push(value.negative as u8);
    out.extend(value.mantissa.to_le_bytes());
    out.extend((value.exponent as i64).to_le_bytes());
    Ok(())
}
pub fn read_number(r: &mut Reader<'_>) -> Result<NumberParts, DecodeError> {
    let offset = r.offset();
    let negative = boolean(r)?;
    let mantissa = r.u64()?;
    let exponent = r.i64()?;
    let exponent = i32::try_from(exponent).map_err(|_| DecodeError::NonCanonical { offset })?;
    let value = NumberParts::unchecked(negative, mantissa, exponent);
    if value.is_normalized(MantissaScale::Large) {
        Ok(value)
    } else {
        Err(DecodeError::NonCanonical { offset })
    }
}
pub fn numeric_type(out: &mut Vec<u8>, value: NumericType) {
    match value {
        NumericType::Fractional => out.push(0),
        NumericType::Integral {
            maximum,
            offset,
            sqrt,
            shift,
        } => {
            out.push(1);
            out.extend(maximum.to_le_bytes());
            out.extend(offset.to_le_bytes());
            out.extend(sqrt.to_le_bytes());
            out.extend(shift.to_le_bytes());
        }
    }
}
pub fn read_numeric_type(r: &mut Reader<'_>) -> Result<NumericType, DecodeError> {
    let offset = r.offset();
    match r.u8()? {
        0 => Ok(NumericType::Fractional),
        1 => Ok(NumericType::Integral {
            maximum: r.u64()?,
            offset: r.i64()?,
            sqrt: r.u64()?,
            shift: r.u64()?,
        }),
        actual => Err(DecodeError::BadNumericType { offset, actual }),
    }
}
pub fn amount(out: &mut Vec<u8>, value: Amount) -> Result<(), DecodeError> {
    numeric_type(out, value.numeric_type);
    out.extend(value.mantissa.to_le_bytes());
    out.extend(value.exponent.to_le_bytes());
    out.push(value.negative as u8);
    Ok(())
}
pub fn read_amount(r: &mut Reader<'_>) -> Result<Amount, DecodeError> {
    let offset = r.offset();
    let numeric_type = read_numeric_type(r)?;
    let mantissa = r.u64()?;
    let exponent = r.i64()?;
    let negative = boolean(r)?;
    if !amount_canonical(numeric_type, mantissa, exponent, negative) {
        return Err(DecodeError::NonCanonical { offset });
    }
    Ok(Amount {
        numeric_type,
        mantissa,
        exponent,
        negative,
    })
}
fn amount_canonical(kind: NumericType, mantissa: u64, exponent: i64, negative: bool) -> bool {
    if mantissa == 0 {
        return !negative && matches!(kind, NumericType::Fractional) && exponent == -100
            || !negative && matches!(kind, NumericType::Integral { .. }) && exponent == 0;
    }
    match kind {
        NumericType::Fractional => {
            (1_000_000_000_000_000..=9_999_999_999_999_999).contains(&mantissa)
                && (-96..=80).contains(&exponent)
        }
        NumericType::Integral { maximum, .. } => !negative && exponent == 0 && mantissa <= maximum,
    }
}
pub fn vault(out: &mut Vec<u8>, value: Vault) -> Result<(), DecodeError> {
    number(out, value.total)?;
    number(out, value.available)?;
    number(out, value.reserved)?;
    option_number(out, value.maximum)?;
    numeric_type(out, value.numeric_type);
    out.push(value.scale);
    number(out, value.shares)?;
    number(out, value.loss)
}
pub fn read_vault(r: &mut Reader<'_>) -> Result<Vault, DecodeError> {
    let offset = r.offset();
    let value = Vault {
        total: read_number(r)?,
        available: read_number(r)?,
        reserved: read_number(r)?,
        maximum: read_option_number(r)?,
        numeric_type: read_numeric_type(r)?,
        scale: r.u8()?,
        shares: read_number(r)?,
        loss: read_number(r)?,
    };
    if super::validation::lawful(value) {
        Ok(value)
    } else {
        Err(DecodeError::NonCanonical { offset })
    }
}
pub fn boolean(r: &mut Reader<'_>) -> Result<bool, DecodeError> {
    let offset = r.offset();
    match r.u8()? {
        0 => Ok(false),
        1 => Ok(true),
        actual => Err(DecodeError::BadBoolean { offset, actual }),
    }
}
pub fn option_number(out: &mut Vec<u8>, value: Option<NumberParts>) -> Result<(), DecodeError> {
    match value {
        None => out.push(0),
        Some(x) => {
            out.push(1);
            number(out, x)?;
        }
    }
    Ok(())
}
pub fn read_option_number(r: &mut Reader<'_>) -> Result<Option<NumberParts>, DecodeError> {
    let offset = r.offset();
    match r.u8()? {
        0 => Ok(None),
        1 => Ok(Some(read_number(r)?)),
        actual => Err(DecodeError::BadOption { offset, actual }),
    }
}
pub fn zero_amount(kind: NumericType) -> Amount {
    Amount {
        numeric_type: kind,
        mantissa: 0,
        exponent: if matches!(kind, NumericType::Fractional) {
            -100
        } else {
            0
        },
        negative: false,
    }
}
pub const fn zero_number() -> NumberParts {
    NumberParts {
        negative: false,
        mantissa: 0,
        exponent: NUMBER_ZERO_EXPONENT,
    }
}
