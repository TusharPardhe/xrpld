//! Canonical LWAB primitive encoding and bounded decoding.

use super::lwab_types::*;
pub const MAGIC: &[u8; 4] = b"LWAB";
pub const VERSION: u8 = 1;
const MAX_WIRE_BYTES: usize = 65_536;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WireError {
    Truncated {
        offset: usize,
        needed: usize,
        remaining: usize,
    },
    Trailing {
        offset: usize,
        remaining: usize,
    },
    BadMagic,
    BadVersion(u8),
    BadTag(u8, u8),
    BadBoolean {
        offset: usize,
        actual: u8,
    },
    BadOption {
        offset: usize,
        actual: u8,
    },
    BadLength {
        offset: usize,
        declared: usize,
    },
    BadNumericType {
        offset: usize,
        actual: u8,
    },
    OutOfRange(usize),
    NonCanonical(usize),
}

pub(crate) fn u8(out: &mut Vec<u8>, x: u8) {
    out.push(x);
}
pub(crate) fn u16(out: &mut Vec<u8>, x: u16) {
    out.extend(x.to_le_bytes());
}
pub(crate) fn u32(out: &mut Vec<u8>, x: u32) {
    out.extend(x.to_le_bytes());
}
pub(crate) fn u64(out: &mut Vec<u8>, x: u64) {
    out.extend(x.to_le_bytes());
}
pub(crate) fn int(out: &mut Vec<u8>, x: i64) {
    u64(out, x as u64);
}
pub(crate) fn boolean(out: &mut Vec<u8>, x: bool) {
    u8(out, x as u8);
}

pub(crate) fn number(out: &mut Vec<u8>, x: Number) -> Result<(), WireError> {
    if !(x == Number::ZERO
        || (1_000_000_000_000_000_000..=9_999_999_999_999_999_999).contains(&x.mantissa)
            && (-32768..=32768).contains(&x.exponent))
    {
        return Err(WireError::NonCanonical(0));
    }
    boolean(out, x.negative);
    u64(out, x.mantissa);
    int(out, x.exponent);
    Ok(())
}
pub(crate) fn numeric_type(out: &mut Vec<u8>, x: NumericType) {
    match x {
        NumericType::Fractional => u8(out, 0),
        NumericType::Integral {
            maximum,
            offset,
            sqrt,
            shift,
        } => {
            u8(out, 1);
            u64(out, maximum);
            int(out, offset);
            u64(out, sqrt);
            u64(out, shift);
        }
    }
}
pub(crate) fn stamount(out: &mut Vec<u8>, x: STAmount) -> Result<(), WireError> {
    numeric_type(out, x.numeric_type);
    u64(out, x.mantissa);
    int(out, x.exponent);
    boolean(out, x.negative);
    Ok(())
}
pub(crate) fn option<T: Copy>(
    out: &mut Vec<u8>,
    value: Option<T>,
    encode: impl Fn(&mut Vec<u8>, T) -> Result<(), WireError>,
) -> Result<(), WireError> {
    match value {
        None => u8(out, 0),
        Some(x) => {
            u8(out, 1);
            encode(out, x)?;
        }
    };
    Ok(())
}
pub(crate) fn envelope(tag: u8, payload: Vec<u8>) -> Vec<u8> {
    let mut out = Vec::with_capacity(10 + payload.len());
    out.extend(MAGIC);
    u8(&mut out, VERSION);
    u8(&mut out, tag);
    u32(&mut out, payload.len() as u32);
    out.extend(payload);
    out
}

include!("lwab_primitive_reader.rs");
