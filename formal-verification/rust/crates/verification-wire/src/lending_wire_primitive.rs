//! Canonical LWAB primitive encoding and bounded decoding.

use super::lending_wire_types::*;
pub const MAGIC: &[u8; 4] = b"LWAB";
pub const VERSION: u8 = 1;
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WireError {
    Truncated,
    Trailing,
    BadMagic,
    BadVersion(u8),
    BadTag(u8, u8),
    BadBoolean(u8),
    BadOption(u8),
    BadNumericType(u8),
    NonCanonical,
    OutOfRange,
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
        return Err(WireError::NonCanonical);
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

pub(crate) struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    pub(crate) fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8], WireError> {
        let end = self.at.checked_add(n).ok_or(WireError::Truncated)?;
        let x = self.bytes.get(self.at..end).ok_or(WireError::Truncated)?;
        self.at = end;
        Ok(x)
    }
    pub(crate) fn u8(&mut self) -> Result<u8, WireError> {
        Ok(self.take(1)?[0])
    }
    pub(crate) fn u16(&mut self) -> Result<u16, WireError> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }
    pub(crate) fn u32(&mut self) -> Result<u32, WireError> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    pub(crate) fn u64(&mut self) -> Result<u64, WireError> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    pub(crate) fn int(&mut self) -> Result<i64, WireError> {
        Ok(self.u64()? as i64)
    }
    pub(crate) fn boolean(&mut self) -> Result<bool, WireError> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            x => Err(WireError::BadBoolean(x)),
        }
    }
    pub(crate) fn number(&mut self) -> Result<Number, WireError> {
        let x = Number {
            negative: self.boolean()?,
            mantissa: self.u64()?,
            exponent: self.int()?,
        };
        let mut b = Vec::new();
        number(&mut b, x)?;
        Ok(x)
    }
    pub(crate) fn numeric_type(&mut self) -> Result<NumericType, WireError> {
        match self.u8()? {
            0 => Ok(NumericType::Fractional),
            1 => Ok(NumericType::Integral {
                maximum: self.u64()?,
                offset: self.int()?,
                sqrt: self.u64()?,
                shift: self.u64()?,
            }),
            x => Err(WireError::BadNumericType(x)),
        }
    }
    pub(crate) fn position(&self) -> usize {
        self.at
    }
    pub(crate) fn done(&self) -> Result<(), WireError> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(WireError::Trailing)
        }
    }
}
pub(crate) fn read_envelope(expected: u8, input: &[u8]) -> Result<&[u8], WireError> {
    let mut r = Reader::new(input);
    if r.take(4)? != MAGIC {
        return Err(WireError::BadMagic);
    }
    let v = r.u8()?;
    if v != VERSION {
        return Err(WireError::BadVersion(v));
    }
    let tag = r.u8()?;
    if tag != expected {
        return Err(WireError::BadTag(expected, tag));
    }
    let len = r.u32()? as usize;
    let p = r.take(len)?;
    r.done()?;
    Ok(p)
}
