//! Version-one strict Vault result codec.
//!
//! It preserves every canonical field from `wire_types`, including the explicit
//! raw/terminal association boundary. It is intentionally distinct from the
//! parent `i64` adapter.

#[path = "wire_types.rs"]
mod types;
pub use types::*;

pub const MAGIC: [u8; 4] = *b"VWAB";
pub const VERSION: u8 = 1;
const OUTCOME_OK: u8 = 0;
const OUTCOME_ERROR: u8 = 1;

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend(value.to_le_bytes());
}
fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend(value.to_le_bytes());
}
fn put_number(out: &mut Vec<u8>, value: Number) {
    out.push(u8::from(value.negative));
    put_u64(out, value.mantissa);
    put_u32(out, value.exponent as u32);
}
fn put_type(out: &mut Vec<u8>, value: NumericType) {
    out.push(match value {
        NumericType::Native => 0,
        NumericType::Int64 => 1,
        NumericType::Fractional => 2,
    });
}
fn put_amount(out: &mut Vec<u8>, value: Amount) {
    put_type(out, value.numeric_type);
    put_number(out, value.number);
}

struct Cursor<'a> {
    bytes: &'a [u8],
    index: usize,
}
impl<'a> Cursor<'a> {
    fn take(&mut self, length: usize) -> Result<&'a [u8], CodecError> {
        let end = self
            .index
            .checked_add(length)
            .ok_or(CodecError::Truncated)?;
        let value = self
            .bytes
            .get(self.index..end)
            .ok_or(CodecError::Truncated)?;
        self.index = end;
        Ok(value)
    }
    fn byte(&mut self) -> Result<u8, CodecError> {
        Ok(self.take(1)?[0])
    }
    fn u32(&mut self) -> Result<u32, CodecError> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn u64(&mut self) -> Result<u64, CodecError> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    fn number(&mut self) -> Result<Number, CodecError> {
        let negative = match self.byte()? {
            0 => false,
            1 => true,
            _ => return Err(CodecError::BadBoolean),
        };
        Ok(Number {
            negative,
            mantissa: self.u64()?,
            exponent: self.u32()? as i32,
        })
    }
    fn numeric_type(&mut self) -> Result<NumericType, CodecError> {
        match self.byte()? {
            0 => Ok(NumericType::Native),
            1 => Ok(NumericType::Int64),
            2 => Ok(NumericType::Fractional),
            _ => Err(CodecError::BadTag),
        }
    }
    fn amount(&mut self) -> Result<Amount, CodecError> {
        Ok(Amount {
            numeric_type: self.numeric_type()?,
            number: self.number()?,
        })
    }
}

/// Encodes the full result for one Vault route. `route` is kept in every frame,
/// so raw and terminal invocations remain distinguishable on the wire.
pub fn encode(route: u8, outcome: &Outcome) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend(MAGIC);
    out.push(VERSION);
    out.push(route);
    match outcome {
        Outcome::Error(error) => out.extend([
            OUTCOME_ERROR,
            match error {
                Error::PrecisionLoss => 0,
                Error::InsufficientFunds => 1,
                Error::InvalidState => 2,
            },
        ]),
        Outcome::Ok(vault) => {
            out.push(OUTCOME_OK);
            out.extend(vault.vault_id);
            out.extend(vault.owner);
            out.extend(vault.account);
            put_amount(&mut out, vault.asset);
            put_number(&mut out, vault.assets_total);
            put_number(&mut out, vault.assets_available);
            put_number(&mut out, vault.assets_reserved);
            match vault.assets_maximum {
                None => out.push(0),
                Some(value) => {
                    out.push(1);
                    put_number(&mut out, value);
                }
            }
            put_type(&mut out, vault.numeric_type);
            out.push(vault.scale);
            put_number(&mut out, vault.shares_total);
            put_number(&mut out, vault.loss_unrealized);
            out.push(u8::from(vault.terminal));
        }
    }
    out
}

pub fn decode(bytes: &[u8]) -> Result<(u8, Outcome), CodecError> {
    let mut c = Cursor { bytes, index: 0 };
    if c.take(4)? != MAGIC {
        return Err(CodecError::BadTag);
    }
    if c.byte()? != VERSION {
        return Err(CodecError::BadVersion);
    }
    let route = c.byte()?;
    let outcome = match c.byte()? {
        OUTCOME_ERROR => Outcome::Error(match c.byte()? {
            0 => Error::PrecisionLoss,
            1 => Error::InsufficientFunds,
            2 => Error::InvalidState,
            _ => return Err(CodecError::BadTag),
        }),
        OUTCOME_OK => {
            let vault_id = c.take(32)?.try_into().unwrap();
            let owner = c.take(20)?.try_into().unwrap();
            let account = c.take(20)?.try_into().unwrap();
            let asset = c.amount()?;
            let assets_total = c.number()?;
            let assets_available = c.number()?;
            let assets_reserved = c.number()?;
            let assets_maximum = match c.byte()? {
                0 => None,
                1 => Some(c.number()?),
                _ => return Err(CodecError::BadOption),
            };
            let numeric_type = c.numeric_type()?;
            let scale = c.byte()?;
            let shares_total = c.number()?;
            let loss_unrealized = c.number()?;
            let terminal = match c.byte()? {
                0 => false,
                1 => true,
                _ => return Err(CodecError::BadBoolean),
            };
            Outcome::Ok(Vault {
                vault_id,
                owner,
                account,
                asset,
                assets_total,
                assets_available,
                assets_reserved,
                assets_maximum,
                numeric_type,
                scale,
                shares_total,
                loss_unrealized,
                terminal,
            })
        }
        _ => return Err(CodecError::BadTag),
    };
    if c.index != bytes.len() {
        return Err(CodecError::Trailing);
    }
    Ok((route, outcome))
}
