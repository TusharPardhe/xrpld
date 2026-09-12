//! Shared Lean `LWAB` framing for the Vault wire dispatcher.

pub const MAGIC: &[u8; 4] = b"LWAB";
pub const VERSION: u8 = 1;
pub const MAX_BYTES: usize = 65_536;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeError {
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
    BadTag {
        expected: u8,
        actual: u8,
    },
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
    OutOfRange {
        offset: usize,
    },
    NonCanonical {
        offset: usize,
    },
}

pub fn decode_error(error: DecodeError, out: &mut Vec<u8>) {
    match error {
        DecodeError::Truncated {
            offset,
            needed,
            remaining,
        } => {
            out.push(0);
            words(out, &[offset, needed, remaining]);
        }
        DecodeError::Trailing { offset, remaining } => {
            out.push(1);
            words(out, &[offset, remaining]);
        }
        DecodeError::BadMagic => out.push(2),
        DecodeError::BadVersion(actual) => out.extend([3, actual]),
        DecodeError::BadTag { expected, actual } => out.extend([4, expected, actual]),
        DecodeError::BadBoolean { offset, actual } => {
            out.push(5);
            words(out, &[offset]);
            out.push(actual);
        }
        DecodeError::BadOption { offset, actual } => {
            out.push(6);
            words(out, &[offset]);
            out.push(actual);
        }
        DecodeError::BadLength { offset, declared } => {
            out.push(7);
            words(out, &[offset, declared]);
        }
        DecodeError::BadNumericType { offset, actual } => {
            out.push(8);
            words(out, &[offset]);
            out.push(actual);
        }
        DecodeError::OutOfRange { offset } => {
            out.push(9);
            words(out, &[offset]);
        }
        DecodeError::NonCanonical { offset } => {
            out.push(10);
            words(out, &[offset]);
        }
    }
}

fn words(out: &mut Vec<u8>, values: &[usize]) {
    for value in values {
        out.extend((*value as u64).to_le_bytes());
    }
}

pub fn response(tag: u8, payload: Vec<u8>) -> Vec<u8> {
    let mut out = Vec::with_capacity(10 + payload.len());
    out.extend(MAGIC);
    out.extend([VERSION, tag]);
    out.extend((payload.len() as u32).to_le_bytes());
    out.extend(payload);
    out
}

pub fn decode_error_response(route: u8, error: DecodeError) -> Vec<u8> {
    let mut payload = vec![1];
    decode_error(error, &mut payload);
    response(route + 128, payload)
}

pub struct Reader<'a> {
    input: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    pub fn new(input: &'a [u8]) -> Self {
        Self { input, at: 0 }
    }
    pub fn offset(&self) -> usize {
        self.at
    }
    pub fn take(&mut self, n: usize) -> Result<&'a [u8], DecodeError> {
        let end = self.at.checked_add(n).ok_or(DecodeError::Truncated {
            offset: self.at,
            needed: n,
            remaining: 0,
        })?;
        let value = self.input.get(self.at..end).ok_or(DecodeError::Truncated {
            offset: self.at,
            needed: n,
            remaining: self.input.len().saturating_sub(self.at),
        })?;
        self.at = end;
        Ok(value)
    }
    pub fn u8(&mut self) -> Result<u8, DecodeError> {
        Ok(self.take(1)?[0])
    }
    pub fn u64(&mut self) -> Result<u64, DecodeError> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().expect("width")))
    }
    pub fn i64(&mut self) -> Result<i64, DecodeError> {
        Ok(self.u64()? as i64)
    }
    pub fn done(&self) -> Result<(), DecodeError> {
        if self.at == self.input.len() {
            Ok(())
        } else {
            Err(DecodeError::Trailing {
                offset: self.at,
                remaining: self.input.len() - self.at,
            })
        }
    }
}

pub fn payload(expected: u8, input: &[u8]) -> Result<&[u8], DecodeError> {
    let mut r = Reader::new(input);
    if r.take(4)? != MAGIC {
        return Err(DecodeError::BadMagic);
    }
    let version = r.u8()?;
    if version != VERSION {
        return Err(DecodeError::BadVersion(version));
    }
    let actual = r.u8()?;
    if actual != expected {
        return Err(DecodeError::BadTag { expected, actual });
    }
    let offset = r.offset();
    let declared = u32::from_le_bytes(r.take(4)?.try_into().expect("width")) as usize;
    if declared > MAX_BYTES {
        return Err(DecodeError::BadLength { offset, declared });
    }
    let value = r.take(declared)?;
    r.done()?;
    Ok(value)
}
