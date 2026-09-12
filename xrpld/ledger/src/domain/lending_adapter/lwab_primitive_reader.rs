pub(crate) struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    pub(crate) fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8], WireError> {
        let start = self.at;
        let end = start.checked_add(n).ok_or(WireError::Truncated {
            offset: start,
            needed: n,
            remaining: self.bytes.len().saturating_sub(start),
        })?;
        let x = self.bytes.get(start..end).ok_or(WireError::Truncated {
            offset: start,
            needed: n,
            remaining: self.bytes.len().saturating_sub(start),
        })?;
        self.at = end;
        Ok(x)
    }
    pub(crate) fn u8(&mut self) -> Result<u8, WireError> {
        Ok(self.take(1)?[0])
    }
    pub(crate) fn u16(&mut self) -> Result<u16, WireError> {
        Ok(u16::from_le_bytes(
            self.take(2)?.try_into().expect("two bytes"),
        ))
    }
    pub(crate) fn u32(&mut self) -> Result<u32, WireError> {
        Ok(u32::from_le_bytes(
            self.take(4)?.try_into().expect("four bytes"),
        ))
    }
    pub(crate) fn u64(&mut self) -> Result<u64, WireError> {
        Ok(u64::from_le_bytes(
            self.take(8)?.try_into().expect("eight bytes"),
        ))
    }
    pub(crate) fn int(&mut self) -> Result<i64, WireError> {
        Ok(self.u64()? as i64)
    }
    pub(crate) fn boolean(&mut self) -> Result<bool, WireError> {
        let offset = self.at;
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            actual => Err(WireError::BadBoolean { offset, actual }),
        }
    }
    pub(crate) fn number(&mut self) -> Result<Number, WireError> {
        let offset = self.at;
        let x = Number {
            negative: self.boolean()?,
            mantissa: self.u64()?,
            exponent: self.int()?,
        };
        let mut encoded = Vec::new();
        number(&mut encoded, x).map_err(|_| WireError::NonCanonical(offset))?;
        Ok(x)
    }
    pub(crate) fn numeric_type(&mut self) -> Result<NumericType, WireError> {
        let offset = self.at;
        match self.u8()? {
            0 => Ok(NumericType::Fractional),
            1 => Ok(NumericType::Integral {
                maximum: self.u64()?,
                offset: self.int()?,
                sqrt: self.u64()?,
                shift: self.u64()?,
            }),
            actual => Err(WireError::BadNumericType { offset, actual }),
        }
    }
    pub(crate) fn position(&self) -> usize {
        self.at
    }
    pub(crate) fn done(&self) -> Result<(), WireError> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(WireError::Trailing {
                offset: self.at,
                remaining: self.bytes.len() - self.at,
            })
        }
    }
}

pub(crate) fn read_envelope(expected: u8, input: &[u8]) -> Result<&[u8], WireError> {
    let mut r = Reader::new(input);
    if r.take(4)? != MAGIC {
        return Err(WireError::BadMagic);
    }
    let version = r.u8()?;
    if version != VERSION {
        return Err(WireError::BadVersion(version));
    }
    let tag = r.u8()?;
    if tag != expected {
        return Err(WireError::BadTag(expected, tag));
    }
    let offset = r.position();
    let declared = r.u32()? as usize;
    if declared > MAX_WIRE_BYTES {
        return Err(WireError::BadLength { offset, declared });
    }
    let payload = r.take(declared)?;
    r.done()?;
    Ok(payload)
}
