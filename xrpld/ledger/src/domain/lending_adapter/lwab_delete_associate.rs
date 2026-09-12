fn associate_number(numeric_type: NumericType, value: Number) -> Result<Number, u8> {
    let raw = math::raw(value)?;
    match numeric_type {
        NumericType::Fractional => {
            if raw.mantissa == 0 || (-99..=80).contains(&raw.exponent) {
                Ok(math::wire(raw))
            } else if raw.exponent > 80 {
                Err(OVERFLOW)
            } else {
                Ok(Number::ZERO)
            }
        }
        NumericType::Integral { maximum, .. } => {
            let amount = if raw.mantissa == 0 {
                0
            } else if raw.exponent >= 0 {
                raw.mantissa
                    .checked_mul(10_u64.checked_pow(raw.exponent as u32).ok_or(OVERFLOW)?)
                    .ok_or(OVERFLOW)?
            } else if raw.exponent <= -20 {
                0
            } else {
                let divisor = 10_u64.pow((-raw.exponent) as u32);
                let quotient = raw.mantissa / divisor;
                quotient
                    + u64::from(
                        raw.mantissa % divisor > divisor / 2
                            || raw.mantissa % divisor == divisor / 2 && quotient % 2 == 1,
                    )
            };
            if amount > maximum {
                return Err(OUT_OF_RANGE);
            }
            Ok(math::wire(NumberParts::from_i64(if value.negative {
                -(amount as i64)
            } else {
                amount as i64
            })))
        }
    }
}

fn associate(vault: Vault) -> Result<Vault, u8> {
    let numeric_type = vault.numeric_type;
    let value = Vault {
        assets_total: associate_number(numeric_type, vault.assets_total)?,
        assets_available: associate_number(numeric_type, vault.assets_available)?,
        assets_reserved: associate_number(numeric_type, vault.assets_reserved)?,
        assets_maximum: vault
            .assets_maximum
            .map(|x| associate_number(numeric_type, x))
            .transpose()?,
        numeric_type,
        scale: vault.scale,
        shares_total: vault.shares_total,
        loss_unrealized: associate_number(numeric_type, vault.loss_unrealized)?,
    };
    math::lawful(value).then_some(value).ok_or(NOT_LAWFUL)
}
