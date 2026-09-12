fn power_minus_one(rate: NumberParts, payments: u32) -> Result<NumberParts, u8> {
    if payments == 0 || rate == NumberParts::zero() {
        return Ok(NumberParts::zero());
    }
    let n = NumberParts::from_i64(i64::from(payments));
    let nrate = nearest(|| n.try_mul(rate))?;
    let threshold = NumberParts::unchecked(false, 1_000_000_000_000_000_000, -27);
    if nrate >= threshold {
        let base = nearest(|| NumberParts::one(MantissaScale::Large).try_add(rate))?;
        let raised = power(base, payments).map_err(|_| TER_INTERNAL)?;
        return nearest(|| raised.try_sub(NumberParts::one(MantissaScale::Large)));
    }
    let mut term = nearest(|| n.try_mul(rate))?;
    let mut sum = term;
    for index in 1..payments {
        term = nearest(|| term.try_mul(rate))?;
        term = nearest(|| term.try_mul(NumberParts::from_i64(i64::from(payments - index))))?;
        term = nearest(|| term.try_div(NumberParts::from_i64(i64::from(index + 1))))?;
        let next = nearest(|| sum.try_add(term))?;
        if next == sum {
            break;
        }
        sum = next;
    }
    Ok(sum)
}
fn factor(rate: NumberParts, payments: u32) -> Result<NumberParts, u8> {
    if payments == 0 {
        return Ok(NumberParts::zero());
    }
    let n = NumberParts::from_i64(i64::from(payments));
    if rate == NumberParts::zero() {
        return nearest(|| NumberParts::one(MantissaScale::Large).try_div(n));
    }
    let minus = power_minus_one(rate, payments)?;
    let raised = nearest(|| NumberParts::one(MantissaScale::Large).try_add(minus))?;
    let numerator = nearest(|| rate.try_mul(raised))?;
    nearest(|| numerator.try_div(minus))
}
pub(super) fn payment(
    principal: NumberParts,
    rate: NumberParts,
    payments: u32,
) -> Result<NumberParts, u8> {
    if principal == NumberParts::zero() || payments == 0 {
        return Ok(NumberParts::zero());
    }
    let factor = factor(rate, payments)?;
    nearest(|| principal.try_mul(factor))
}
pub(super) fn implied_principal(
    payment: NumberParts,
    rate: NumberParts,
    payments: u32,
) -> Result<NumberParts, u8> {
    if payments == 0 {
        return Ok(NumberParts::zero());
    }
    let factor = factor(rate, payments)?;
    nearest(|| payment.try_div(factor))
}
pub(super) fn management_fee(
    nt: NumericType,
    value: NumberParts,
    rate: u16,
    scale: i32,
) -> Result<NumberParts, u8> {
    round(
        nt,
        tenth_bips(value, u32::from(rate), RoundingMode::ToNearest)?,
        RoundingMode::Downward,
        scale,
    )
}
