fn create(r: CreateRequest) -> Outcome {
    if !valid(r.vault_identity, r.broker.identity, r.loan_identity) {
        return Outcome::Rejected(TER_INVALID);
    }
    let principal = match math::raw(r.principal) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let available = match math::raw(r.vault.assets_available) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    if available < principal {
        return Outcome::Rejected(math::TER_INSUFFICIENT_FUNDS);
    }
    let assets_total = match math::raw(r.vault.assets_total) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let vault_scale = match math::exponent(r.vault.numeric_type, assets_total) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let rate = match math::periodic_rate(r.rates.interest, r.schedule.payment_interval) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let periodic = match math::payment(principal, rate, r.schedule.payment_total) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let mode = if rate == NumberParts::zero() {
        RoundingMode::ToNearest
    } else {
        RoundingMode::Upward
    };
    let amount = match math::nearest(|| {
        periodic.try_mul(NumberParts::from_i64(i64::from(r.schedule.payment_total)))
    }) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let total = match rounded(r.vault.numeric_type, amount, vault_scale, mode) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let outstanding = match rounded(
        r.vault.numeric_type,
        principal,
        vault_scale,
        RoundingMode::ToNearest,
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let total_interest = match math::nearest(|| total.try_sub(outstanding)) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let management = match math::management_fee(
        r.vault.numeric_type,
        total_interest,
        r.broker.management_fee_rate,
        vault_scale,
    ) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let first =
        match math::implied_principal(periodic, rate, r.schedule.payment_total).and_then(|start| {
            math::implied_principal(periodic, rate, r.schedule.payment_total.saturating_sub(1))
                .and_then(|next| math::nearest(|| start.try_sub(next)))
        }) {
            Ok(x) => x,
            Err(e) => return Outcome::Model(e),
        };
    for field in [
        r.principal,
        r.fees.origination,
        r.fees.service,
        r.fees.late_payment,
        r.fees.close_payment,
    ] {
        let field = match math::raw(field) {
            Ok(x) => x,
            Err(e) => return Outcome::Model(e),
        };
        match precisely(r.vault.numeric_type, field, vault_scale) {
            Ok(true) => {}
            Ok(false) => return Outcome::Rejected(math::TER_PRECISION_LOSS),
            Err(e) => return e,
        }
    }
    if (r.rates.interest != 0 && total_interest.signum() <= 0) || first.signum() <= 0 {
        return Outcome::Rejected(math::TER_PRECISION_LOSS);
    }
    if (r.rates.interest == 0 && total_interest.signum() > 0)
        || management.signum() < 0
        || total.signum() <= 0
        || periodic.signum() <= 0
    {
        return Outcome::Rejected(math::TER_INTERNAL);
    }
    let payment = match rounded(
        r.vault.numeric_type,
        periodic,
        vault_scale,
        RoundingMode::Upward,
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    if payment == NumberParts::zero() {
        return Outcome::Rejected(math::TER_PRECISION_LOSS);
    }
    let ratio = match math::nearest(|| total.try_div(payment)) {
        Ok(x) => x,
        Err(_) => return Outcome::Rejected(math::TER_PRECISION_LOSS),
    };
    let count = match ratio.try_to_i64() {
        Ok(x) => x,
        Err(_) => return Outcome::Rejected(math::TER_PRECISION_LOSS),
    };
    if count != i64::from(r.schedule.payment_total) {
        return Outcome::Rejected(math::TER_PRECISION_LOSS);
    }
    build(
        r,
        principal,
        vault_scale,
        periodic,
        total,
        outstanding,
        management,
    )
}
