fn build(
    r: CreateRequest,
    principal: NumberParts,
    scale: i32,
    periodic: NumberParts,
    total: NumberParts,
    outstanding: NumberParts,
    management: NumberParts,
) -> Outcome {
    let debt_before = match math::raw(r.broker.debt_total) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let debt = match math::nearest(|| debt_before.try_add(principal)) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let maximum = match math::raw(r.broker.debt_maximum) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    if maximum != NumberParts::zero() && maximum < debt {
        return Outcome::Rejected(math::TER_LIMIT_EXCEEDED);
    }
    let cover = match math::tenth_bips(debt, r.broker.cover_rate_minimum, RoundingMode::Upward)
        .and_then(|x| math::round(r.vault.numeric_type, x, RoundingMode::Upward, scale))
    {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let available_cover = match math::raw(r.broker.cover_available) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    if available_cover < cover {
        return Outcome::Rejected(math::TER_INSUFFICIENT_FUNDS);
    }
    let mut vault = r.vault;
    let available_before = match math::raw(vault.assets_available) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    vault.assets_available =
        match math::nearest(|| available_before.try_sub(principal)).map(math::wire) {
            Ok(x) => x,
            Err(e) => return Outcome::Model(e),
        };
    if r.pending {
        let reserved_before = match math::raw(vault.assets_reserved) {
            Ok(x) => x,
            Err(e) => return Outcome::Model(e),
        };
        vault.assets_reserved =
            match math::nearest(|| reserved_before.try_add(principal)).map(math::wire) {
                Ok(x) => x,
                Err(e) => return Outcome::Model(e),
            };
    }
    if !math::lawful(vault) {
        return Outcome::Model(math::ERROR_NOT_LAWFUL);
    }
    let debt_adjusted = match math::nearest(|| debt_before.try_add(principal)) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let debt_after = match math::round(
        r.vault.numeric_type,
        debt_adjusted,
        RoundingMode::ToNearest,
        scale,
    )
    .map(math::wire)
    {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let mut broker = r.broker;
    broker.debt_total = debt_after;
    broker.loan_count = match broker.loan_count.checked_add(1) {
        Some(x) => x,
        None => return Outcome::Model(math::TER_INTERNAL),
    };
    let loan = Loan {
        identity: r.loan_identity,
        vault_identity: r.vault_identity,
        rates: r.rates,
        fees: r.fees,
        schedule: r.schedule,
        payment_remaining: r.schedule.payment_total,
        periodic_payment: math::wire(periodic),
        principal_outstanding: math::wire(outstanding),
        total_value_outstanding: math::wire(total),
        management_fee_outstanding: math::wire(management),
        loan_scale: i64::from(scale),
        previous_payment_due_date: 0,
        next_payment_due_date: r
            .schedule
            .start_date
            .wrapping_add(r.schedule.payment_interval),
        pending: r.pending,
        impaired: false,
        defaulted: false,
        allows_overpayment: r.allows_overpayment,
    };
    Outcome::Value(LendingState {
        vault_identity: r.vault_identity,
        vault,
        broker,
        loan,
    })
}
