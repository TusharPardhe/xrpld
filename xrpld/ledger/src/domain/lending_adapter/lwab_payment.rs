//! Exact LWAB LoanPay routes 6--8 and 22--24.
//! Raw transitions expose the modeled state; terminal routes associate the
//! successful vault exactly once, leaving rejected results uncommitted.
use super::{
    accept::associate,
    lwab_create_math as math,
    lwab_primitive::{self as p, Reader, WireError},
    lwab_records as records,
    lwab_types::*,
};
use basics::number::{NumberParts, RoundingMode};

const INTERNAL: u8 = 1;
const EXPIRED: u8 = 12;
const KILLED: u8 = 23;
const TOO_SOON: u8 = 40;
const INSUFFICIENT: u8 = 41;
#[derive(Debug)]
enum Outcome {
    Value(LendingState),
    Rejected(u8),
    Model(u8),
}

pub(super) fn dispatch(input: &[u8], kind: u8, terminal: bool) -> Vec<u8> {
    let route = if terminal { kind + 16 } else { kind };
    let req = match p::read_envelope(route, input).and_then(|b| read(b, kind)) {
        Ok(x) => x,
        Err(e) => return super::finish(route, Err(e)),
    };
    let result = match kind {
        6 => regular(req),
        7 => late(req),
        8 => full(req),
        _ => unreachable!(),
    };
    let payload = match result {
        Outcome::Value(state) => {
            let state = if terminal {
                match associate(state.vault) {
                    Ok(v) => LendingState { vault: v, ..state },
                    Err(e) => return super::finish(route, Ok(vec![1, e])),
                }
            } else {
                state
            };
            let mut x = vec![0, 0];
            records::state(&mut x, state).expect("canonical payment state");
            x
        }
        Outcome::Rejected(t) => vec![0, 1, t],
        Outcome::Model(e) => vec![1, e],
    };
    super::finish(route, Ok(payload))
}
#[derive(Clone, Copy)]
struct Request {
    base: BrokerRequest,
    ty: PaymentType,
    amount: Number,
    now: u32,
}
fn read(body: &[u8], kind: u8) -> Result<Request, WireError> {
    let mut r = Reader::new(body);
    let base = BrokerRequest {
        loan: records::read_loan(&mut r)?,
        vault: records::read_vault(&mut r)?,
        broker: records::read_broker(&mut r)?,
    };
    let ty = if kind == 6 {
        match r.u8()? {
            0 => PaymentType::Regular,
            1 => PaymentType::Late,
            2 => PaymentType::Full,
            3 => PaymentType::Overpayment,
            x => return Err(WireError::BadTag(0, x)),
        }
    } else {
        if kind == 7 {
            PaymentType::Late
        } else {
            PaymentType::Full
        }
    };
    let amount = r.number()?;
    let now = r.u32()?;
    r.done()?;
    Ok(Request {
        base,
        ty,
        amount,
        now,
    })
}
fn raw(n: Number) -> Result<NumberParts, Outcome> {
    math::raw(n).map_err(Outcome::Model)
}
fn add(a: NumberParts, b: NumberParts) -> Result<NumberParts, Outcome> {
    math::nearest(|| a.try_add(b)).map_err(Outcome::Model)
}
fn sub(a: NumberParts, b: NumberParts) -> Result<NumberParts, Outcome> {
    math::nearest(|| a.try_sub(b)).map_err(Outcome::Model)
}
fn mul(a: NumberParts, b: NumberParts) -> Result<NumberParts, Outcome> {
    math::nearest(|| a.try_mul(b)).map_err(Outcome::Model)
}
fn div(a: NumberParts, b: NumberParts) -> Result<NumberParts, Outcome> {
    math::nearest(|| a.try_div(b)).map_err(Outcome::Model)
}
fn round(
    nt: NumericType,
    n: NumberParts,
    mode: RoundingMode,
    scale: i32,
) -> Result<NumberParts, Outcome> {
    math::round(nt, n, mode, scale).map_err(Outcome::Model)
}
fn scale(v: Vault) -> Result<i32, Outcome> {
    math::exponent(v.numeric_type, raw(v.assets_total)?).map_err(Outcome::Model)
}
fn fee(nt: NumericType, n: NumberParts, rate: u16, s: i32) -> Result<NumberParts, Outcome> {
    math::management_fee(nt, n, rate, s).map_err(Outcome::Model)
}
fn rate(rate: u32, seconds: u32) -> Result<NumberParts, Outcome> {
    math::periodic_rate(rate, seconds).map_err(Outcome::Model)
}
fn amount_due(
    total: NumberParts,
    extra_i: NumberParts,
    extra_f: NumberParts,
) -> Result<NumberParts, Outcome> {
    add(add(total, extra_i)?, extra_f)
}
fn regular(r: Request) -> Outcome {
    let l = r.base.loan;
    if l.next_payment_due_date == 0 {
        return Outcome::Rejected(INTERNAL);
    }
    if r.now > l.next_payment_due_date {
        return Outcome::Rejected(EXPIRED);
    };
    match r.ty {
        PaymentType::Late | PaymentType::Full => return Outcome::Rejected(INTERNAL),
        _ => {}
    };
    installments(r)
}
fn scheduled(
    l: Loan,
    v: Vault,
    b: LoanBroker,
) -> Result<(NumberParts, NumberParts, NumberParts, NumberParts, bool), Outcome> {
    let s = scale(v)?;
    let total = raw(l.total_value_outstanding)?;
    let principal = raw(l.principal_outstanding)?;
    let management = raw(l.management_fee_outstanding)?;
    let payment = round(
        v.numeric_type,
        raw(l.periodic_payment)?,
        RoundingMode::Upward,
        s,
    )?;
    if l.payment_remaining == 1 || total <= payment {
        return Ok((
            total,
            principal,
            management,
            sub(sub(total, principal)?, management)?,
            true,
        ));
    }
    let periodic = rate(l.rates.interest, l.schedule.payment_interval)?;
    let current_i = sub(sub(total, principal)?, management)?;
    let remaining = l.payment_remaining - 1;
    let target_p = math::implied_principal(raw(l.periodic_payment)?, periodic, remaining)
        .map_err(Outcome::Model)?;
    let target_total = mul(
        raw(l.periodic_payment)?,
        NumberParts::from_i64(i64::from(remaining)),
    )?;
    let target_gross = sub(target_total, target_p)?;
    let target_m = math::tenth_bips(
        target_gross,
        u32::from(b.management_fee_rate),
        RoundingMode::ToNearest,
    )
    .map_err(Outcome::Model)?;
    let target_i = sub(target_gross, target_m)?;
    let p = std::cmp::min(
        principal,
        std::cmp::max(
            NumberParts::zero(),
            sub(
                principal,
                round(v.numeric_type, target_p, RoundingMode::Upward, s)?,
            )?,
        ),
    );
    let room_i = sub(payment, p)?;
    let i = std::cmp::min(
        current_i,
        std::cmp::min(
            std::cmp::max(NumberParts::zero(), room_i),
            std::cmp::max(
                NumberParts::zero(),
                sub(
                    current_i,
                    round(v.numeric_type, target_i, RoundingMode::Downward, s)?,
                )?,
            ),
        ),
    );
    let room_m = sub(room_i, i)?;
    let m = std::cmp::min(
        management,
        std::cmp::min(
            std::cmp::max(NumberParts::zero(), room_m),
            std::cmp::max(
                NumberParts::zero(),
                sub(
                    management,
                    round(v.numeric_type, target_m, RoundingMode::ToNearest, s)?,
                )?,
            ),
        ),
    );
    let total = add(add(p, i)?, m)?;
    Ok((total, p, m, i, false))
}
fn cash(
    r: Request,
    total: NumberParts,
    p: NumberParts,
    m: NumberParts,
    interest: NumberParts,
    extra_i: NumberParts,
    extra_f: NumberParts,
    final_: bool,
) -> Outcome {
    let mut v = r.base.vault;
    let mut b = r.base.broker;
    let mut l = r.base.loan;
    let s = match scale(v) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let due = match amount_due(total, extra_i, extra_f) {
        Ok(x) => x,
        Err(e) => return e,
    };
    if match raw(r.amount) {
        Ok(x) => x,
        Err(e) => return e,
    } < due
    {
        return Outcome::Rejected(INSUFFICIENT);
    };
    let paid_i = match add(interest, extra_i) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let paid_f = match add(m, extra_f) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let cash = match round(
        v.numeric_type,
        match add(p, paid_i) {
            Ok(x) => x,
            Err(e) => return e,
        },
        RoundingMode::Downward,
        s,
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    v.assets_available = match add(
        match raw(v.assets_available) {
            Ok(x) => x,
            Err(e) => return e,
        },
        cash,
    ) {
        Ok(x) => math::wire(x),
        Err(e) => return e,
    };
    v.assets_total = match add(
        match raw(v.assets_total) {
            Ok(x) => x,
            Err(e) => return e,
        },
        paid_i,
    ) {
        Ok(x) => math::wire(x),
        Err(e) => return e,
    };
    b.debt_total = match round(
        v.numeric_type,
        match sub(
            match raw(b.debt_total) {
                Ok(x) => x,
                Err(e) => return e,
            },
            p,
        ) {
            Ok(x) => x,
            Err(e) => return e,
        },
        RoundingMode::ToNearest,
        s,
    ) {
        Ok(x) => math::wire(x),
        Err(e) => return e,
    };
    let min_cover = match math::tenth_bips(
        raw(b.debt_total).unwrap_or(NumberParts::zero()),
        b.cover_rate_minimum,
        RoundingMode::Upward,
    )
    .and_then(|x| math::round(v.numeric_type, x, RoundingMode::Upward, s))
    {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    if raw(b.cover_available).unwrap_or(NumberParts::zero()) < min_cover {
        b.cover_available = match add(
            raw(b.cover_available).unwrap_or(NumberParts::zero()),
            paid_f,
        ) {
            Ok(x) => math::wire(x),
            Err(e) => return e,
        }
    };
    if !math::lawful(v) {
        return Outcome::Model(8);
    };
    if final_ {
        l.total_value_outstanding = Number::ZERO;
        l.principal_outstanding = Number::ZERO;
        l.management_fee_outstanding = Number::ZERO;
        l.payment_remaining = 0;
        l.previous_payment_due_date = l.next_payment_due_date;
        l.next_payment_due_date = 0
    } else {
        l.total_value_outstanding = match sub(raw(l.total_value_outstanding).unwrap(), total) {
            Ok(x) => math::wire(x),
            Err(e) => return e,
        };
        l.principal_outstanding = match sub(raw(l.principal_outstanding).unwrap(), p) {
            Ok(x) => math::wire(x),
            Err(e) => return e,
        };
        l.management_fee_outstanding = match sub(raw(l.management_fee_outstanding).unwrap(), m) {
            Ok(x) => math::wire(x),
            Err(e) => return e,
        };
        l.payment_remaining = l.payment_remaining.wrapping_sub(1);
        l.previous_payment_due_date = l.next_payment_due_date;
        l.next_payment_due_date = l
            .next_payment_due_date
            .wrapping_add(l.schedule.payment_interval)
    };
    if raw(v.assets_available).unwrap() > raw(v.assets_total).unwrap() {
        return Outcome::Rejected(INTERNAL);
    };
    Outcome::Value(LendingState {
        vault_identity: l.vault_identity,
        vault: v,
        broker: b,
        loan: l,
    })
}
fn installments(r: Request) -> Outcome {
    let mut r = r;
    if r.base.loan.payment_remaining == 0 {
        return Outcome::Rejected(INSUFFICIENT);
    }
    for _ in 0..100 {
        if r.base.loan.payment_remaining == 0 {
            break;
        };
        let (t, p, m, i, last) = match scheduled(r.base.loan, r.base.vault, r.base.broker) {
            Ok(x) => x,
            Err(e) => return e,
        };
        let due = match amount_due(
            t,
            NumberParts::zero(),
            raw(r.base.loan.fees.service).unwrap_or(NumberParts::zero()),
        ) {
            Ok(x) => x,
            Err(e) => return e,
        };
        if raw(r.amount).unwrap_or(NumberParts::zero()) < due {
            return if r.base.loan.payment_remaining == 0 {
                Outcome::Rejected(KILLED)
            } else {
                Outcome::Rejected(INSUFFICIENT)
            };
        };
        match cash(
            r,
            t,
            p,
            m,
            i,
            NumberParts::zero(),
            raw(r.base.loan.fees.service).unwrap_or(NumberParts::zero()),
            last,
        ) {
            Outcome::Value(s) => {
                r.base = BrokerRequest {
                    loan: s.loan,
                    vault: s.vault,
                    broker: s.broker,
                };
                if last {
                    return Outcome::Value(s);
                }
            }
            x => return x,
        }
    }
    Outcome::Value(LendingState {
        vault_identity: r.base.loan.vault_identity,
        vault: r.base.vault,
        broker: r.base.broker,
        loan: r.base.loan,
    })
}
fn late(r: Request) -> Outcome {
    let l = r.base.loan;
    if l.next_payment_due_date == 0 {
        return Outcome::Rejected(INTERNAL);
    }
    if r.now <= l.next_payment_due_date {
        return Outcome::Rejected(TOO_SOON);
    };
    let (t, p, m, i, last) = match scheduled(l, r.base.vault, r.base.broker) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let overdue = r.now - l.next_payment_due_date;
    let late_i = match rate(l.rates.late_interest, overdue)
        .and_then(|x| mul(raw(l.principal_outstanding)?, x))
    {
        Ok(x) => x,
        Err(e) => return e,
    };
    let s = match scale(r.base.vault) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let rounded = match round(
        r.base.vault.numeric_type,
        late_i,
        RoundingMode::ToNearest,
        s,
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let mf = match fee(
        r.base.vault.numeric_type,
        rounded,
        r.base.broker.management_fee_rate,
        s,
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let net = match sub(rounded, mf) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let service_late = match add(
        raw(l.fees.service).unwrap_or(NumberParts::zero()),
        raw(l.fees.late_payment).unwrap_or(NumberParts::zero()),
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let ef = match add(service_late, mf) {
        Ok(x) => x,
        Err(e) => return e,
    };
    cash(r, t, p, m, i, net, ef, last)
}
fn full(r: Request) -> Outcome {
    let l = r.base.loan;
    if l.next_payment_due_date == 0 {
        return Outcome::Rejected(INTERNAL);
    }
    if r.now > l.next_payment_due_date {
        return Outcome::Rejected(EXPIRED);
    }
    if l.payment_remaining <= 1 {
        return Outcome::Rejected(KILLED);
    };
    let s = match scale(r.base.vault) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let periodic = match rate(l.rates.interest, l.schedule.payment_interval) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let theoretical = match math::implied_principal(
        raw(l.periodic_payment).unwrap(),
        periodic,
        l.payment_remaining,
    ) {
        Ok(x) => x,
        Err(e) => return Outcome::Model(e),
    };
    let accrued = if r.now <= l.previous_payment_due_date.max(l.schedule.start_date) {
        NumberParts::zero()
    } else {
        let elapsed = NumberParts::from_i64(i64::from(
            r.now - l.previous_payment_due_date.max(l.schedule.start_date),
        ));
        let numerator = match mul(
            match mul(theoretical, periodic) {
                Ok(x) => x,
                Err(e) => return e,
            },
            elapsed,
        ) {
            Ok(x) => x,
            Err(e) => return e,
        };
        match div(
            numerator,
            NumberParts::from_i64(i64::from(l.schedule.payment_interval)),
        ) {
            Ok(x) => x,
            Err(e) => return e,
        }
    };
    let penalty =
        match math::tenth_bips(theoretical, l.rates.close_interest, RoundingMode::ToNearest) {
            Ok(x) => x,
            Err(e) => return Outcome::Model(e),
        };
    let gross = match add(accrued, penalty) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let rounded = match round(r.base.vault.numeric_type, gross, RoundingMode::Downward, s) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let mf = match fee(
        r.base.vault.numeric_type,
        rounded,
        r.base.broker.management_fee_rate,
        s,
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let total_after_principal = match sub(
        raw(l.total_value_outstanding).unwrap(),
        raw(l.principal_outstanding).unwrap(),
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let state_i = match sub(
        total_after_principal,
        raw(l.management_fee_outstanding).unwrap(),
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let close = match round(
        r.base.vault.numeric_type,
        raw(l.fees.close_payment).unwrap(),
        RoundingMode::ToNearest,
        s,
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let untracked_i = match sub(
        match sub(rounded, mf) {
            Ok(x) => x,
            Err(e) => return e,
        },
        state_i,
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    let untracked_f = match sub(
        match add(close, mf) {
            Ok(x) => x,
            Err(e) => return e,
        },
        raw(l.management_fee_outstanding).unwrap(),
    ) {
        Ok(x) => x,
        Err(e) => return e,
    };
    cash(
        r,
        raw(l.total_value_outstanding).unwrap(),
        raw(l.principal_outstanding).unwrap(),
        raw(l.management_fee_outstanding).unwrap(),
        state_i,
        untracked_i,
        untracked_f,
        true,
    )
}
