#[path = "vectors/lending_canonical.rs"]
mod lending_canonical;
#[path = "vectors/lending_fixture.rs"]
mod lending_fixture;
#[path = "vectors/lending_malformed.rs"]
mod lending_malformed;

use crate::{lending_abi, lending_manifest};
use ledger::lending_adapter::lossless::{build_schedule, has_expired};

pub fn run() -> usize {
    lending_abi::initialize();
    for (now, expiry, exclusive, expected) in [
        (10, 10, false, true),
        (10, 10, true, false),
        (11, 10, true, true),
        (9, 10, false, false),
    ] {
        let lean = lending_abi::expired(now, expiry, exclusive);
        assert_eq!(lean, expected, "Lean hasExpired boundary");
        assert_eq!(
            lean,
            has_expired(now, expiry, exclusive),
            "Lean and Quaxar hasExpired boundary"
        );
    }
    for (two_step, expected_start) in [(false, 99), (true, 7)] {
        let lean = lending_abi::schedule(60, 3, 10, 7, 99, two_step);
        let quaxar = build_schedule(Some(60), Some(3), Some(10), 7, 99, two_step);
        assert_eq!(
            lean,
            [
                quaxar.payment_interval,
                quaxar.payment_total,
                quaxar.grace_period,
                quaxar.start_date,
                0
            ]
        );
        assert_eq!(lean[3], expected_start, "schedule start association");
    }
    let malformed_checks = lending_malformed::run();
    assert_eq!(
        malformed_checks, 265,
        "Lending malformed finite grid remains fully covered"
    );
    lending_canonical::run();
    assert_eq!(
        lending_abi::complete_adapter(),
        lending_manifest::SOURCE_EXPORTS
    );
    lending_manifest::SOURCE_EXPORTS + malformed_checks + 27 + 1
}
