//! Direct Lean↔Quaxar parity vectors for raw broker/cover tags 12 through 16.
#[path = "vectors/lending_broker_fixture.rs"]
mod lending_broker_fixture;

use crate::{
    lending_abi,
    lending_wire::{self, *},
};
use lending_broker_fixture::{broker, fractional, integral, n};

pub const EXPORT_IDS: [&str; 5] = [
    "lean_lending_raw_broker_create_wire",
    "lean_lending_raw_broker_update_wire",
    "lean_lending_raw_cover_validate_wire",
    "lean_lending_raw_cover_deposit_wire",
    "lean_lending_raw_cover_withdraw_wire",
];
fn frame(tag: u8, request: Request) -> Vec<u8> {
    lending_wire::encode_request(tag, request).expect("canonical raw broker/cover request")
}
fn compare(tag: u8, input: &[u8], name: &str) -> Response<Payload> {
    let lean = lending_abi::wire(tag.into(), input);
    let quaxar = ledger::lending_lwab::dispatch_route(tag, input);
    assert_eq!(quaxar, lean, "{name}: exact full response bytes");
    assert_eq!(
        ledger::lending_lwab::dispatch_route(tag, input),
        quaxar,
        "{name}: repeatable"
    );
    let typed = lending_wire::decode_response(tag, &lean).expect("Lean result decodes");
    assert_eq!(
        lending_wire::decode_response(tag, &quaxar),
        Ok(typed),
        "{name}: all typed fields"
    );
    typed
}
fn malformed(tag: u8, seed: &[u8]) -> usize {
    let mut wrong = seed[..10].to_vec();
    wrong[5] = if tag == 12 { 13 } else { 12 };
    let mut trailing = seed.to_vec();
    trailing.push(0);
    for input in [
        b"NOPE".as_slice(),
        b"LWAB\x02".as_slice(),
        wrong.as_slice(),
        &seed[..9],
        trailing.as_slice(),
    ] {
        compare(tag, input, "malformed/noncanonical envelope");
    }
    let body = (10..seed.len())
        .find_map(|at| {
            let mut value = seed.to_vec();
            value[at] = 2;
            (lending_abi::wire(tag.into(), &value).get(10) == Some(&1)).then_some(value)
        })
        .expect("each broker/cover frame reaches a malformed field decoder");
    compare(tag, &body, "malformed field");
    6
}
pub fn run() -> usize {
    let create_default = Request::BrokerCreate(BrokerCreateRequest {
        identity: broker().identity,
        debt_maximum: None,
        management_fee_rate: None,
        cover_rate_minimum: None,
        cover_rate_liquidation: None,
    });
    let create_options = Request::BrokerCreate(BrokerCreateRequest {
        identity: broker().identity,
        debt_maximum: Some(n(1_000_000_000_000_000_000, -17)),
        management_fee_rate: Some(u16::MAX),
        cover_rate_minimum: Some(u32::MAX),
        cover_rate_liquidation: Some(100_000),
    });
    let mut update = broker();
    update.debt_maximum = n(1_000_000_000_000_000_000, -17);
    let update_absent = Request::BrokerUpdate(BrokerUpdateRequest {
        broker: update,
        debt_maximum: None,
    });
    let update_lower = Request::BrokerUpdate(BrokerUpdateRequest {
        broker: update,
        debt_maximum: Some(n(1_000_000_000_000_000_000, -19)),
    });
    let validate_zero = Request::CoverValidate(CoverValidateRequest {
        numeric_type: NumericType::Fractional,
        cover_available: broker().cover_available,
        amount: fractional(0, -100),
    });
    let validate_dust = Request::CoverValidate(CoverValidateRequest {
        numeric_type: NumericType::Fractional,
        cover_available: broker().cover_available,
        amount: fractional(1_000_000_000_000_000, -40),
    });
    let validate_integral = Request::CoverValidate(CoverValidateRequest {
        numeric_type: NumericType::Integral {
            maximum: 100_000_000_000_000_000,
            offset: 17,
            sqrt: 3_000_000_000,
            shift: 2_095_475_792,
        },
        cover_available: broker().cover_available,
        amount: integral(7),
    });
    let validate_overflow = Request::CoverValidate(CoverValidateRequest {
        numeric_type: NumericType::Fractional,
        cover_available: n(1_000_000_000_000_000_000, 78),
        amount: fractional(1_000_000_000_000_000, -16),
    });
    let deposit = Request::Cover(CoverRequest {
        broker: broker(),
        numeric_type: NumericType::Fractional,
        amount: fractional(1_000_000_000_000_000, -16),
    });
    let dust = Request::Cover(CoverRequest {
        broker: broker(),
        numeric_type: NumericType::Fractional,
        amount: fractional(1_000_000_000_000_000, -40),
    });
    let integral_cover = Request::Cover(CoverRequest {
        broker: broker(),
        numeric_type: NumericType::Integral {
            maximum: 100_000_000_000_000_000,
            offset: 17,
            sqrt: 3_000_000_000,
            shift: 2_095_475_792,
        },
        amount: integral(7),
    });
    let mut negative_amount = fractional(1_000_000_000_000_000, -16);
    negative_amount.negative = true;
    let negative_cover = Request::Cover(CoverRequest {
        broker: broker(),
        numeric_type: NumericType::Fractional,
        amount: negative_amount,
    });
    let mixed_cover = Request::Cover(CoverRequest {
        broker: broker(),
        numeric_type: NumericType::Integral {
            maximum: 100_000_000_000_000_000,
            offset: 17,
            sqrt: 3_000_000_000,
            shift: 2_095_475_792,
        },
        amount: fractional(1_000_000_000_000_000, -16),
    });
    let overflow_cover = Request::Cover(CoverRequest {
        broker: LoanBroker {
            cover_available: n(1_000_000_000_000_000_000, 78),
            ..broker()
        },
        numeric_type: NumericType::Fractional,
        amount: fractional(1_000_000_000_000_000, -16),
    });
    let mut checks = 0;
    for (tag, request, name) in [
        (12, create_default, "create defaults every optional field"),
        (12, create_options, "create preserves full option values"),
        (13, update_absent, "update absent retains debt maximum"),
        (
            13,
            update_lower,
            "raw update does not invent validation guard",
        ),
        (14, validate_zero, "zero cover precision loss"),
        (14, validate_dust, "cover scale dust precision loss"),
        (14, validate_integral, "integral cover validation"),
        (14, validate_overflow, "cover scale conversion overflow"),
        (15, deposit, "deposit downward cover rounding and credit"),
        (15, dust, "deposit unroundable internal result"),
        (16, deposit, "withdraw raw debit without balance guard"),
        (16, dust, "withdraw unroundable internal result"),
        (16, integral_cover, "integral cover raw debit"),
        (
            15,
            negative_cover,
            "negative credit remains a typed raw movement",
        ),
        (
            15,
            mixed_cover,
            "requested numeric type controls cover scale",
        ),
        (15, overflow_cover, "deposit conversion error framing"),
        (16, overflow_cover, "withdraw conversion error framing"),
    ] {
        let input = frame(tag, request);
        compare(tag, &input, name);
        checks += 1 + malformed(tag, &input);
    }
    checks
}
