//! Direct Lean↔Quaxar material LWAB payment-route evidence (6/7/8, 22/23/24).
use crate::{
    lending_abi, lending_create,
    lending_wire::{self, *},
};

pub const EXPORT_IDS: [&str; 6] = [
    "lean_lending_raw_regular_payment_wire",
    "lean_lending_raw_late_payment_wire",
    "lean_lending_raw_full_payment_wire",
    "lean_lending_terminal_regular_payment_wire",
    "lean_lending_terminal_late_payment_wire",
    "lean_lending_terminal_full_payment_wire",
];
fn created() -> LendingState {
    let input =
        lending_wire::encode_request(3, Request::Create(lending_create::create(false, 0))).unwrap();
    let bytes = ledger::lending_lwab::dispatch_route(3, &input);
    let Response::Ok(Payload::State(Lifecycle::Value(value))) =
        lending_wire::decode_response(3, &bytes).unwrap()
    else {
        panic!("payment fixture creation")
    };
    value
}
fn amount() -> Number {
    Number {
        negative: false,
        mantissa: 1_000_000_000_000_000_000,
        exponent: -16,
    }
}
fn frame(tag: u8, state: LendingState, now: u32) -> Vec<u8> {
    let base = BrokerRequest {
        loan: state.loan,
        vault: state.vault,
        broker: state.broker,
    };
    let request = match tag {
        6 | 22 => Request::Payment(PaymentRequest {
            base,
            payment_type: PaymentType::Regular,
            amount: amount(),
            now,
        }),
        _ => Request::Amount(AmountRequest {
            base,
            amount: amount(),
            now,
        }),
    };
    lending_wire::encode_request(tag, request).unwrap()
}
fn compare(tag: u8, input: &[u8], name: &str) -> Response<Payload> {
    let lean = lending_abi::wire(tag.into(), input);
    let quaxar = ledger::lending_lwab::dispatch_route(tag, input);
    assert_eq!(quaxar, lean, "{name}: exact complete response");
    assert_eq!(
        ledger::lending_lwab::dispatch_route(tag, input),
        quaxar,
        "{name}: repeatability"
    );
    let typed = lending_wire::decode_response(tag, &lean).unwrap();
    assert_eq!(
        lending_wire::decode_response(tag, &quaxar),
        Ok(typed),
        "{name}: typed equality"
    );
    typed
}
fn malformed(tag: u8, seed: &[u8]) -> usize {
    let mut wrong = seed[..10].to_vec();
    wrong[5] = if tag < 17 { tag + 16 } else { tag - 16 };
    let mut trailing = seed.to_vec();
    trailing.push(0);
    for input in [
        b"NOPE".as_slice(),
        b"LWAB\x02".as_slice(),
        wrong.as_slice(),
        &seed[..9],
        trailing.as_slice(),
    ] {
        compare(tag, input, "malformed LWAB frame");
    }
    5
}
pub fn run() -> usize {
    let state = created();
    let mut checks = 0;
    for tag in [6, 7, 8, 22, 23, 24] {
        let now = match tag {
            7 | 23 => state.loan.next_payment_due_date.wrapping_add(1),
            _ => state.loan.next_payment_due_date,
        };
        let wire = frame(tag, state, now);
        let typed = compare(tag, &wire, "payment success/guard full material");
        assert!(
            matches!(typed, Response::Ok(Payload::State(_))),
            "state lifecycle route"
        );
        checks += 1 + malformed(tag, &wire);
        let mut zero = state;
        zero.loan.next_payment_due_date = 0;
        compare(tag, &frame(tag, zero, now), "zero due-date internal guard");
        checks += 1;
        if matches!(tag, 6 | 22) {
            let mut empty = state;
            empty.loan.payment_remaining = 0;
            compare(tag, &frame(tag, empty, now), "zero scheduled-payment guard");
            checks += 1;
        }
    }
    checks
}
