//! Full-material LWAB vectors for raw Loan.accept (4) and terminal accept (20).

use crate::{
    lending_abi,
    lending_wire::{self, *},
};

pub const EXPORT_IDS: [&str; 2] = [
    "lean_lending_raw_accept_wire",
    "lean_lending_terminal_accept_wire",
];

#[path = "vectors/lending_accept_fixture.rs"]
mod fixture;
use fixture::{number, request, request_with_type};

fn compare(tag: u8, input: &[u8], name: &str) -> Response<Payload> {
    let lean = lending_abi::wire(tag.into(), input);
    let quaxar = ledger::lending_lwab::dispatch_route(tag, input);
    assert_eq!(quaxar, lean, "{name}: complete response bytes");
    assert_eq!(
        ledger::lending_lwab::dispatch_route(tag, input),
        quaxar,
        "{name}: repeatable Quaxar response",
    );
    let lean_typed = lending_wire::decode_response(tag, &lean).expect("Lean typed response");
    let quaxar_typed = lending_wire::decode_response(tag, &quaxar).expect("Quaxar typed response");
    assert_eq!(quaxar_typed, lean_typed, "{name}: complete decoded result");
    lean_typed
}

fn frame(tag: u8, request: Request) -> Vec<u8> {
    lending_wire::encode_request(tag, request).expect("canonical accept request")
}

fn malformed(tag: u8, seed: &[u8]) -> usize {
    let mut wrong_tag = seed[..10].to_vec();
    wrong_tag[5] = if tag == 4 { 20 } else { 4 };
    let mut bad_length = seed[..10].to_vec();
    bad_length[6..10].copy_from_slice(&65_537_u32.to_le_bytes());
    let mut trailing = seed.to_vec();
    trailing.push(0);
    for (name, input) in [
        ("magic", b"NOPE".as_slice()),
        ("version", b"LWAB\x02".as_slice()),
        ("tag", wrong_tag.as_slice()),
        ("truncated", &seed[..9]),
        ("length", bad_length.as_slice()),
        ("trailing", trailing.as_slice()),
    ] {
        compare(tag, input, name);
    }
    let mut checks = 6;
    for class in [5, 10] {
        let input = (10..seed.len())
            .find_map(|at| {
                let mut candidate = seed.to_vec();
                candidate[at] = 2;
                (lending_abi::wire(tag.into(), &candidate).get(11) == Some(&class))
                    .then_some(candidate)
            })
            .expect("reachable accept decoder class");
        compare(tag, &input, "malformed body");
        checks += 1;
    }
    checks
}

pub fn run() -> usize {
    let one = number(-18);
    let raw = frame(4, request(true, one, one, -18));
    let terminal = frame(20, request(true, one, one, -18));
    let raw_typed = compare(4, &raw, "raw success retains pre-association state");
    let terminal_typed = compare(20, &terminal, "terminal success associates once");
    let Response::Ok(Payload::LoanVault(Lifecycle::Value(raw_value))) = raw_typed else {
        panic!("raw accept succeeds")
    };
    let Response::Ok(Payload::LoanVault(Lifecycle::Value(terminal_value))) = terminal_typed else {
        panic!("terminal accept succeeds")
    };
    assert!(
        !raw_value.loan.pending && !terminal_value.loan.pending,
        "accept clears pending only"
    );
    assert_eq!(
        raw_value.vault.assets_reserved,
        Number::ZERO,
        "raw subtracts reserved exactly"
    );
    assert_eq!(
        raw_value.vault, terminal_value.vault,
        "lawful terminal association preserves represented values"
    );
    let native = NumericType::Integral {
        maximum: 100_000_000_000_000_000,
        offset: 17,
        sqrt: 3_000_000_000,
        shift: 2_095_475_792,
    };
    let integral = compare(
        20,
        &frame(
            20,
            request_with_type(true, number(-18), number(-18), -18, native),
        ),
        "terminal native association preserves all numeric-type fields",
    );
    assert!(matches!(
        integral,
        Response::Ok(Payload::LoanVault(Lifecycle::Value(LoanVault { vault, .. })))
            if vault.numeric_type == native
    ));
    assert_eq!(
        compare(
            20,
            &frame(20, request_with_type(true, number(0), number(0), 0, native)),
            "terminal native association out-of-range",
        ),
        Response::Ok(Payload::LoanVault(Lifecycle::ModelError(2)))
    );
    let underflow = compare(
        20,
        &frame(20, request(true, number(-100), number(-100), -100)),
        "terminal fractional association underflows to canonical zero",
    );
    assert!(matches!(
        underflow,
        Response::Ok(Payload::LoanVault(Lifecycle::Value(LoanVault { vault, .. })))
            if vault.assets_total == Number::ZERO
                && vault.assets_available == Number::ZERO
                && vault.assets_reserved == Number::ZERO
                && vault.loss_unrealized == Number::ZERO
    ));
    compare(
        4,
        &frame(4, request(false, one, one, -18)),
        "raw intentionally has no preclaim gate",
    );
    let underflow = compare(
        4,
        &frame(4, request(true, Number::ZERO, one, -18)),
        "raw reserved subtraction retains no invented preclaim guard",
    );
    let Response::Ok(Payload::LoanVault(Lifecycle::Value(underflow_value))) = underflow else {
        panic!("raw accept preserves the modeled negative reserved result")
    };
    assert!(
        underflow_value.vault.assets_reserved.negative,
        "raw accept does not add an unmodeled reservation guard"
    );
    let maximum = Number {
        negative: false,
        mantissa: 9_999_999_999_999_999_990,
        exponent: 32_768,
    };
    let raw_overflow = compare(
        4,
        &frame(
            4,
            request(
                true,
                maximum,
                Number {
                    negative: true,
                    ..maximum
                },
                -18,
            ),
        ),
        "raw subtraction overflow",
    );
    assert_eq!(
        raw_overflow,
        Response::Ok(Payload::LoanVault(Lifecycle::ModelError(0)))
    );
    let terminal_error = compare(
        20,
        &frame(20, request(true, one, one, 81)),
        "terminal association failure is atomic",
    );
    assert!(matches!(
        terminal_error,
        Response::Ok(Payload::LoanVault(Lifecycle::ModelError(_)))
    ));
    let malformed = malformed(4, &raw) + malformed(20, &terminal);
    6 + malformed
}
