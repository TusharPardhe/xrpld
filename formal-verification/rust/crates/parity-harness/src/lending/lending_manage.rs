//! Direct Lean↔Quaxar evidence for LoanManage tags 9/10/11 and 25/26/27.
use crate::{
    lending_abi, lending_create,
    lending_wire::{self, *},
};
pub const EXPORT_IDS: [&str; 6] = [
    "lean_lending_raw_manage_impair_wire",
    "lean_lending_raw_manage_unimpair_wire",
    "lean_lending_raw_manage_default_wire",
    "lean_lending_terminal_manage_impair_wire",
    "lean_lending_terminal_manage_unimpair_wire",
    "lean_lending_terminal_manage_default_wire",
];
fn created() -> LendingState {
    let input =
        lending_wire::encode_request(3, Request::Create(lending_create::create(false, 0))).unwrap();
    let bytes = ledger::lending_lwab::dispatch_route(3, &input);
    let Response::Ok(Payload::State(Lifecycle::Value(value))) =
        lending_wire::decode_response(3, &bytes).unwrap()
    else {
        panic!("management fixture creation")
    };
    value
}
fn frame(tag: u8, state: LendingState, impaired: bool) -> Vec<u8> {
    let base = BrokerRequest {
        loan: state.loan,
        vault: state.vault,
        broker: state.broker,
    };
    let request = if matches!(tag, 11 | 27) {
        Request::Default(DefaultRequest { base, impaired })
    } else {
        Request::LoanVault(LoanVaultRequest {
            loan: base.loan,
            vault: base.vault,
        })
    };
    lending_wire::encode_request(tag, request).unwrap()
}
fn compare(tag: u8, input: &[u8], name: &str) -> Response<Payload> {
    let lean = lending_abi::wire(tag.into(), input);
    let quaxar = ledger::lending_lwab::dispatch_route(tag, input);
    assert_eq!(quaxar, lean, "{name}: exact complete management bytes");
    assert_eq!(
        ledger::lending_lwab::dispatch_route(tag, input),
        quaxar,
        "{name}: repeatable"
    );
    let typed = lending_wire::decode_response(tag, &lean).unwrap();
    assert_eq!(
        lending_wire::decode_response(tag, &quaxar),
        Ok(typed),
        "{name}: typed full result"
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
        compare(tag, input, "malformed/noncanonical frame");
    }
    let body = (10..seed.len())
        .find_map(|at| {
            let mut input = seed.to_vec();
            input[at] = 2;
            (lending_abi::wire(tag.into(), &input).get(10) == Some(&1)).then_some(input)
        })
        .expect("reachable malformed management body");
    compare(tag, &body, "malformed field");
    6
}
pub fn run() -> usize {
    let base = created();
    let mut impaired = base;
    impaired.vault.loss_unrealized = impaired.loan.principal_outstanding;
    let mut default = base;
    default.broker.cover_available = default.loan.principal_outstanding;
    default.broker.cover_rate_minimum = 100_000;
    default.broker.cover_rate_liquidation = 100_000;
    let mut checks = 0;
    for tag in [9, 10, 11, 25, 26, 27] {
        let state = match tag {
            10 | 26 => impaired,
            11 | 27 => default,
            _ => base,
        };
        let typed = compare(
            tag,
            &frame(tag, state, matches!(tag, 11 | 27)),
            "canonical loss/debt/cover transition",
        );
        assert!(
            matches!(
                typed,
                Response::Ok(Payload::Vault(_)) | Response::Ok(Payload::BrokerVault(_))
            ),
            "management result shape"
        );
        checks += 1 + malformed(tag, &frame(tag, state, matches!(tag, 11 | 27)));
    }
    let mut excessive = base;
    excessive.vault.assets_available = excessive.vault.assets_total;
    assert!(matches!(
        compare(
            9,
            &frame(9, excessive, false),
            "impair unavailable-loss limit"
        ),
        Response::Ok(Payload::Vault(Lifecycle::RejectedTer(38)))
    ));
    let mut missing_loss = base;
    missing_loss.vault.loss_unrealized = Number::ZERO;
    assert!(matches!(
        compare(
            10,
            &frame(10, missing_loss, false),
            "unimpair bad ledger loss guard"
        ),
        Response::Ok(Payload::Vault(Lifecycle::RejectedTer(25)))
    ));
    let mut insolvent = base;
    insolvent.vault.assets_total = Number {
        negative: false,
        mantissa: 1_000_000_000_000_000_000,
        exponent: -18,
    };
    insolvent.vault.assets_available = Number::ZERO;
    assert!(matches!(
        compare(11, &frame(11, insolvent, false), "default debt/loss guard"),
        Response::Ok(Payload::BrokerVault(Lifecycle::RejectedTer(25)))
    ));
    let mut bad_association = base;
    bad_association.vault.assets_total = Number {
        negative: false,
        mantissa: 1_000_000_000_000_000_000,
        exponent: 81,
    };
    bad_association.vault.assets_available = bad_association.vault.assets_total;
    assert!(matches!(
        compare(
            25,
            &frame(25, bad_association, false),
            "terminal association failure atomic"
        ),
        Response::Ok(Payload::Vault(Lifecycle::ModelError(_)))
    ));
    checks + 4
}
