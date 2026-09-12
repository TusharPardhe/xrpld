//! Complete Lean/Quaxar delete-family parity vectors for tags 5 and 21.

use crate::{
    lending_abi,
    lending_wire::{self, *},
};

pub const EXPORT_IDS: [&str; 2] = [
    "lean_lending_raw_delete_wire",
    "lean_lending_terminal_delete_wire",
];
#[path = "vectors/lending_delete_fixture.rs"]
mod fixture;
use fixture::{n, request};

fn compare(tag: u8, input: &[u8], name: &str) -> Response<Payload> {
    let lean = lending_abi::wire(tag.into(), input);
    let quaxar = ledger::lending_lwab::dispatch_route(tag, input);
    assert_eq!(quaxar, lean, "{name}: complete response bytes");
    assert_eq!(
        ledger::lending_lwab::dispatch_route(tag, input),
        quaxar,
        "{name}: repeatability"
    );
    let typed = lending_wire::decode_response(tag, &lean).expect("Lean response decodes");
    assert_eq!(
        lending_wire::decode_response(tag, &quaxar),
        Ok(typed),
        "{name}: complete BrokerResult"
    );
    typed
}
fn frame(tag: u8, request: Request) -> Vec<u8> {
    lending_wire::encode_request(tag, request).unwrap()
}
fn broker(mut request: Request, edit: impl FnOnce(&mut BrokerRequest)) -> Request {
    let Request::Broker(ref mut value) = request else {
        unreachable!()
    };
    edit(value);
    request
}
fn malformed_body(tag: u8, seed: &[u8]) {
    let input = (10..seed.len())
        .find_map(|index| {
            let mut candidate = seed.to_vec();
            candidate[index] = 2;
            (lending_abi::wire(tag.into(), &candidate).get(11) == Some(&5)).then_some(candidate)
        })
        .expect("delete has a reachable malformed-body boolean");
    compare(tag, &input, "malformed body");
}

pub fn run() -> usize {
    let raw = frame(5, request(true, -18));
    let Response::Ok(Payload::BrokerVault(Lifecycle::Value(pending))) =
        compare(5, &raw, "pending delete full material")
    else {
        panic!("pending raw delete")
    };
    assert_eq!(pending.vault.assets_reserved, Number::ZERO);
    assert_eq!(pending.broker.debt_total, Number::ZERO);
    assert_eq!(pending.broker.loan_count, 0);
    let Response::Ok(Payload::BrokerVault(Lifecycle::Value(active))) = compare(
        5,
        &frame(5, request(false, -18)),
        "active delete last-loan debt reset",
    ) else {
        panic!("active raw delete")
    };
    assert_eq!(active.broker.debt_total, Number::ZERO);
    assert_eq!(active.vault.assets_reserved, n(-18));
    let mismatched = broker(request(true, -18), |r| {
        r.loan.identity.broker_id = ObjectId(99);
        r.broker.identity.vault_id = ObjectId(98);
    });
    assert!(matches!(
        compare(
            5,
            &frame(5, mismatched),
            "lossless identity and authorization material"
        ),
        Response::Ok(Payload::BrokerVault(Lifecycle::Value(_)))
    ));
    let unreserved = broker(request(true, -18), |r| r.vault.assets_available = n(-18));
    assert_eq!(
        compare(5, &frame(5, unreserved), "pending balance lawfulness guard"),
        Response::Ok(Payload::BrokerVault(Lifecycle::ModelError(8)))
    );
    assert!(matches!(
        compare(
            21,
            &frame(21, request(true, -18)),
            "terminal associates exactly once"
        ),
        Response::Ok(Payload::BrokerVault(Lifecycle::Value(_)))
    ));
    assert_eq!(
        compare(
            21,
            &frame(21, request(true, 81)),
            "terminal association failure"
        ),
        Response::Ok(Payload::BrokerVault(Lifecycle::ModelError(0)))
    );
    let mut checks = 6;
    for (tag, seed) in [(5, raw), (21, frame(21, request(true, -18)))] {
        let mut wrong = seed[..10].to_vec();
        wrong[5] = if tag == 5 { 21 } else { 5 };
        let mut trailing = seed.clone();
        trailing.push(0);
        for (name, input) in [
            ("magic", b"NOPE".as_slice()),
            ("tag", wrong.as_slice()),
            ("trailing", trailing.as_slice()),
            ("truncated", &seed[..9]),
        ] {
            compare(tag, input, name);
            checks += 1;
        }
        malformed_body(tag, &seed);
        checks += 1;
    }
    checks
}
