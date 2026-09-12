#[path = "vectors/lending_create_fixture.rs"]
mod lending_create_fixture;

use crate::{
    lending_abi,
    lending_wire::{self, *},
};
pub(crate) use lending_create_fixture::create;

const OPERATIONS: [(u8, bool); 6] = [
    (1, false),
    (2, true),
    (3, false),
    (17, false),
    (18, true),
    (19, false),
];
pub const EXPORT_IDS: [&str; 6] = [
    "lean_lending_raw_create_wire",
    "lean_lending_raw_create_pending_wire",
    "lean_lending_raw_create_immediate_wire",
    "lean_lending_terminal_create_wire",
    "lean_lending_terminal_create_pending_wire",
    "lean_lending_terminal_create_immediate_wire",
];
fn compare((tag, forced_pending): (u8, bool), name: &str, request: CreateRequest) -> usize {
    let input = lending_wire::encode_request(tag, Request::Create(request))
        .expect("canonical create frame");
    let lean = lending_abi::wire(tag.into(), &input);
    let lean_typed = lending_wire::decode_response(tag, &lean).expect("Lean StateResult");
    let quaxar = ledger::lending_lwab::dispatch_route(tag, &input);
    let quaxar_typed = lending_wire::decode_response(tag, &quaxar).expect("Quaxar StateResult");
    assert_eq!(quaxar_typed, lean_typed);
    assert_eq!(quaxar, lean, "tag {tag} {name}: complete bytes");
    assert_eq!(
        ledger::lending_lwab::dispatch_route(tag, &input),
        quaxar,
        "tag {tag} {name}: repeatable bytes"
    );
    if let Response::Ok(Payload::State(Lifecycle::Value(state))) = quaxar_typed {
        assert_eq!(
            state.loan.pending,
            if matches!(tag, 1 | 17) {
                request.pending
            } else {
                forced_pending
            }
        );
    }
    1
}
fn malformed(tag: u8, input: &[u8]) -> usize {
    let lean = lending_abi::wire(tag.into(), input);
    let quaxar = ledger::lending_lwab::dispatch_route(tag, input);
    assert_eq!(quaxar, lean, "tag {tag} malformed full bytes");
    assert_eq!(
        ledger::lending_lwab::dispatch_route(tag, input),
        quaxar,
        "tag {tag} malformed repeatability"
    );
    1
}
fn first_mutation(tag: u8, input: &[u8], class: u8) -> Vec<u8> {
    for index in 10..input.len() {
        let mut candidate = input.to_vec();
        candidate[index] = 2;
        if lending_abi::wire(tag.into(), &candidate).get(11) == Some(&class) {
            return candidate;
        }
    }
    panic!("no tag {tag} mutation for Lean decoder class {class}")
}
pub fn run() -> usize {
    let mut checks = 0;
    for operation @ (tag, _) in OPERATIONS {
        checks += compare(operation, "canonical request immediate", create(false, 0));
        checks += compare(operation, "canonical request pending", create(true, 0));
        checks += compare(operation, "nonzero-interest", create(false, 1));
        let mut guards = [create(false, 0); 5];
        guards[0].loan_identity.borrower = AccountId(0);
        guards[1].vault.assets_available = Number::ZERO;
        guards[2].broker.debt_maximum =
            lending_create_fixture::number(1_000_000_000_000_000_000, -18);
        guards[3].broker.cover_rate_minimum = 100_000;
        guards[4].principal = Number::ZERO;
        for (name, request) in [
            ("temINVALID", guards[0]),
            ("tecINSUFFICIENT_FUNDS available", guards[1]),
            ("tecLIMIT_EXCEEDED", guards[2]),
            ("tecINSUFFICIENT_FUNDS cover", guards[3]),
            ("tecPRECISION_LOSS", guards[4]),
        ] {
            checks += compare(operation, name, request);
        }
        let canonical = lending_wire::encode_request(tag, Request::Create(create(false, 0)))
            .expect("create seed");
        let mut bad_tag = canonical[..10].to_vec();
        bad_tag[5] = if tag == 1 { 2 } else { 1 };
        let mut bad_length = canonical[..10].to_vec();
        bad_length[6..10].copy_from_slice(&65_537_u32.to_le_bytes());
        for input in [
            b"NOPE".as_slice(),
            b"LWAB\x02".as_slice(),
            bad_tag.as_slice(),
            &canonical[..9],
            bad_length.as_slice(),
        ] {
            checks += malformed(tag, input);
        }
        let mut trailing = canonical.clone();
        trailing.push(0);
        checks += malformed(tag, &trailing);
        for class in [5, 6, 8, 10] {
            checks += malformed(tag, &first_mutation(tag, &canonical, class));
        }
    }
    checks
}
