use super::lending_fixture::complete_requests;
use crate::{
    lending_abi,
    lending_wire::{self, *},
};

fn assert_response(operation: u32, bytes: &[u8]) {
    assert!(bytes.len() >= 11, "response frame is complete");
    assert_eq!(&bytes[..4], b"LWAB", "Lean wire magic");
    assert_eq!(bytes[4], 1, "Lean wire version");
    assert_eq!(
        bytes[5],
        128 + operation as u8,
        "response tag retains route identity"
    );
    let payload_len = u32::from_le_bytes(bytes[6..10].try_into().unwrap()) as usize;
    assert_eq!(
        bytes.len(),
        10 + payload_len,
        "response has exact bounded payload"
    );
    assert_eq!(bytes[10], 1, "malformed request is decoder error");
}
fn assert_decode_error(operation: u32, name: &str, input: &[u8], expected_class: u8) {
    let bytes = lending_abi::wire(operation, input);
    assert_response(operation, &bytes);
    assert_eq!(
        bytes[11], expected_class,
        "{name} exact Lean decoder class for route {operation}"
    );
    assert_eq!(
        lending_wire::decode_response(operation as u8, &bytes),
        Ok(Response::DecodeError(expected_class)),
        "{name} typed route-associated error"
    );
    assert_eq!(
        lending_abi::wire(operation, input),
        bytes,
        "{name} response copied byte-for-byte"
    );
}
fn first_mutation_with_class(operation: u32, input: &[u8], class: u8) -> Vec<u8> {
    for index in 10..input.len() {
        if input[index] == 2 {
            continue;
        }
        let mut candidate = input.to_vec();
        candidate[index] = 2;
        let output = lending_abi::wire(operation, &candidate);
        if output.len() >= 12 && output[10] == 1 && output[11] == class {
            return candidate;
        }
    }
    panic!("no deterministic byte mutation reaches decoder class {class} for route {operation}")
}
fn mutation_seed(operation: u32, request: Request, class: u8) -> Vec<u8> {
    let request = match (operation, class, request) {
        (12, 5 | 10, Request::BrokerCreate(mut value)) => {
            value.debt_maximum = Some(Number::ZERO);
            Request::BrokerCreate(value)
        }
        (_, _, value) => value,
    };
    lending_wire::encode_request(operation as u8, request).expect("canonical mutation seed")
}
pub(crate) fn run() -> usize {
    let mut checks = 0;
    for (operation, request) in complete_requests() {
        let wrong_tag = if operation == 27 {
            1
        } else {
            operation as u8 + 1
        };
        let canonical =
            lending_wire::encode_request(operation as u8, request).expect("canonical request");
        let mut truncated = canonical[..9].to_vec();
        truncated[5] = operation as u8;
        let mut bad_length = canonical[..10].to_vec();
        bad_length[6..10].copy_from_slice(&1u32.to_le_bytes());
        let mut trailing = canonical.clone();
        trailing.push(0);
        for (name, input, class) in [
            ("magic", b"NOPE".to_vec(), 2),
            ("version", b"LWAB\x02".to_vec(), 3),
            (
                "tag",
                vec![b'L', b'W', b'A', b'B', 1, wrong_tag, 0, 0, 0, 0],
                4,
            ),
            ("truncated", truncated, 0),
            ("bad-length", bad_length, 0),
            ("trailing", trailing, 1),
        ] {
            assert_decode_error(operation, name, &input, class);
            checks += 1;
        }
        for (name, class) in [("bad-boolean", 5), ("noncanonical", 10)] {
            let input = first_mutation_with_class(
                operation,
                &mutation_seed(operation, request, class),
                class,
            );
            assert_decode_error(operation, name, &input, class);
            checks += 1;
        }
        if !matches!(operation, 14 | 15 | 16) {
            let input = first_mutation_with_class(operation, &canonical, 6);
            assert_decode_error(operation, "bad-option", &input, 6);
            checks += 1;
        }
        if operation != 12 && operation != 13 {
            let input = first_mutation_with_class(operation, &canonical, 8);
            assert_decode_error(operation, "bad-numeric-type", &input, 8);
            checks += 1;
        }
    }
    checks
}
