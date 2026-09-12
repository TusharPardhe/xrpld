use super::*;
use basics::number::NumberParts;

fn n(value: u64) -> NumberParts {
    NumberParts::unchecked(false, value, -18)
}

fn build_frame(tag: u8, trailing: &[u8]) -> Vec<u8> {
    let mut body = Vec::new();
    for value in [n(1_000_000_000_000_000_000), n(1_000_000_000_000_000_000)] {
        types::number(&mut body, value).unwrap();
    }
    body.push(0);
    body.push(0);
    body.push(0);
    types::number(&mut body, n(1_000_000_000_000_000_000)).unwrap();
    types::number(&mut body, zero_number()).unwrap();
    let mut input = primitive::response(tag, body);
    input.extend(trailing);
    input
}

#[test]
fn build_roundtrip_and_envelope_errors_are_exact() {
    let input = build_frame(1, &[]);
    let output = dispatch_route(1, &input);
    assert_eq!(&output[..6], b"LWAB\x01\x81");
    assert_eq!(output[10], 0);
    assert_eq!(
        dispatch_route(1, b"NOPE"),
        primitive::decode_error_response(1, DecodeError::BadMagic)
    );
    assert_eq!(
        dispatch_route(1, b"LWAB\x02"),
        primitive::decode_error_response(1, DecodeError::BadVersion(2))
    );
    assert_eq!(dispatch_route(1, &build_frame(1, &[0]))[11], 1);
}

#[test]
fn terminal_build_applies_asset_association() {
    let raw = Vault {
        total: NumberParts::unchecked(false, 1_000_000_000_000_000_001, -18),
        available: NumberParts::unchecked(false, 1_000_000_000_000_000_001, -18),
        reserved: zero_number(),
        maximum: None,
        numeric_type: NumericType::Fractional,
        scale: 0,
        shares: n(1_000_000_000_000_000_000),
        loss: zero_number(),
    };
    let canonical = Vault {
        total: n(1_000_000_000_000_000_000),
        available: n(1_000_000_000_000_000_000),
        ..raw
    };
    assert_eq!(
        transition_admin::associate_terminal(canonical),
        Ok(canonical),
        "canonical fractional fields survive the terminal association"
    );
    let raw_result = dispatch_route(1, &encode_build_request(1, raw).unwrap());
    let terminal_result = dispatch_route(2, &encode_build_request(2, raw).unwrap());
    assert_eq!(&raw_result[10..12], &[0, 0], "raw construction succeeds");
    assert_eq!(
        &terminal_result[10..12],
        &[0, 0],
        "terminal construction succeeds"
    );
    assert_ne!(
        raw_result, terminal_result,
        "terminal association rounds asset fields"
    );
}
