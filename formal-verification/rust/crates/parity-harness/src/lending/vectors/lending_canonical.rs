use super::lending_fixture::complete_requests;
use crate::{
    lending_abi,
    lending_wire::{self, *},
};

fn broker_create_vector() {
    let identity = BrokerIdentity {
        broker_id: ObjectId(3),
        vault_id: ObjectId(1),
        owner: AccountId(1),
        account: AccountId(4),
    };
    let request = BrokerCreateRequest {
        identity,
        debt_maximum: None,
        management_fee_rate: None,
        cover_rate_minimum: None,
        cover_rate_liquidation: None,
    };
    let input = lending_wire::encode_request(12, Request::BrokerCreate(request))
        .expect("canonical request");
    let output = lending_abi::wire(12, &input);
    let expected = LoanBroker {
        identity,
        management_fee_rate: 0,
        cover_rate_minimum: 0,
        cover_rate_liquidation: 0,
        debt_total: Number::ZERO,
        debt_maximum: Number::ZERO,
        cover_available: Number::ZERO,
        loan_count: 0,
    };
    let mut exact = vec![b'L', b'W', b'A', b'B', 1, 140];
    let mut payload = vec![0];
    payload.extend(lending_wire::encode_broker(expected).unwrap());
    exact.extend((payload.len() as u32).to_le_bytes());
    exact.extend(payload);
    assert_eq!(
        output, exact,
        "success response bytes are exact, not a digest or projection"
    );
    assert_eq!(
        lending_wire::decode_broker_response(12, &output),
        Ok(Response::Ok(expected))
    );
}
fn canonical_result_vectors() {
    for (operation, request) in complete_requests() {
        let input =
            lending_wire::encode_request(operation as u8, request).expect("canonical full request");
        let output = lending_abi::wire(operation, &input);
        let quaxar = ledger::lending_lwab::dispatch_route(operation as u8, &input);
        assert_eq!(
            quaxar, output,
            "route {operation}: exact full response bytes"
        );
        assert_eq!(
            lending_wire::decode_response(operation as u8, &quaxar),
            lending_wire::decode_response(operation as u8, &output),
            "route {operation}: complete typed result"
        );
        assert!(
            matches!(
                lending_wire::decode_response(operation as u8, &output),
                Ok(Response::Ok(_))
            ),
            "route {operation} fully decodes result fields"
        );
        assert_eq!(
            ledger::lending_lwab::dispatch_route(operation as u8, &input),
            quaxar,
            "route {operation}: repeatable"
        );
        assert_eq!(
            lending_abi::wire(operation, &input),
            output,
            "route {operation}: copied response bytes"
        );
    }
}
pub(crate) fn run() {
    canonical_result_vectors();
    broker_create_vector();
}
