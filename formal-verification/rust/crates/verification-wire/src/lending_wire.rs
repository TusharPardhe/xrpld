//! Lean-compatible Lending wire ABI. This is LWAB v1, never the prior LWC projection.

#[path = "lending_wire_primitive.rs"]
mod lending_wire_primitive;
#[path = "lending_wire_records.rs"]
mod lending_wire_records;
#[path = "lending_wire_requests.rs"]
mod lending_wire_requests;
#[path = "lending_wire_response.rs"]
mod lending_wire_response;
#[path = "lending_wire_types.rs"]
mod lending_wire_types;
pub use lending_wire_primitive::{MAGIC, VERSION, WireError};
pub use lending_wire_records::{
    decode_broker, encode_broker, encode_broker_vault, encode_loan_vault, encode_state,
};
pub use lending_wire_requests::{Request, decode_broker_response, encode_request};
pub use lending_wire_response::{CoverResult, Lifecycle, Payload, Response, decode_response};
pub use lending_wire_types::*;

#[cfg(test)]
mod tests {
    use super::*;
    fn broker_create() -> BrokerCreateRequest {
        BrokerCreateRequest {
            identity: BrokerIdentity {
                broker_id: ObjectId(3),
                vault_id: ObjectId(1),
                owner: AccountId(1),
                account: AccountId(4),
            },
            debt_maximum: None,
            management_fee_rate: None,
            cover_rate_minimum: None,
            cover_rate_liquidation: None,
        }
    }
    #[test]
    fn broker_create_request_is_exact_lwab() {
        let wire = encode_request(12, Request::BrokerCreate(broker_create())).unwrap();
        assert_eq!(&wire[..6], b"LWAB\x01\x0c");
        assert_eq!(u32::from_le_bytes(wire[6..10].try_into().unwrap()), 36);
        assert_eq!(
            &wire[10..],
            &[
                3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0
            ]
        );
    }
    #[test]
    fn typed_broker_codec_round_trips_all_fields() {
        let b = LoanBroker {
            identity: broker_create().identity,
            management_fee_rate: 7,
            cover_rate_minimum: 8,
            cover_rate_liquidation: 9,
            debt_total: Number::ZERO,
            debt_maximum: Number::ZERO,
            cover_available: Number::ZERO,
            loan_count: 10,
        };
        assert_eq!(decode_broker(&encode_broker(b).unwrap()), Ok(b));
    }
}
