//! Exact material Lean-to-Quaxar LWAB Vault vectors.

use std::collections::BTreeSet;

use basics::number::NumberParts as RuntimeNumber;
use ledger::vault_lwab::{self as lwab, NumericType as WireNumericType, Vault as WireVault};

use crate::vault_abi;

#[derive(Debug, Default)]
pub struct RouteEvidence {
    pub canonical: BTreeSet<u8>,
    pub guards: usize,
    pub malformed: usize,
    pub material_checks: usize,
}

fn build(total: u64, available: u64, shares: u64, loss: u64) -> WireVault {
    let number = |value| {
        if value == 0 {
            RuntimeNumber::zero()
        } else {
            RuntimeNumber::unchecked(false, value, -18)
        }
    };
    WireVault {
        total: number(total),
        available: number(available),
        reserved: RuntimeNumber::zero(),
        maximum: None,
        numeric_type: WireNumericType::Fractional,
        scale: 0,
        shares: number(shares),
        loss: number(loss),
    }
}

fn compare(evidence: &mut RouteEvidence, route: u8, input: Vec<u8>, label: &str) {
    let lean = vault_abi::wire(route.into(), &input);
    let quaxar = lwab::dispatch_route(route, &input);
    assert_eq!(lean, quaxar, "route {route} {label} full material response");
    assert_eq!(lean[5], route + 128, "route {route} response association");
    assert!(
        evidence.canonical.insert(route),
        "duplicate canonical route {route}"
    );
    evidence.material_checks += 1;
}

pub fn vectors() -> RouteEvidence {
    let mut evidence = RouteEvidence::default();
    let value = build(
        1_000_000_000_000_000_000,
        1_000_000_000_000_000_000,
        1_000_000_000_000_000_000,
        0,
    );
    let asset_one = lwab::Amount {
        numeric_type: WireNumericType::Fractional,
        mantissa: 1_000_000_000_000_000_000,
        exponent: -18,
        negative: false,
    };
    let share_one = lwab::Amount {
        numeric_type: WireNumericType::Integral {
            maximum: 9_223_372_036_854_775_807,
            offset: 18,
            sqrt: 3_037_000_499,
            shift: 2_147_483_648,
        },
        mantissa: 1,
        exponent: 0,
        negative: false,
    };
    let empty = build(0, 0, 0, 0);
    let stranded = build(0, 0, 1_000_000_000_000_000_000, 0);
    let canonical = [
        (1, lwab::encode_build_request(1, value)),
        (2, lwab::encode_build_request(2, value)),
        (3, lwab::encode_amount_request(3, value, asset_one)),
        (4, lwab::encode_deposit_request(value, asset_one, false)),
        (
            5,
            lwab::encode_withdraw_request(5, value, true, share_one, false),
        ),
        (
            6,
            lwab::encode_withdraw_request(6, value, true, share_one, false),
        ),
        (
            7,
            lwab::encode_clawback_request(value, asset_one, share_one),
        ),
        (8, lwab::encode_amount_request(8, stranded, share_one)),
        (9, lwab::encode_amount_request(9, stranded, share_one)),
        (10, lwab::encode_vault_only_request(10, stranded)),
        (11, lwab::encode_vault_only_request(11, empty)),
        (12, lwab::encode_set_request(value, value.total)),
    ];
    for (route, request) in canonical {
        compare(
            &mut evidence,
            route,
            request.expect("canonical Vault LWAB request"),
            "success",
        );
    }
    let asset_zero = lwab::Amount {
        mantissa: 0,
        exponent: -100,
        ..asset_one
    };
    let share_zero = lwab::Amount {
        mantissa: 0,
        exponent: 0,
        ..share_one
    };
    let negative_asset = lwab::Amount {
        negative: true,
        ..asset_one
    };
    let guards = [
        (3, lwab::encode_amount_request(3, value, asset_zero)),
        (4, lwab::encode_deposit_request(empty, asset_one, true)),
        (
            6,
            lwab::encode_withdraw_request(6, value, true, share_zero, false),
        ),
        (
            7,
            lwab::encode_clawback_request(value, negative_asset, share_one),
        ),
        (
            7,
            lwab::encode_clawback_request(value, asset_zero, share_zero),
        ),
        (8, lwab::encode_amount_request(8, stranded, share_zero)),
        (9, lwab::encode_amount_request(9, stranded, share_zero)),
        (10, lwab::encode_vault_only_request(10, value)),
    ];
    for (route, request) in guards {
        let input = request.expect("canonical guard request");
        assert_eq!(
            vault_abi::wire(route.into(), &input),
            lwab::dispatch_route(route, &input),
            "route {route} tagged guard response"
        );
        evidence.guards += 1;
        evidence.material_checks += 1;
    }
    for route in 1..=12u8 {
        for input in [
            b"NOPE".as_slice(),
            b"LWAB\x02".as_slice(),
            b"LWAB".as_slice(),
            b"LWAB\x01\0\0\0\0\0".as_slice(),
            &[b'L', b'W', b'A', b'B', 1, route, 0, 0, 0, 0, 0],
            &[b'L', b'W', b'A', b'B', 1, route, 1, 0, 0, 0],
        ] {
            assert_eq!(
                vault_abi::wire(route.into(), input),
                lwab::dispatch_route(route, input),
                "route {route} codec rejection"
            );
            evidence.malformed += 1;
        }
    }
    assert_eq!(evidence.canonical.len(), 12);
    assert_eq!(evidence.guards, 8);
    assert_eq!(evidence.malformed, 72);
    evidence
}
