use crate::{abi::Number, stamount_abi as ffi};
use basics::number::{
    MantissaScale, NumberParts, RoundingMode, set_mantissa_scale, set_rounding_mode,
};
use protocol::st_amount::AmountError;
use protocol::{
    Asset, IOUAmount, MPTAmount, STAmount, XRPAmount, can_add, can_subtract, div_round,
    div_round_strict, get_rate, mul_round, mul_round_strict, no_issue, round_to_exponent,
    sf_generic,
};

use crate::stamount_model::{amount, bases, checked, issue, mode, project, same, wire};

pub fn run() -> (usize, usize) {
    set_mantissa_scale(MantissaScale::Large330);
    let mut checks = 0;
    let bases = bases();
    for tag in 0..4 {
        checks += run_mode(tag, &bases);
    }
    checks += crate::stamount_generated::run();
    set_rounding_mode(RoundingMode::ToNearest);
    (checks, 0)
}

fn run_mode(tag: u8, bases: &[(u8, u64, i32, bool)]) -> usize {
    set_rounding_mode(mode(tag));
    let mut checks = 0;
    for &(kind, mantissa, exponent, negative) in bases {
        let amount = amount(kind, mantissa, exponent, negative);
        let raw = ffi::St {
            kind,
            mantissa,
            offset: i64::from(exponent),
            negative: negative as u8,
        };
        assert_eq!(project(ffi::access(raw)), project(raw));
        checks += 1;
        assert!(ffi::comparable(raw, raw));
        checks += 1;
        match kind {
            0 | 1 => assert_eq!(
                ffi::int(raw),
                Ok(if negative {
                    -(mantissa as i64)
                } else {
                    mantissa as i64
                })
            ),
            _ => {
                assert_eq!(
                    ffi::int(raw),
                    Err(crate::stamount_model::StErrorCase::CannotConvert.lean_tag())
                );
                assert_eq!(
                    ffi::iou(raw, tag),
                    Ok((
                        if negative {
                            -(mantissa as i64)
                        } else {
                            mantissa as i64
                        },
                        i64::from(exponent)
                    ))
                );
            }
        }
        checks += 1;
        let lean_number = ffi::number(raw, tag);
        let quaxar_number = match kind {
            0 => NumberParts::from(amount.xrp()),
            1 => NumberParts::from(amount.mpt()),
            _ => NumberParts::from(amount.iou()),
        };
        let x = lean_number.expect("unexpected Lean to_number error");
        assert_eq!(
            (x.negative, x.mantissa, x.exponent),
            (
                quaxar_number.negative as u8,
                quaxar_number.mantissa,
                i64::from(quaxar_number.exponent)
            )
        );
        checks += 1;
        assert!(ffi::eq(raw, raw, false));
        assert!(!ffi::eq(raw, raw, true));
        checks += 2;
        for op in 0..4 {
            assert_eq!(ffi::compare(op, raw, raw), Ok(op == 1 || op == 3));
            checks += 1;
        }
        let mut negated = amount.clone();
        negated.negate();
        assert_eq!(project(ffi::neg(raw)), project(wire(&negated, kind)));
        checks += 1;
        same(
            ffi::construct(
                1,
                raw,
                0,
                Number {
                    negative: 0,
                    mantissa: 0,
                    exponent: 0,
                },
                tag,
            ),
            checked(kind, mantissa, exponent, negative),
            kind,
            None,
        );
        checks += 1;
        same(
            ffi::construct(
                2,
                raw,
                if negative {
                    -(mantissa as i64)
                } else {
                    mantissa as i64
                },
                Number {
                    negative: 0,
                    mantissa: 0,
                    exponent: 0,
                },
                tag,
            ),
            checked(kind, mantissa, exponent, negative),
            kind,
            None,
        );
        checks += 1;
        let number = Number {
            negative: negative as u8,
            mantissa,
            exponent: i64::from(exponent),
        };
        let via = NumberParts::unchecked(negative, mantissa, exponent);
        let expected = match kind {
            0 => XRPAmount::from_number(via)
                .map(STAmount::from_xrp_amount)
                .map_err(|_| AmountError::NativeOutOfRange),
            1 => MPTAmount::from_number(via)
                .map(|value| STAmount::from_mpt_amount(sf_generic(), value, issue()))
                .map_err(|_| AmountError::MptOutOfRange),
            _ => IOUAmount::from_number(via)
                .map(|value| STAmount::from_iou_amount(sf_generic(), value, no_issue()))
                .map_err(|_| AmountError::IssuedOutOfRange),
        };
        same(ffi::construct(3, raw, 0, number, tag), expected, kind, None);
        checks += 1;
        assert_eq!(
            project(
                ffi::construct(
                    0,
                    raw,
                    if negative {
                        -(mantissa as i64)
                    } else {
                        mantissa as i64
                    },
                    number,
                    tag
                )
                .unwrap()
            ),
            project(raw)
        );
        checks += 1;
    }
    checks + binary_checks(tag)
}

#[path = "stamount_cases_binary.rs"]
mod stamount_cases_binary;
use stamount_cases_binary::binary_checks;
