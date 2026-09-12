use crate::{
    abi::Number,
    stamount_abi as ffi,
    stamount_model::{StErrorCase, amount, same},
};
use protocol::st_amount::AmountError;

pub fn run(mode: u8) -> usize {
    let native = ffi::St {
        kind: 0,
        mantissa: 1,
        offset: 18,
        negative: 0,
    };
    let mpt = ffi::St {
        kind: 1,
        mantissa: 1,
        offset: 19,
        negative: 0,
    };
    let issued = ffi::St {
        kind: 2,
        mantissa: 1_000_000_000_000_000,
        offset: 81,
        negative: 0,
    };
    let number = Number {
        negative: 0,
        mantissa: 0,
        exponent: 0,
    };
    same(
        ffi::construct(1, native, 0, number, mode),
        Err(AmountError::NativeOutOfRange),
        0,
        Some(StErrorCase::CheckedNativeRange),
    );
    same(
        ffi::construct(1, mpt, 0, number, mode),
        Err(AmountError::MptOutOfRange),
        1,
        Some(StErrorCase::CheckedMptRange),
    );
    same(
        ffi::construct(1, issued, 0, number, mode),
        Err(AmountError::IssuedOutOfRange),
        2,
        Some(StErrorCase::CheckedIssuedRange),
    );
    assert_eq!(
        ffi::iou(native, mode),
        Err(StErrorCase::CannotConvert.lean_tag())
    );
    assert_eq!(ffi::int(issued), Err(StErrorCase::CannotConvert.lean_tag()));
    let one = ffi::St {
        kind: 0,
        mantissa: 1,
        offset: 0,
        negative: 0,
    };
    let zero = ffi::St { mantissa: 0, ..one };
    same(
        ffi::binary(2, one, zero, 0, false, mode),
        amount(0, 1, 0, false).try_divide(&amount(0, 0, 0, false), protocol::xrp_issue()),
        0,
        Some(StErrorCase::DivideByZero),
    );
    assert_eq!(
        ffi::compare(0, native, issued),
        Err(StErrorCase::NotComparable.lean_tag())
    );
    7
}
