use crate::stamount_abi as ffi;
use basics::{base_uint::Uint192, number::RoundingMode};
use protocol::st_amount::AmountError;
use protocol::{Asset, MPTAmount, MPTIssue, STAmount, no_issue, sf_generic};

pub fn mode(tag: u8) -> RoundingMode {
    [
        RoundingMode::ToNearest,
        RoundingMode::TowardsZero,
        RoundingMode::Downward,
        RoundingMode::Upward,
    ][tag as usize]
}
pub fn wire(x: &STAmount, kind: u8) -> ffi::St {
    ffi::St {
        kind,
        mantissa: x.mantissa(),
        offset: i64::from(x.exponent()),
        negative: x.negative() as u8,
    }
}
pub fn issue() -> MPTIssue {
    MPTIssue::new(Uint192::from_slice(&[7; 24]).unwrap())
}
pub fn amount(kind: u8, m: u64, e: i32, neg: bool) -> STAmount {
    match kind {
        0 => STAmount::new_native(m, neg),
        1 => STAmount::from_mpt_amount(
            sf_generic(),
            MPTAmount::from_value(if neg { -(m as i64) } else { m as i64 }),
            issue(),
        ),
        _ => STAmount::new_with_asset(sf_generic(), no_issue(), m, e, neg),
    }
}
pub fn project(x: ffi::St) -> (u8, u64, i64, u8) {
    (x.kind, x.mantissa, x.offset, x.negative)
}
#[derive(Clone, Copy, Debug)]
pub enum StErrorCase {
    CheckedNativeRange,
    CheckedMptRange,
    CheckedIssuedRange,
    DivideByZero,
    NotComparable,
    CannotConvert,
}
impl StErrorCase {
    pub const fn lean_tag(self) -> u8 {
        match self {
            Self::CheckedNativeRange | Self::CheckedMptRange => 2,
            Self::CheckedIssuedRange => 0,
            Self::DivideByZero => 1,
            Self::NotComparable => 6,
            Self::CannotConvert => 7,
        }
    }
    const fn quaxar_error(self) -> Option<AmountError> {
        match self {
            Self::CheckedNativeRange => Some(AmountError::NativeOutOfRange),
            Self::CheckedMptRange => Some(AmountError::MptOutOfRange),
            Self::CheckedIssuedRange => Some(AmountError::IssuedOutOfRange),
            Self::DivideByZero => Some(AmountError::DivisionByZero),
            Self::NotComparable | Self::CannotConvert => None,
        }
    }
}
pub fn same(
    lean: Result<ffi::St, u8>,
    q: Result<STAmount, AmountError>,
    kind: u8,
    expected: Option<StErrorCase>,
) {
    match (lean, q, expected) {
        (Ok(a), Ok(b), None) => assert_eq!(project(a), project(wire(&b, kind))),
        (Err(tag), Err(error), Some(case)) => {
            assert_eq!(tag, case.lean_tag(), "Lean STAmount error class");
            assert_eq!(
                Some(error),
                case.quaxar_error(),
                "Quaxar STAmount error class"
            );
        }
        (a, b, context) => {
            panic!("STAmount outcome/error-class mismatch {a:?} vs {b:?}; {context:?}")
        }
    }
}
pub fn checked(kind: u8, m: u64, e: i32, n: bool) -> Result<STAmount, AmountError> {
    let a = match kind {
        0 => Asset::Issue(protocol::xrp_issue()),
        1 => Asset::MPTIssue(issue()),
        _ => Asset::Issue(no_issue()),
    };
    STAmount::try_new_with_asset(sf_generic(), a, m, e, n)
}
pub fn bases() -> [(u8, u64, i32, bool); 6] {
    [
        (0, 5, 0, false),
        (0, 11, 0, true),
        (1, 5, 0, false),
        (1, 11, 0, true),
        (2, 1_500_000_000_000_000, -15, false),
        (2, 2_000_000_000_000_000, -15, true),
    ]
}
