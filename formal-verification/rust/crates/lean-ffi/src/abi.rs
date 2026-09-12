use std::mem::MaybeUninit;

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Number {
    pub negative: u8,
    pub mantissa: u64,
    pub exponent: i64,
}

const _: () = {
    assert!(std::mem::size_of::<Number>() == 24);
    assert!(std::mem::align_of::<Number>() == 8);
    assert!(std::mem::offset_of!(Number, negative) == 0);
    assert!(std::mem::offset_of!(Number, mantissa) == 8);
    assert!(std::mem::offset_of!(Number, exponent) == 16);
};

unsafe extern "C" {
    fn lean_bridge_initialize() -> i32;
    fn lean_bridge_roundtrip(negative: u8, mantissa: u64, exponent: i64, out: *mut Number);
    fn lean_bridge_binary(
        op: u8,
        lhs: Number,
        rhs: Number,
        mode: u8,
        out: *mut Number,
        error: *mut u8,
    ) -> i32;
    fn lean_bridge_neg(input: Number, out: *mut Number);
    fn lean_bridge_signum(input: Number) -> i64;
    fn lean_bridge_compare(relation: u8, lhs: Number, rhs: Number) -> u8;
    fn lean_bridge_normalize(input: Number, mode: u8, out: *mut Number, error: *mut u8) -> i32;
    fn lean_bridge_to_rep(input: Number, mode: u8, out: *mut i64, error: *mut u8) -> i32;
    fn lean_bridge_raw_roundtrip(negative: u8, mantissa: u64, exponent: i64, out: *mut Number);
    fn lean_bridge_rounding_tag(mode: u8) -> u8;
    fn lean_bridge_numeric_integral(tag: u8) -> u8;
}

pub fn initialize() {
    assert_eq!(
        unsafe { lean_bridge_initialize() },
        1,
        "Lean initialization"
    );
}

pub fn raw_roundtrip(value: Number) -> Number {
    let mut out = MaybeUninit::uninit();
    unsafe {
        lean_bridge_raw_roundtrip(
            value.negative,
            value.mantissa,
            value.exponent,
            out.as_mut_ptr(),
        )
    };
    unsafe { out.assume_init() }
}

pub fn normalized_roundtrip(value: Number) -> Number {
    let mut out = MaybeUninit::uninit();
    unsafe {
        lean_bridge_roundtrip(
            value.negative,
            value.mantissa,
            value.exponent,
            out.as_mut_ptr(),
        )
    };
    unsafe { out.assume_init() }
}

pub fn binary(op: u8, lhs: Number, rhs: Number, mode: u8) -> Result<Number, u8> {
    let mut out = MaybeUninit::uninit();
    let mut error = u8::MAX;
    let ok = unsafe { lean_bridge_binary(op, lhs, rhs, mode, out.as_mut_ptr(), &mut error) };
    if ok != 0 {
        Ok(unsafe { out.assume_init() })
    } else {
        Err(error)
    }
}

pub fn neg(value: Number) -> Number {
    let mut out = MaybeUninit::uninit();
    unsafe { lean_bridge_neg(value, out.as_mut_ptr()) };
    unsafe { out.assume_init() }
}

pub fn signum(value: Number) -> i64 {
    unsafe { lean_bridge_signum(value) }
}
pub fn compare(relation: u8, lhs: Number, rhs: Number) -> bool {
    unsafe { lean_bridge_compare(relation, lhs, rhs) != 0 }
}

pub fn normalize(value: Number, mode: u8) -> Result<Number, u8> {
    let mut out = MaybeUninit::uninit();
    let mut error = u8::MAX;
    let ok = unsafe { lean_bridge_normalize(value, mode, out.as_mut_ptr(), &mut error) };
    if ok != 0 {
        Ok(unsafe { out.assume_init() })
    } else {
        Err(error)
    }
}

pub fn to_rep(value: Number, mode: u8) -> Result<i64, u8> {
    let mut out = MaybeUninit::uninit();
    let mut error = u8::MAX;
    let ok = unsafe { lean_bridge_to_rep(value, mode, out.as_mut_ptr(), &mut error) };
    if ok != 0 {
        Ok(unsafe { out.assume_init() })
    } else {
        Err(error)
    }
}

pub fn rounding_tag(mode: u8) -> u8 {
    unsafe { lean_bridge_rounding_tag(mode) }
}
pub fn numeric_integral(tag: u8) -> bool {
    unsafe { lean_bridge_numeric_integral(tag) != 0 }
}
