use crate::abi::Number;
use std::mem::MaybeUninit;

unsafe extern "C" {
    fn lean_int_direct(op: u8, left: u64, right: u64) -> u64;
    fn lean_int_compare(relation: u8, left: u64, right: u64) -> u8;
    fn lean_int_from_number(value: Number, mode: u8, out: *mut u64, error: *mut u8) -> i32;
    fn lean_int_to_number(value: u64, mode: u8, out: *mut Number, error: *mut u8) -> i32;
    fn lean_int_mul_ratio(
        value: u64,
        num: u32,
        den: u32,
        round_up: u8,
        out: *mut u64,
        error: *mut u8,
    ) -> i32;
}

fn result<T>(call: impl FnOnce(*mut T, *mut u8) -> i32) -> Result<T, u8> {
    let mut out = MaybeUninit::uninit();
    let mut error = u8::MAX;
    if call(out.as_mut_ptr(), &mut error) != 0 {
        Ok(unsafe { out.assume_init() })
    } else {
        Err(error)
    }
}
fn bits(value: i64) -> u64 {
    value as u64
}
fn signed(value: u64) -> i64 {
    value as i64
}

pub fn direct(op: u8, left: i64, right: i64) -> i64 {
    signed(unsafe { lean_int_direct(op, bits(left), bits(right)) })
}
pub fn compare(relation: u8, left: i64, right: i64) -> bool {
    let value = unsafe { lean_int_compare(relation, bits(left), bits(right)) };
    assert_ne!(value, u8::MAX, "invalid IntAmount comparison selector");
    value != 0
}
pub fn from_number(value: Number, mode: u8) -> Result<i64, u8> {
    result(|out, error| unsafe { lean_int_from_number(value, mode, out, error) }).map(signed)
}
pub fn to_number(value: i64, mode: u8) -> Result<Number, u8> {
    result(|out, error| unsafe { lean_int_to_number(bits(value), mode, out, error) })
}
pub fn mul_ratio(value: i64, num: u32, den: u32, round_up: bool) -> Result<i64, u8> {
    result(|out, error| unsafe {
        lean_int_mul_ratio(bits(value), num, den, round_up as u8, out, error)
    })
    .map(signed)
}
