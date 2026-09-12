use crate::abi::Number;
use std::mem::MaybeUninit;

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct St {
    pub kind: u8,
    pub mantissa: u64,
    pub offset: i64,
    pub negative: u8,
}
const _: () = {
    assert!(std::mem::size_of::<St>() == 32);
    assert!(std::mem::align_of::<St>() == 8);
    assert!(std::mem::offset_of!(St, kind) == 0);
    assert!(std::mem::offset_of!(St, mantissa) == 8);
    assert!(std::mem::offset_of!(St, offset) == 16);
    assert!(std::mem::offset_of!(St, negative) == 24);
};
unsafe extern "C" {
    fn lean_st_access(x: St, out: *mut St);
    fn lean_st_comparable(a: St, b: St) -> u8;
    fn lean_st_int(x: St, out: *mut i64, error: *mut u8) -> i32;
    fn lean_st_iou(x: St, mode: u8, m: *mut i64, e: *mut i64, error: *mut u8) -> i32;
    fn lean_st_number(x: St, mode: u8, out: *mut Number, error: *mut u8) -> i32;
    fn lean_st_construct(
        op: u8,
        x: St,
        v: i64,
        n: Number,
        mode: u8,
        out: *mut St,
        error: *mut u8,
    ) -> i32;
    fn lean_st_eq(op: u8, a: St, b: St) -> u8;
    fn lean_st_compare(op: u8, a: St, b: St, out: *mut u8, error: *mut u8) -> i32;
    fn lean_st_neg(x: St, out: *mut St);
    fn lean_st_binary(
        op: u8,
        a: St,
        b: St,
        kind: u8,
        up: u8,
        mode: u8,
        out: *mut St,
        error: *mut u8,
    ) -> i32;
    fn lean_st_can(op: u8, a: St, b: St, mode: u8, out: *mut u8, error: *mut u8) -> i32;
    fn lean_st_round(x: St, scale: i64, mode: u8, out: *mut St, error: *mut u8) -> i32;
    fn lean_st_rate(a: St, b: St, mode: u8) -> u64;
}
fn result<T>(call: impl FnOnce(*mut T, *mut u8) -> i32) -> Result<T, u8> {
    let mut out = MaybeUninit::uninit();
    let mut e = u8::MAX;
    if call(out.as_mut_ptr(), &mut e) != 0 {
        Ok(unsafe { out.assume_init() })
    } else {
        Err(e)
    }
}
pub fn access(x: St) -> St {
    let mut o = MaybeUninit::uninit();
    unsafe {
        lean_st_access(x, o.as_mut_ptr());
        o.assume_init()
    }
}
pub fn comparable(a: St, b: St) -> bool {
    unsafe { lean_st_comparable(a, b) != 0 }
}
pub fn int(x: St) -> Result<i64, u8> {
    result(|o, e| unsafe { lean_st_int(x, o, e) })
}
pub fn iou(x: St, m: u8) -> Result<(i64, i64), u8> {
    let mut a = 0;
    let mut b = 0;
    let mut e = u8::MAX;
    if unsafe { lean_st_iou(x, m, &mut a, &mut b, &mut e) } != 0 {
        Ok((a, b))
    } else {
        Err(e)
    }
}
pub fn number(x: St, m: u8) -> Result<Number, u8> {
    result(|o, e| unsafe { lean_st_number(x, m, o, e) })
}
pub fn construct(op: u8, x: St, v: i64, n: Number, m: u8) -> Result<St, u8> {
    result(|o, e| unsafe { lean_st_construct(op, x, v, n, m, o, e) })
}
pub fn eq(a: St, b: St, ne: bool) -> bool {
    unsafe { lean_st_eq(ne as u8, a, b) != 0 }
}
pub fn compare(op: u8, a: St, b: St) -> Result<bool, u8> {
    let mut o = 0;
    let mut e = u8::MAX;
    if unsafe { lean_st_compare(op, a, b, &mut o, &mut e) } != 0 {
        Ok(o != 0)
    } else {
        Err(e)
    }
}
pub fn neg(x: St) -> St {
    let mut o = MaybeUninit::uninit();
    unsafe {
        lean_st_neg(x, o.as_mut_ptr());
        o.assume_init()
    }
}
pub fn binary(op: u8, a: St, b: St, k: u8, up: bool, m: u8) -> Result<St, u8> {
    result(|o, e| unsafe { lean_st_binary(op, a, b, k, up as u8, m, o, e) })
}
pub fn can(op: u8, a: St, b: St, m: u8) -> Result<bool, u8> {
    let mut o = 0;
    let mut e = u8::MAX;
    if unsafe { lean_st_can(op, a, b, m, &mut o, &mut e) } != 0 {
        Ok(o != 0)
    } else {
        Err(e)
    }
}
pub fn round(x: St, s: i64, m: u8) -> Result<St, u8> {
    result(|o, e| unsafe { lean_st_round(x, s, m, o, e) })
}
pub fn rate(a: St, b: St, m: u8) -> u64 {
    unsafe { lean_st_rate(a, b, m) }
}
