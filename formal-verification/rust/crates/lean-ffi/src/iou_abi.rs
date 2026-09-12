use crate::abi::Number;
use std::mem::MaybeUninit;

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Iou {
    pub mantissa: i64,
    pub exponent: i64,
}

const _: () = {
    assert!(std::mem::size_of::<Iou>() == 16);
    assert!(std::mem::align_of::<Iou>() == 8);
    assert!(std::mem::offset_of!(Iou, mantissa) == 0);
    assert!(std::mem::offset_of!(Iou, exponent) == 8);
};

unsafe extern "C" {
    fn lean_iou_build_accessors(mantissa: i64, exponent: i64, out: *mut Iou);
    fn lean_iou_from_number_bridge(value: Number, mode: u8, out: *mut Iou, error: *mut u8) -> i32;
    fn lean_iou_of_mantissa_exp_bridge(
        m: i64,
        e: i64,
        mode: u8,
        out: *mut Iou,
        error: *mut u8,
    ) -> i32;
    fn lean_iou_of_number_bridge(value: Number, mode: u8, out: *mut Iou, error: *mut u8) -> i32;
    fn lean_iou_to_number_bridge(value: Iou, mode: u8, out: *mut Number, error: *mut u8) -> i32;
    fn lean_iou_compare_bridge(relation: u8, a: Iou, b: Iou, mode: u8, error: *mut u8) -> u8;
    fn lean_iou_unary_bridge(op: u8, value: Iou, mode: u8, out: *mut Iou, error: *mut u8) -> i32;
    fn lean_iou_binary_bridge(
        op: u8,
        a: Iou,
        b: Iou,
        mode: u8,
        out: *mut Iou,
        error: *mut u8,
    ) -> i32;
    fn lean_iou_mul_ratio_bridge(
        value: Iou,
        n: u32,
        d: u32,
        up: u8,
        mode: u8,
        out: *mut Iou,
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
pub fn build(m: i64, e: i64) -> Iou {
    let mut out = MaybeUninit::uninit();
    unsafe {
        lean_iou_build_accessors(m, e, out.as_mut_ptr());
        out.assume_init()
    }
}
pub fn from_number(n: Number, mode: u8) -> Result<Iou, u8> {
    result(|o, e| unsafe { lean_iou_from_number_bridge(n, mode, o, e) })
}
pub fn of_parts(m: i64, e: i64, mode: u8) -> Result<Iou, u8> {
    result(|o, x| unsafe { lean_iou_of_mantissa_exp_bridge(m, e, mode, o, x) })
}
pub fn of_number(n: Number, mode: u8) -> Result<Iou, u8> {
    result(|o, e| unsafe { lean_iou_of_number_bridge(n, mode, o, e) })
}
pub fn to_number(a: Iou, mode: u8) -> Result<Number, u8> {
    result(|o, e| unsafe { lean_iou_to_number_bridge(a, mode, o, e) })
}
pub fn compare(r: u8, a: Iou, b: Iou, mode: u8) -> Result<bool, u8> {
    let mut error = u8::MAX;
    let value = unsafe { lean_iou_compare_bridge(r, a, b, mode, &mut error) };
    if value == u8::MAX {
        Err(error)
    } else {
        Ok(value != 0)
    }
}
pub fn neg(a: Iou, mode: u8) -> Result<Iou, u8> {
    result(|o, e| unsafe { lean_iou_unary_bridge(0, a, mode, o, e) })
}
pub fn binary(op: u8, a: Iou, b: Iou, mode: u8) -> Result<Iou, u8> {
    result(|o, e| unsafe { lean_iou_binary_bridge(op, a, b, mode, o, e) })
}
pub fn mul_ratio(a: Iou, n: u32, d: u32, up: bool, mode: u8) -> Result<Iou, u8> {
    result(|o, e| unsafe { lean_iou_mul_ratio_bridge(a, n, d, up as u8, mode, o, e) })
}
