use std::{ptr, slice};

unsafe extern "C" {
    fn lean_lending_initialize() -> i32;
    fn lean_lending_expired(now: u32, expiry: u32, exclusive: u8) -> i32;
    fn lean_lending_schedule_projection(
        interval: u32,
        total: u32,
        grace: u32,
        start: u32,
        now: u32,
        two_step: u8,
        out: *mut u32,
    ) -> i32;
    fn lean_lending_wire_invoke(
        operation: u32,
        input: *const u8,
        input_len: usize,
        out: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32;
    fn lean_lending_wire_free(out: *mut u8);
    fn lean_lending_complete_adapter() -> i32;
}

pub fn initialize() {
    assert_eq!(
        unsafe { lean_lending_initialize() },
        1,
        "Lending Lean initialization"
    );
}
pub fn expired(now: u32, expiry: u32, exclusive: bool) -> bool {
    unsafe { lean_lending_expired(now, expiry, exclusive as u8) != 0 }
}
pub fn schedule(
    interval: u32,
    total: u32,
    grace: u32,
    start: u32,
    now: u32,
    two_step: bool,
) -> [u32; 5] {
    let mut out = [0; 5];
    assert_eq!(
        unsafe {
            lean_lending_schedule_projection(
                interval,
                total,
                grace,
                start,
                now,
                two_step as u8,
                out.as_mut_ptr(),
            )
        },
        1
    );
    out
}

/// Calls the selected Lean route using a copied input and returns an exact copy
/// of its response frame. `operation` is the canonical request tag (1..=27).
pub fn wire(operation: u32, input: &[u8]) -> Vec<u8> {
    let mut bytes = ptr::null_mut();
    let mut len = 0;
    assert_eq!(
        unsafe {
            lean_lending_wire_invoke(operation, input.as_ptr(), input.len(), &mut bytes, &mut len)
        },
        1,
        "wire bridge invocation"
    );
    assert!(!bytes.is_null());
    let result = unsafe { slice::from_raw_parts(bytes, len).to_vec() };
    unsafe { lean_lending_wire_free(bytes) };
    result
}
pub fn complete_adapter() -> usize {
    let calls = unsafe { lean_lending_complete_adapter() };
    // The harness validates the expected invocation count against its manifest.
    assert!(calls >= 0, "Lean invocation count is non-negative");
    calls as usize
}
