//! Lean ABI calls used by the material Vault bridge.

unsafe extern "C" {
    fn lean_vault_initialize() -> i32;
    fn lean_vault_insolvent_projection(total: u64, shares: u64) -> i32;
    fn lean_vault_wire_invoke(
        operation: u32,
        input: *const u8,
        input_len: usize,
        out: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32;
    fn lean_vault_wire_free(out: *mut u8);
}

pub fn initialize() -> i32 {
    unsafe { lean_vault_initialize() }
}

pub fn insolvent(total: u64, shares: u64) -> bool {
    unsafe { lean_vault_insolvent_projection(total, shares) != 0 }
}

/// Executes a specific Lean LWAB export and copies its complete result frame.
pub fn wire(operation: u32, input: &[u8]) -> Vec<u8> {
    let mut out = std::ptr::null_mut();
    let mut len = 0;
    assert_eq!(
        unsafe {
            lean_vault_wire_invoke(operation, input.as_ptr(), input.len(), &mut out, &mut len)
        },
        1,
        "Lean Vault Wire route invocation"
    );
    assert!(!out.is_null(), "Lean Vault Wire allocates a result");
    let bytes = unsafe { std::slice::from_raw_parts(out, len).to_vec() };
    unsafe { lean_vault_wire_free(out) };
    bytes
}
