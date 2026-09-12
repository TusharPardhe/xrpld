use std::{cell::RefCell, collections::BTreeSet};

pub const SOURCE_EXPORTS: usize = 34;
pub const RAW_INTERNAL_EXPORTS: usize = 16;
pub const TERMINAL_EXPORTS: usize = 11;
pub const ABI_INVOKED_EXPORTS: usize = 34;
pub const DIVERGENCES: usize = 0;
pub const SCALAR_EXPORTS: usize = 7;

thread_local! { static EXECUTED_SEMANTIC: RefCell<BTreeSet<&'static str>> = const { RefCell::new(BTreeSet::new()) }; }
pub fn register_semantic(export: &'static str) {
    assert!(
        MANIFEST.iter().any(|(id, _)| *id == export),
        "unknown Lending export ID"
    );
    assert!(
        EXECUTED_SEMANTIC.with(|ids| ids.borrow_mut().insert(export)),
        "duplicate Lending semantic export ID"
    );
}
pub fn semantic_compared_exports() -> usize {
    EXECUTED_SEMANTIC.with(|ids| ids.borrow().len())
}
pub fn unavailable_exports() -> usize {
    SOURCE_EXPORTS - semantic_compared_exports()
}

pub const MANIFEST: [(&str, &str); SOURCE_EXPORTS] = [
    ("lean_lending_has_expired", "SCALAR: expiry boundary"),
    (
        "lean_lending_schedule_build",
        "SCALAR: schedule construction",
    ),
    (
        "lean_lending_schedule_interval",
        "SCALAR: schedule interval",
    ),
    ("lean_lending_schedule_total", "SCALAR: schedule total"),
    ("lean_lending_schedule_grace", "SCALAR: schedule grace"),
    ("lean_lending_schedule_start", "SCALAR: schedule start"),
    ("lean_lending_schedule_time_check", "SCALAR: schedule TER"),
    ("lean_lending_raw_create_wire", "RAW: ByteArray route"),
    (
        "lean_lending_raw_create_pending_wire",
        "RAW: ByteArray route",
    ),
    (
        "lean_lending_raw_create_immediate_wire",
        "RAW: ByteArray route",
    ),
    ("lean_lending_raw_accept_wire", "RAW: ByteArray route"),
    ("lean_lending_raw_delete_wire", "RAW: ByteArray route"),
    (
        "lean_lending_raw_regular_payment_wire",
        "RAW: ByteArray route",
    ),
    ("lean_lending_raw_late_payment_wire", "RAW: ByteArray route"),
    ("lean_lending_raw_full_payment_wire", "RAW: ByteArray route"),
    (
        "lean_lending_raw_manage_impair_wire",
        "RAW: ByteArray route",
    ),
    (
        "lean_lending_raw_manage_unimpair_wire",
        "RAW: ByteArray route",
    ),
    (
        "lean_lending_raw_manage_default_wire",
        "RAW: ByteArray route",
    ),
    (
        "lean_lending_raw_broker_create_wire",
        "RAW: ByteArray route",
    ),
    (
        "lean_lending_raw_broker_update_wire",
        "RAW: ByteArray route",
    ),
    (
        "lean_lending_raw_cover_validate_wire",
        "RAW: ByteArray route",
    ),
    (
        "lean_lending_raw_cover_deposit_wire",
        "RAW: ByteArray route",
    ),
    (
        "lean_lending_raw_cover_withdraw_wire",
        "RAW: ByteArray route",
    ),
    (
        "lean_lending_terminal_create_wire",
        "TERMINAL: ByteArray route",
    ),
    (
        "lean_lending_terminal_create_pending_wire",
        "TERMINAL: ByteArray route",
    ),
    (
        "lean_lending_terminal_create_immediate_wire",
        "TERMINAL: ByteArray route",
    ),
    (
        "lean_lending_terminal_accept_wire",
        "TERMINAL: ByteArray route",
    ),
    (
        "lean_lending_terminal_delete_wire",
        "TERMINAL: ByteArray route",
    ),
    (
        "lean_lending_terminal_regular_payment_wire",
        "TERMINAL: ByteArray route",
    ),
    (
        "lean_lending_terminal_late_payment_wire",
        "TERMINAL: ByteArray route",
    ),
    (
        "lean_lending_terminal_full_payment_wire",
        "TERMINAL: ByteArray route",
    ),
    (
        "lean_lending_terminal_manage_impair_wire",
        "TERMINAL: ByteArray route",
    ),
    (
        "lean_lending_terminal_manage_unimpair_wire",
        "TERMINAL: ByteArray route",
    ),
    (
        "lean_lending_terminal_manage_default_wire",
        "TERMINAL: ByteArray route",
    ),
];
const _: () = {
    assert!(MANIFEST.len() == SOURCE_EXPORTS);
    assert!(RAW_INTERNAL_EXPORTS + TERMINAL_EXPORTS + SCALAR_EXPORTS == SOURCE_EXPORTS);
    assert!(ABI_INVOKED_EXPORTS == SOURCE_EXPORTS);
};
