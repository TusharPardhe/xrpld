use lean_ffi::{abi, int_abi, iou_abi, lending_abi, stamount_abi, vault_abi};
use verification_wire as lending_wire;
mod coverage;
#[path = "protocol/direct_domains.rs"]
mod direct_domains;
#[path = "protocol/int_amount.rs"]
mod int_amount;
#[path = "protocol/int_arithmetic.rs"]
mod int_arithmetic;
#[path = "protocol/iou.rs"]
mod iou;
#[path = "lending/lending.rs"]
mod lending;
#[path = "lending/lending_accept.rs"]
mod lending_accept;
#[path = "lending/lending_broker.rs"]
mod lending_broker;
#[path = "lending/lending_create.rs"]
mod lending_create;
#[path = "lending/lending_delete.rs"]
mod lending_delete;
#[path = "lending/lending_manage.rs"]
mod lending_manage;
#[path = "lending/lending_manifest.rs"]
mod lending_manifest;
#[path = "lending/lending_payment.rs"]
mod lending_payment;
#[path = "protocol/number.rs"]
mod number;
#[path = "protocol/stamount.rs"]
mod stamount;
#[path = "protocol/stamount_errors.rs"]
mod stamount_errors;
#[path = "protocol/vectors/stamount_generated.rs"]
mod stamount_generated;
#[path = "protocol/stamount_model.rs"]
mod stamount_model;
#[path = "vault/vault.rs"]
mod vault;
#[path = "vault/vault_manifest.rs"]
mod vault_manifest;
#[path = "vault/vault_registry.rs"]
mod vault_registry;
#[path = "vault/vault_wire.rs"]
mod vault_wire;

fn main() {
    abi::initialize();
    direct_domains::run();
    for mode in [0, 1, 2, 3, 255] {
        assert_eq!(abi::rounding_tag(mode), if mode < 3 { mode } else { 3 });
    }
    assert!(abi::numeric_integral(0));
    assert!(abi::numeric_integral(1));
    assert!(!abi::numeric_integral(2));
    assert!(!abi::numeric_integral(255));
    let number_checks = number::run();
    let iou_checks = iou::run();
    let int_report = int_amount::run();
    let (stamount_checks, stamount_divergences) = stamount::run();
    let vault_checks = vault::run();
    let vault_wire = vault_wire::vectors();
    let vault_report = vault_registry::execute(&vault_wire);
    let lending_create_checks = lending_create::run();
    for export in lending_create::EXPORT_IDS {
        lending_manifest::register_semantic(export);
    }
    let lending_scalar_checks = lending::run();
    let lending_accept_checks = lending_accept::run();
    for export in lending_accept::EXPORT_IDS {
        lending_manifest::register_semantic(export);
    }
    let lending_delete_checks = lending_delete::run();
    for export in lending_delete::EXPORT_IDS {
        lending_manifest::register_semantic(export);
    }
    let lending_payment_checks = lending_payment::run();
    for export in lending_payment::EXPORT_IDS {
        lending_manifest::register_semantic(export);
    }
    let lending_manage_checks = lending_manage::run();
    for export in lending_manage::EXPORT_IDS {
        lending_manifest::register_semantic(export);
    }
    let lending_broker_checks = lending_broker::run();
    for export in lending_broker::EXPORT_IDS {
        lending_manifest::register_semantic(export);
    }
    for export in [
        "lean_lending_has_expired",
        "lean_lending_schedule_build",
        "lean_lending_schedule_interval",
        "lean_lending_schedule_total",
        "lean_lending_schedule_grace",
        "lean_lending_schedule_start",
        "lean_lending_schedule_time_check",
    ] {
        lending_manifest::register_semantic(export);
    }
    let lending_checks = lending_scalar_checks
        + lending_create_checks
        + lending_accept_checks
        + lending_delete_checks
        + lending_payment_checks
        + lending_manage_checks
        + lending_broker_checks;
    coverage::report(
        number_checks,
        iou_checks,
        int_report,
        stamount_checks,
        stamount_divergences,
        vault_checks,
        vault_report,
        &vault_wire,
        lending_checks,
    );
    println!(
        "PASS: modular Lean↔Quaxar protocol export harness completed bounded cross-validation"
    );
}
