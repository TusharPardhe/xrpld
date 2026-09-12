# Migration inventory

## Source families

- Complete Lean source/config/docs: all 390 non-`.lake` working-tree files copied to `lean/`, preserving module names and imports. This includes 41 Model, 318 Properties, and 23 FFI Lean files plus package/config/docs.
- Lending LWAB Rust codec/type modules: moved to `rust/crates/verification-wire/src/`.
- Six ABI Rust modules, runtime wrapper, all 13 C/H bridge files, and native build wiring: moved to `rust/crates/lean-ffi/` (`native/` for C/H).
- Comparison runners, stable manifests, coverage reporting, and fixture constructors: moved to `rust/crates/parity-harness/src/{protocol,vault,lending}`; executable fixture constructors are grouped under domain `vectors/` folders.
- Bridge reports and historical logs: moved to `evidence/archive/`; the authoritative final report is also preserved under `evidence/baselines/2026-09-12/`.

Generated `.lake`, Cargo `target`, caches, binaries, core dumps, and machine-local paths were not imported.

## Dirty Quaxar test artifacts

1. `xrpl/protocol/src/amounts/iou_amount/tests.rs` → `rust/tests/protocol/iou_amount_internal.rs`, adapted only from crate-relative to public imports and compiled.
2. `xrpl/protocol/tests/amounts/amount_floor_parity.rs` → `rust/tests/protocol/amount_floor_parity.rs`, compiled unchanged.
3. `xrpl/protocol/tests/amounts/int_amount_number_conversion.rs` → `rust/tests/protocol/int_amount_number_conversion.rs`, compiled unchanged.
4. `xrpl/protocol/tests/amounts/iou_number_conversion.rs` → `rust/tests/protocol/iou_number_conversion.rs`, compiled unchanged.
5. `xrpl/protocol/tests/amounts/st_amount_surface.rs` → `rust/tests/protocol/st_amount_surface.rs`, compiled unchanged.
6. `xrpl/protocol/tests/amounts/mod.rs` → module-declaration-only artifact; replaced by explicit `[[test]]` entries in `rust/tests/Cargo.toml`.
7. `xrpld/ledger/tests/domain/lending_adapter.rs` → `rust/tests/lending/adapter.rs`, compiled unchanged.
8. `xrpld/ledger/tests/domain/lending_lwab_accept.rs` → `rust/tests/lending/lwab_accept.rs`, adapted from crate-local to public `ledger::lending_lwab` import and compiled.
9. `xrpld/ledger/tests/domain/lending_lwab_delete.rs` → `rust/tests/lending/lwab_delete.rs`, adapted identically and compiled.
10. `xrpld/ledger/tests/domain/vault_adapter.rs` → `rust/tests/vault/adapter.rs`, compiled unchanged.
11. `xrpld/ledger/tests/domain/mod.rs` → module-declaration-only artifact; replaced by explicit Cargo test targets.
12. `xrpld/ledger/src/domain/vault_adapter/lwab_tests.rs` → preserved byte-for-byte as `rust/tests/source-coupled/vault_lwab_internal.rs`. It requires private modules and is not compiled externally; its unique envelope, round-trip, and terminal-association behavior is exercised through public APIs by `parity-harness/src/vault/vault_wire.rs`.

No production test path was added on this branch, and no original dirty worktree was modified.
