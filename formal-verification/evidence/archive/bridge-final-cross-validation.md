
## Lending raw-create tag-1 semantic proof (2026-09-12)

The bridge invokes authoritative `lean_lending_raw_create_wire` and Quaxar `ledger::lending_lwab::dispatch_route(1, input)` with identical canonical frames. It compares complete tag-129 bytes, decoded `Lifecycle<LendingState>` material, and repeatability for immediate, pending, and nonzero-interest successful creation plus invalid identity, available-funds, cover-funds, debt-limit, and precision-loss rejections. It also checks the complete Lean diagnostic payload for malformed magic, version, tag, truncated, oversized-length, trailing, boolean, option, numeric-type, and noncanonical tag-1 frames. The runtime export-ID registry admits `lean_lending_raw_create_wire` only after these assertions; the executed report therefore derives Lending `semantic=8` and `unavailable=26` (not constants).

# Vault Lean ↔ Quaxar complete cross-validation

**Date:** 2026-09-12. This report covers the 38 authoritative Vault FFI exports. It distinguishes complete semantic material from codec-only malformed vectors and does **not** count `lean_vault_complete_adapter`, request echoes, zero defaults, numeric projections, or ABI reachability as parity.

## Executed result

Both bridge profiles completed with the runtime-derived result:

```text
VAULT COUNTS | source=38 | applicable=38 | ABI=38 | semantic=38 |
unavailable=0 | divergences=0 | semantic_vectors=20 | predicate_vectors=3 |
material_checks=20
VAULT WIRE COUNTS | semantic_routes=12 | guard_results=8 |
malformed_codec_only=72 | byte_divergences=0
```

The registry records each stable ID once in separate ABI and semantic sets, rejects a duplicate insertion, requires all IDs to be present, and derives every count from those sets. Each route invokes Lean through `lean_vault_wire_invoke` and invokes Quaxar's lossless `vault_lwab::dispatch_route` with the same request. It compares the complete response bytes: full Vault state (total, available, reserved, maximum, shares, scale, loss, numeric type), full STAmounts, raw/terminal association, result alternatives, and exact tagged model/TER errors. The three insolvency predicate boundaries are separately executed; they are genuine predicates, not numeric projections.

## Authoritative one-to-one manifest

A route is an operation-family ABI export. Accessor IDs share the complete material result of their owning operation; this avoids separately counting projections while still comparing every accessor's represented result field once.

| ID | Authoritative Lean export | LWAB route | Compared material |
|---|---|---:|---|
| V01 | `lean_vault_build_raw` | 1 | raw Vault or model error |
| V02 | `lean_vault_build` | 2 | terminal Vault or model error |
| V03 | `lean_vault_assets_total` | 2 | terminal `assetsTotal` |
| V04 | `lean_vault_assets_available` | 2 | terminal `assetsAvailable` |
| V05 | `lean_vault_assets_maximum` | 2 | present/absent maximum and Number |
| V06 | `lean_vault_numeric_type` | 2 | complete numeric type |
| V07 | `lean_vault_numeric_tag` | 2 | numeric-type tag |
| V08 | `lean_vault_scale` | 2 | scale |
| V09 | `lean_vault_shares_total` | 2 | shares total |
| V10 | `lean_vault_loss_unrealized` | 2 | unrealized loss |
| V11 | `lean_rounded_deposit_amount` | 3 | rounded amount or rejection |
| V12 | `lean_rounded_deposit_result_amount` | 3 | rounded amount alternative |
| V13 | `lean_rounded_deposit_result_code` | 3 | exact rounding TER |
| V14 | `lean_vault_is_insolvent` | 2 + predicate | lawful-state predicate boundaries |
| V15 | `lean_vault_deposit` | 4 | full deposit result/error |
| V16 | `lean_deposit_result_amount` | 4 | deposited STAmount |
| V17 | `lean_deposit_result_shares` | 4 | issued-share STAmount |
| V18 | `lean_deposit_result_vault` | 4 | complete post-deposit Vault |
| V19 | `lean_deposit_result_error` | 4 | tagged deposit TER |
| V20 | `lean_shares_to_assets_withdraw` | 5 | quote STAmount/error |
| V21 | `lean_mk_withdraw_amount` | 5 | asset/share discriminator |
| V22 | `lean_vault_withdraw` | 6 | full withdraw result/error |
| V23 | `lean_withdraw_result_assets` | 6 | assets STAmount |
| V24 | `lean_withdraw_result_shares` | 6 | burned-share STAmount |
| V25 | `lean_withdraw_result_vault` | 6 | complete post-withdraw Vault |
| V26 | `lean_withdraw_result_error` | 6 | tagged withdraw TER |
| V27 | `lean_vault_clawback` | 7 | full clawback result/error |
| V28 | `lean_clawback_result_assets` | 7 | recovered STAmount |
| V29 | `lean_clawback_result_shares` | 7 | destroyed-share STAmount |
| V30 | `lean_clawback_result_vault` | 7 | complete post-clawback Vault |
| V31 | `lean_clawback_result_error` | 7 | tagged clawback TER |
| V32 | `lean_vault_burn_shares_raw` | 8 | raw post-burn Vault/error |
| V33 | `lean_vault_burn_shares` | 9 | terminal post-burn Vault/error |
| V34 | `lean_can_burn_shares` | 10 | burn decision |
| V35 | `lean_can_burn_result_assets` | 10 | burnable-share amount |
| V36 | `lean_can_burn_result_code` | 10 | exact burn TER |
| V37 | `lean_can_vault_delete` | 11 | exact delete TER |
| V38 | `lean_can_vault_set` | 12 | exact set TER |

The 12 route associations are: raw build (1), terminal build (2), deposit rounding (3), deposit (4), share-to-asset quote (5), withdraw (6), clawback (7), raw burn (8), terminal burn (9), can-burn (10), can-delete (11), and can-set (12). The overlap called out in the prior audit is V20: it is both the prior typed helper and the route-5 material comparison. The prior 10 typed IDs are V03–V10, V14, V20; the prior wire IDs are V01, V02, V11, V15, V20, V22, V27, V32–V34, V37–V38. The remaining former typed/property IDs are V12–V13, V16–V19, V21, V23–V26, V28–V31, and V35–V36; they are now covered by the full material result of their owning route.

## Vectors and checks

- **12 success vectors:** one canonical, complete request/result for every route. The raw/terminal build and burn pairs retain their distinct response tags and association boundaries.
- **8 tagged guard vectors:** precision, donation/empty, zero share, negative/zero clawback, raw/terminal burn, and can-burn rejection boundaries. These compare complete tagged result/error frames.
- **3 predicate boundaries:** solvent, empty, and insolvent Vault states.
- **72 malformed frames:** six envelope failures for each route. These confirm decoder parity only and are deliberately excluded from the 38 semantic IDs and 20 material checks.

## Validation

Executed after the registry and material-route integration:

```sh
# Quaxar (debug and release)
cargo test -p ledger vault_adapter --lib
cargo test -p ledger vault_adapter --lib --release

# Lean ↔ Quaxar bridge (debug and release)
cargo run --quiet
cargo run --release --quiet

# Formatting and file limits
rustfmt --check src/main.rs src/vault.rs src/vault_abi.rs src/vault_wire.rs \
  src/vault_registry.rs src/coverage.rs
wc -l src/main.rs src/vault.rs src/vault_abi.rs src/vault_wire.rs \
  src/vault_registry.rs src/coverage.rs
```

Both Quaxar runs passed two targeted Vault adapter tests. Both bridge runs passed the registry assertions and all material comparisons with zero divergences. `rustfmt --check` passed; all modified bridge implementation files were at most 173 lines. The Quaxar tests emitted pre-existing warnings in unrelated Lending wire modules only. No C++ rippled source was built or changed; no credentials, commits, pushes, resets, restores, cleans, or discard operations were used.

## Lending raw-create tags 1–3 parity (2026-09-12)

Quaxar now dispatches raw create tags 1, 2, and 3 with responses 129, 130, and 131 through one full NumberParts create core. Tag 1 retains the decoded request boolean; tags 2 and 3 deliberately decode that boolean and then force pending/immediate behavior, matching Lean `Loan.createPending` and `Loan.createImmediate`. Debug and release bridge execution compared byte-identical full `Lifecycle<LendingState>` responses, typed results, inherited guards, exact malformed DecodeError frames/offsets, and repeatability. Runtime evidence: `semantic_compared_exports=10`, `unavailable_exports=24`, `divergences=0`, and `bounded_executable_checks=381`. The export IDs were registered only after the vectors completed.

Focused validation passed in both profiles: `cargo test -p ledger lending_lwab --lib`, `cargo test -p ledger lending_lwab --lib --release`, `cargo run --quiet`, and `cargo run --release --quiet`. No full ledger suite, Lean schema change, C++ rippled change, credential use, commit, push, reset, restore, revert, clean, or discard operation was performed.
