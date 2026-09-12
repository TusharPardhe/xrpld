# Vault Lean ↔ Quaxar: independent final cross-validation

**Audit date:** 2026-09-12. This report replaces the invalid historical 36-row report. It uses only the requested authoritative paths:

- Formal repository: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification`
- Formal Lean source: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification`
- Bridge: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke`
- Quaxar: `/Users/tusharpardhe/Documents/xrpl/quaxar`

## Result

Fresh debug and release execution of the actual bridge both completed with:

```text
VAULT COUNTS | source=50 | applicable=50 | ABI=50 | semantic=50 |
unavailable=0 | divergences=0 | semantic_vectors=20 | predicate_vectors=3 |
material_checks=20
VAULT WIRE COUNTS | semantic_routes=12 | guard_results=8 |
malformed_codec_only=72 | byte_divergences=0
```

The required equality holds in both profiles: **source = manifest = ABI = semantic = 50**, with **unavailable = 0** and **divergences = 0**. The bridge completed normally after the counters.

## Source truth and static reconciliation

A fresh recursive scan of every checked-working-tree `*.lean` file below the formal source path, excluding generated `.lake` artifacts only, used a whitespace/newline-tolerant `@[\s*export NAME]` matcher. It scanned 381 Lean files (93 Vault-path files), found 173 total exports and **50 unique Vault-domain exports**. This includes untracked `XRPL/FFI/Vault/Wire.lean`; 28 exports begin `lean_vault_` and the other 22 are Vault result/accessor/helper exports. No alternate annotation spelling produced an additional export.

The exact reconciliation command reported:

```text
RECONCILIATION source=50 manifest=50 ABI=50 routes=12
source-minus-manifest=[]
manifest-minus-source=[]
source-minus-ABI=[]
ABI-minus-source=[]
routes=[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
```

`src/vault_manifest.rs` contains stable IDs V01–V50, one row per source export. The C surface contains all 38 typed/helper symbols plus all 12 generated symbols declared through the `WIRE(...)` macro in `src/vault_wire_bridge.c`. The previous apparent C undercount was a simplistic direct-call grep; token-level reconciliation includes `lean_shares_to_assets_withdraw` and the macro declarations. The 12 real Wire exports are V39–V50:

```text
lean_vault_raw_build_wire                 lean_vault_build_wire
lean_vault_round_deposit_wire             lean_vault_deposit_wire
lean_vault_shares_to_assets_withdraw_wire lean_vault_withdraw_wire
lean_vault_clawback_wire                  lean_vault_burn_shares_raw_wire
lean_vault_burn_shares_wire               lean_vault_can_burn_shares_wire
lean_vault_can_delete_wire                lean_vault_can_set_wire
```

No manifest entry was removed and no source export was added: the former 38-entry typed/helper set was real, and the missing set was precisely the 12 untracked Wire exports.

## Executed semantic operation table

`src/vault_wire.rs` invokes each route through `lean_vault_wire_invoke`, obtains the Quaxar response through `ledger::vault_lwab::dispatch_route`, and asserts equality of the **entire canonical response byte vector**. `XRPL/FFI/Vault/Wire.lean`, `src/vault_wire_bridge.c`, and Quaxar `xrpld/ledger/src/domain/vault_adapter/lwab.rs` use the same tag order.

| Route | Operation | Exports reconciled | Material compared |
|---:|---|---|---|
| 1 | raw build | V01, V39 | complete raw Vault or error frame |
| 2 | terminal build | V02–V10, V14, V40 | terminal Vault and all total/available/maximum/type/tag/scale/shares/loss fields; insolvency also has 3 direct boundaries |
| 3 | deposit rounding | V11–V13, V41 | rounded amount or TER alternative |
| 4 | deposit | V15–V19, V42 | result, amount, shares, post-state Vault, TER/error |
| 5 | shares-to-assets quote | V20–V21, V43 | quote/error and asset/share discriminator |
| 6 | withdraw | V22–V26, V44 | assets, shares, post-state Vault, TER/error |
| 7 | clawback | V27–V31, V45 | assets, shares, post-state Vault, TER/error |
| 8 | raw burn | V32, V46 | raw post-burn Vault/error |
| 9 | terminal burn | V33, V47 | terminal post-burn Vault/error |
| 10 | can burn | V34–V36, V48 | decision, burnable shares, TER/error |
| 11 | can delete | V37, V49 | delete TER |
| 12 | can set | V38, V50 | set TER |

The 12 canonical vectors are successful, complete result comparisons. Eight additional tagged guard vectors compare material error/result alternatives. The 20 comparisons preserve raw-versus-terminal association; complete Vault data (total, available, reserved, maximum, shares, scale, loss, numeric type); typed amounts; and tagged model/TER alternatives. The three direct `lean_vault_is_insolvent` vectors compare the lawful-state predicate for `(100,100)`, `(0,0)`, and `(0,1)`. The 72 malformed frames are checked only for codec agreement and explicitly excluded from semantic coverage; no echo/default/projection-only or malformed-only vector contributes to the 50 semantic IDs.

## Commands and observed validation

```sh
# Exact source / bridge / route reconciliation and bridge formatting
rustfmt --check src/main.rs src/vault_manifest.rs src/vault_registry.rs
# Result: pass; bridge files are 55, 183, and 66 lines.

# Actual bridge package, executed independently
cd /Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke
cargo run --quiet
cargo run --release --quiet
# Both: the 50/50/50/50, unavailable=0, divergences=0 counters above.

# Actual Quaxar ledger package
cd /Users/tusharpardhe/Documents/xrpl/quaxar
cargo test -p ledger vault_adapter --lib
cargo test -p ledger vault_adapter --lib --release
cargo test -p ledger --lib
# Targeted: 2 passed in debug and 2 passed in release.
# Full library: 185 passed; 0 failed.
```

The actual bridge `Cargo.toml` is package `quaxar-lean-number-smoke` and directly paths to Quaxar `basics`, `ledger`, and `protocol`. The tested Quaxar package is `xrpld/ledger/Cargo.toml` (`name = "ledger"`). The formal pin is unchanged at `leanprover/lean4:v4.28.0`, so no pin-change rebuild was required. The targeted and full ledger test runs had no failures to separate. Bridge runs did emit pre-existing unrelated `lending_wire*` unused-import/dead-code warnings; they do not concern Vault and did not affect successful Vault execution.

## State audit and scope

Only inspection commands (`branch --show-current`, `status --short`, `log`, `show-ref`, `diff --stat`) were run against the formal and Quaxar repositories. Formal is on `formal-verification-completion` at `9fe0fea26` with 87 dirty-status entries; Quaxar is on `quaxar-full-verification` at `46ce6c7a` with 27. In each repository both swapped-named local refs point to that repository's current HEAD. The bridge has no `.git` directory. No checkout, rename, reset, restore, revert, clean, discard, commit, push, C++ rippled modification, or credential action occurred. `/tmp/lean-vault-exports.txt` was absent at both inspection points, so no temporary audit artifact remains.

**Bounded caveat:** this establishes exact parity for the 20 executed canonical/guard material vectors plus three insolvency boundaries in both bridge profiles. It is not an exhaustive state-space proof, and it makes no claim for the separately reported Lending surface.

## Lending transition parity status — 2026-09-12

This report’s Vault result must not be interpreted as Lending transition parity. The absolute-path manifest is [`lending-transition-manifest.md`](./lending-transition-manifest.md). It maps all 27 exact LWAB transition tags and full schemas from `XRPL/FFI/Lending/Wire/{Transitions,LoanState,VaultBroker}.lean`.

A fresh `cargo run --quiet` in `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke` reported:

```text
LENDING COUNTS | source_exports=34 | applicable_exports=7 | abi_invoked_exports=34 |
semantic_compared_exports=7 | unavailable_exports=27 | divergences=0 |
raw=16 | terminal=11 | scalar=7 | bounded_executable_checks=327
```

The seven scalar exports (`has_expired` and six schedule projections) are genuinely compared. The 27 raw/terminal LWAB routes are not yet compared against a Quaxar dispatcher: the bridge currently checks Lean output codec determinism and malformed decoder behavior only. Therefore the requested completion counters **cannot honestly be reported** as `semantic=34, unavailable=0` until Quaxar has a lossless LWAB decoder/dispatcher/encoder and the bridge compares both exact bytes and decoded full material states on canonical success and all modeled guard vectors in debug and release.


## Lending terminal association increment — 2026-09-12T16:27+01:00

An absolute-path LWAB manifest now exists at `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/lending-route-manifest.md`. It records all 34 exports, tags 1–27, response tags 129–155, schemas, complete typed results, and the terminal rule: raw transition once, then exactly one Vault association only on a successful result.

Quaxar now has a typed `lending_adapter/terminal.rs` association primitive for `LendingState`, `Vault`, `BrokerVault`, and `LoanVault`; its focused debug test proves one association on success and atomic raw-error/association-overflow behavior. `cargo test -p ledger lending_adapter --lib` passed with **2 passed, 0 failed**. Changed adapter files were formatted with `rustfmt`.

This is deliberately not a full Lending semantic-parity result. The actual bridge baseline run still reports `source_exports=34`, `applicable_exports=7`, `semantic_compared_exports=7`, and `unavailable_exports=27`, because no Quaxar Lending LWAB decoder/dispatcher/encoder is yet invoked by bridge route vectors. Therefore `semantic=34, unavailable=0, divergences=0` is not asserted, and no release full-route semantic test has been claimed for this increment.

Follow-up serial validation: Quaxar release `cargo test -p ledger lending_adapter --lib --release` passed **2/2**; bridge `cargo run --quiet` and `cargo run --release --quiet` both passed, and both retained the truthful Lending output `semantic_compared_exports=7`, `unavailable_exports=27`. The warning output is unused/dead-code material from the not-yet-integrated Lending LWAB dispatcher/vector surface.


## Lending dispatcher integration audit — 2026-09-12T16:38+01:00

No semantic counter was promoted in this audit. The authoritative Lean LWAB schema exists and the bridge invokes every Lean ABI endpoint, but its transition vectors call and decode **Lean only**. `src/lending.rs` imports only `ledger::lending_adapter::lossless::{build_schedule, has_expired}`; it contains no `ledger::lending_*lwab::dispatch_route` call. Therefore route output equality for tags 1–27 is not established.

Fresh serial validation:

```text
Quaxar: cargo test -p ledger lending_adapter --lib --quiet                  PASS (2/2)
Quaxar: cargo test -p ledger lending_adapter --lib --release --quiet        PASS (2/2)
Quaxar: cargo test -p tx loan --quiet                                       PASS (422 + 407)
Quaxar: cargo test -p tx loan --release --quiet                             PASS (422 + 407)
Bridge: cargo run --quiet                                                    PASS
Bridge: cargo run --release --quiet                                          PASS
```

Both bridge profiles reported exactly:

```text
LENDING COUNTS | source_exports=34 | applicable_exports=7 | abi_invoked_exports=34 |
semantic_compared_exports=7 | unavailable_exports=27 | divergences=0 |
raw=16 | terminal=11 | scalar=7 | bounded_executable_checks=327
```

The passing adapter and concrete-handler tests test distinct existing implementations; they do not supply a lossless Quaxar LWAB decoder/dispatcher/encoder or make the bridge compare a Quaxar transition response. Lean operation bodies also differ materially from the current adapter (for example, Lean `Loan.create` calculates amortization/precision/cover guards and `Loan.regularPayment` is scheduled-installment based). Reporting `applicable=34`, `semantic=34`, or `unavailable=0` would consequently be false. No Lean schema changed in this audit, so the pinned Lean build was not rerun.


## Lending accept-family parity — 2026-09-12

The authoritative wrappers in `XRPL/FFI/Lending/Wire/Transitions.lean` are now executed through the bridge for `rawAcceptWire` (request tag 4 / response 132) and `terminalAcceptWire` (request tag 20 / response 148). The Lean model itself was not altered. Quaxar `ledger::lending_lwab::dispatch_route` now losslessly decodes the complete `LoanVaultRequest`, performs the exact modeled raw acceptance update (no invented preclaim guard), and writes the full tagged `LoanVault` lifecycle result. Its terminal route runs raw accept once and then performs the modeled asset association; an association failure returns the error instead of emitting the raw mutation.

`src/lending_accept.rs` sends the same canonical input bytes to Lean and Quaxar, requires exact whole-frame equality, decodes both full typed results, and repeats Quaxar dispatch. Its vectors cover raw and terminal success, raw pre-association behavior with both non-pending and negative-reserved inputs, reachable raw subtraction overflow, terminal association overflow / atomic failure, and malformed magic, version, route tag, length, truncation, trailing, Boolean, and noncanonical body cases. The dedicated Quaxar unit test additionally checks raw result fields, terminal atomic error tag `0`, and malformed-frame determinism.

Fresh serial results:

```text
Lean: lake build XRPL.FFI.Lending.Transitions                         PASS (3137 jobs)
Quaxar debug:  lending_adapter 2/2; compiled LWAB accept test 1/1    PASS
Quaxar release: lending_adapter 2/2; compiled LWAB accept test 1/1  PASS
Bridge debug and release                                               PASS
LENDING COUNTS | source_exports=34 | applicable_exports=12 |
abi_invoked_exports=34 | semantic_compared_exports=12 |
unavailable_exports=22 | divergences=0 | raw=16 | terminal=11 | scalar=7 | bounded_executable_checks=403
```

The two semantic IDs are registered only after those executed byte-and-typed-result comparisons. This is a real accept-family increment from 10/24 to **12 semantic / 22 unavailable / 0 divergences** in both profiles; it is not a claim that the other 22 Lending transition routes are implemented.


## Lending accept-family parity correction — 2026-09-12T17:14+01:00

The accept routes remain registered only after execution-derived comparisons: raw `lean_lending_raw_accept_wire` (tag 4 → response 132) and terminal `lean_lending_terminal_accept_wire` (tag 20 → response 148). For every vector, the bridge supplies identical LWAB request bytes to Lean and `ledger::lending_lwab::dispatch_route`, requires complete response-byte equality, decodes both complete `LoanVault` lifecycle responses, compares typed values, and repeats Quaxar dispatch.

The extended vectors exposed two terminal association mismatches and both are repaired. Integral association now compares Lean’s nearest-rounded integral amount, rather than the normalized Number mantissa, and returns the canonical signed integral Number; the native integral success vector retains all NumericType fields (`maximum`, `offset`, `sqrt`, `shift`) and the complete Loan/Vault result. Fractional association below the IOU representable range now returns Lean’s canonical zero fields instead of `notLawful`; the exponent -100 vector verifies canonical zero total, available, reserved, and unrealized loss. The remaining vectors cover raw/terminal success, raw no-preclaim behavior (including negative reserved assets), raw overflow, terminal out-of-range, terminal overflow/atomic failure, malformed envelope/body classes, and repeatability. No `notLawful` result is reachable through the lossless accept decoder: Vault inputs are already lawful, accept mutates only reserved assets, and association either preserves or canonicalizes those asset fields.

Focused final validation (no full suite): pinned Lean `lake build XRPL.FFI.Lending.Transitions` passed (`3137 jobs`); Quaxar `lending_adapter` and `lwab_accept` focused tests passed in debug (2/2 and 1/1) and release (2/2 and 1/1); bridge `cargo run --quiet` and `cargo run --release --quiet` both passed. Each bridge profile reports:

```text
LENDING COUNTS | source_exports=34 | applicable_exports=12 |
abi_invoked_exports=34 | semantic_compared_exports=12 |
unavailable_exports=22 | divergences=0 | raw=16 | terminal=11 | scalar=7 |
bounded_executable_checks=403
```

Changed Rust files are rustfmt-clean and under 200 lines; no rippled C++ source was changed. Existing warning output is unused/dead-code material outside this focused behavior.


## Final Lending completion and PR #44 invariant backmerge — 2026-09-12T19:20+01:00

This section supersedes the earlier incomplete Lending counters below/above in this historical report. PR #44 was **not** merged wholesale: its useful LoanBroker invariant work was semantically adapted to the current identity-aware model while retaining the newer Lending FFI/Wire/Terminal and Vault association modules absent from that PR.

Lean additions now include identity-preserving `LoanBroker.Exact`/`toExact`, `LoanBroker.WF`, `LoanBroker.Exact.Valid`, operator-level `LoanBroker.Valid`, `LoanBroker.Lawful`, `LawfulLoanBroker`, executable `LoanBroker.validate`, constructive `Decidable` instances, and the universal `LoanBroker.valid_iff_exact` theorem under its explicit product-totality/headroom premises. The focused `XRPL.Properties.LoanBroker.LoanBroker` build and aggregate `XRPL.Properties.Properties` build passed under pinned Lean 4.28.0. A scoped scan found no `sorry`, `admit`, new `axiom`, `native_decide`, `unsafe`, or placeholder in the new LoanBroker proof modules.

The Quaxar/bridge Lending implementation now executes all 27 transition routes plus seven scalar helpers. Independent debug and release bridge executions each reported:

```text
LENDING COUNTS | source_exports=34 | applicable_exports=34 |
abi_invoked_exports=34 | semantic_compared_exports=34 |
unavailable_exports=0 | divergences=0 | raw=16 | terminal=11 | scalar=7 |
bounded_executable_checks=682
PASS: modular Lean↔Quaxar protocol export harness completed bounded cross-validation
```

Independent focused validation:

```text
cargo test -p ledger lending_lwab -- --test-threads=1
# 3 passed; 0 failed; 186 filtered out

cargo check --manifest-path /Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/Cargo.toml
# PASS

cargo run --quiet --manifest-path /Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/Cargo.toml
cargo run --release --quiet --manifest-path /Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/Cargo.toml
# Both PASS with the 34/34 matrix above
```

The same runs retained Protocol zero-divergence counters and Vault `source=applicable=ABI=semantic=50`, `unavailable=0`, `divergences=0`; Vault wire remained 12 semantic routes, eight guard results, 72 malformed codec-only frames, and zero byte divergences. Complete Lending route responses are compared as full bytes and decoded typed values with repeatability and malformed/noncanonical coverage. All bridge `lending*.rs` files are at most 194 lines. Lean and Quaxar `git diff --check` passed, and no C/C++ path was changed.

**Bounded caveat:** 34/34 means every declared Lending export has genuine executable semantic comparisons in this bounded harness. It is not a universal proof that Rust/Quaxar equals Lean for every possible input. Universal claims apply to the Lean theorems under their premises; the Rust connection remains bounded cross-validation.
