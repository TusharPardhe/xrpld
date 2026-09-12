# Quaxar formal verification

This workspace models selected **rippled** behavior in Lean, proves properties of those models, and performs bounded executable comparisons against the production Quaxar Rust crates. It is intentionally outside the production Cargo workspace: production never depends on verification code.

## Source hierarchy

1. rippled implementation/declarations and XRPL amendment rules define compatibility behavior.
2. rippled tests corroborate edge cases and regression intent.
3. Lean provides an executable, reviewable model and kernel-checked theorems.
4. Quaxar is the independent Rust implementation under comparison.

Undefined, implementation-defined, or accidental C++ behavior is not promoted blindly into a protocol rule; it is documented and replaced by an explicit portable boundary contract.

## Layout

- `lean/`: complete Lake project—41 model, 318 property, and 23 FFI Lean modules.
- `rust/crates/verification-wire/`: lossless Lending LWAB types and codecs; no Lean or Quaxar dependency.
- `rust/crates/lean-ffi/`: raw/safe Lean ABI and native C shims; no Quaxar dependency.
- `rust/crates/parity-harness/`: domain runners, executable vectors, manifests, Quaxar calls, and comparison reporting.
- `rust/tests/`: nine migrated public Quaxar regression targets plus one preserved source-coupled internal test.
- `vectors/`: stable vector catalog and domain classification; current executable fixtures are Rust-backed and are labeled as such.
- `coverage/`: rippled ↔ Lean ↔ FFI ↔ Quaxar ↔ vector mappings.
- `scripts/`: orchestration only—no protocol calculations.
- `docs/`: modeling, proof, wire, extension, traceability, ADR, and theorem guidance.
- `evidence/`: reviewed baseline, generated runs, and clearly marked historical reports.

## Dependency direction

```text
rippled source → Lean model → Lean properties
                         └→ Lean FFI → parity harness ← Quaxar production crates
                                   ↑
                           verification-wire
```

Dependencies flow toward the harness only. Neither Quaxar nor the wire/FFI crates depend on the harness.

## Targeted commands

```sh
formal-verification/scripts/check-layout
formal-verification/scripts/check-rust
formal-verification/scripts/check-domain protocol
formal-verification/scripts/check-domain vault
formal-verification/scripts/check-domain lending
```

Lean and parity execution require the pinned local Lean toolchain and model libraries. See `docs/adding-a-domain.md` and `scripts/run-parity` for environment details. Generated build directories and evidence runs are ignored.

## Claim boundary

A Lean theorem is universal only under its written premises. A successful ABI call proves reachability only. A bounded parity run proves equality only for the executed vectors. It does not prove universal Rust↔Lean equivalence. See `CLAIMS.md`.
