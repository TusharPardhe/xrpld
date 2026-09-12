# Architecture

## Purpose

Keep production code easy to navigate while making formal artifacts independently buildable, reviewable, and scalable. This directory contains specifications, proofs, adapters, vectors, mappings, and evidence—not a second production implementation.

## Components

### Lean model

`lean/XRPL/Model/{Protocol,Vault,Lending}` contains pure executable semantics derived from rippled. Models preserve branch order, rounding points, result/error alternatives, and complete identity-bearing state. They do not import Quaxar.

### Lean properties

`lean/XRPL/Properties/` contains theorem statements and proofs. `Common` is allowed only for precisely named lemmas reused by multiple operations; generic `Utils`, `Misc`, and dumping-ground modules are prohibited. Universal proofs may not use `sorry`, `admit`, new axioms, `native_decide`, or `unsafe` shortcuts.

### Lean FFI

`lean/XRPL/FFI/` exposes stable scalar or byte-array wrappers. Each wrapper decodes, calls one existing model operation, and encodes the complete tagged result. It must not reimplement behavior or discard fields.

### Verification wire crate

`rust/crates/verification-wire` owns versioned LWAB decoding/encoding and typed records. It has no Lean, Quaxar, or harness dependency. Malformed/noncanonical codec observations never count as semantic operation coverage.

### Lean FFI crate

`rust/crates/lean-ffi` confines raw `extern "C"`, pointer ownership, Lean runtime initialization, and C shims. Native sources live in `native/`; safe Rust call surfaces live in `src/`. No Quaxar imports are permitted.

### Parity harness

`rust/crates/parity-harness` is the only component allowed to depend on both verification crates and production Quaxar. Physical folders group Protocol, Vault, and Lending. Executable fixtures live in each domain's `vectors/` directory. A run sends identical inputs to Lean and Quaxar, compares complete bytes and typed values, repeats deterministic routes, and reports stable counters.

### Regression tests

`rust/tests` compiles migrated public test behavior outside production paths. Tests requiring private production modules are preserved under `source-coupled/`, mapped to equivalent public harness checks, and excluded from Cargo targets rather than silently weakened.

## Raw and terminal operations

A raw transition changes only model state. A terminal transition executes the raw transition exactly once and performs exactly one asset association on success. Failed raw execution or failed association publishes no partially mutated result.

## Scaling rule

Every new domain gets the same six artifacts: Model, Properties, FFI, executable vectors, coverage mapping, and theorem catalog. Stable IDs—not file order—identify exports and vectors. Generated results go under `evidence/runs`; reviewed baselines are promoted manually.

## Prohibited coupling

- No production dependency on `formal-verification/`.
- No copied Quaxar or rippled algorithm in the harness.
- No hard-coded expected arithmetic in shell scripts.
- No absolute developer paths in active source/configuration.
- No generated `.lake`, `target`, caches, binaries, or core dumps in Git.
- No bridge Rust source file over 200 lines.
