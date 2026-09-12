# Adding a verified domain

1. Add pure executable semantics under `lean/XRPL/Model/<Domain>/` and cite the pinned rippled symbols in the module header.
2. Define representation well-formedness separately from exact/business validity.
3. Add universal theorems under `lean/XRPL/Properties/<Domain>/`; keep every premise visible.
4. Add stable scalar or byte-array exports under `lean/XRPL/FFI/<Domain>/` without duplicating the model operation.
5. Add versioned codec types to `verification-wire` only when shared by multiple runners; otherwise use the production codec through the harness.
6. Add safe ABI wrappers to `lean-ffi`; confine raw pointers and C calls there.
7. Add executable fixture constructors under `parity-harness/src/<domain>/vectors/` and stable IDs to `vectors/schemas/catalog.toml`.
8. Add a `coverage/<domain>.toml` mapping rippled source, Lean definitions/theorems/exports, Quaxar APIs, and vector IDs.
9. Add public regression tests under `rust/tests/<domain>/`; preserve private source-coupled tests explicitly rather than weakening them silently.
10. Run layout, domain Lean, Rust regressions, and debug/release parity. Promote a generated run to `evidence/baselines/` only after review.

Use `SKIP_LEAN=1` only for a local lightweight pass; CI/release evidence must include the relevant Lean targets. Never add a production algorithm to this workspace.
