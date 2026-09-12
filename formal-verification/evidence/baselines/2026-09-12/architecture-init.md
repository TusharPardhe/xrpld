# Formal-verification architecture initialization evidence

Date: 2026-09-12

## Revisions

- rippled source revision: `9fe0fea2629ac455af4d38ec529dc7652f7fcbbb`
- Quaxar stacked implementation base: `7df371464d57459f4ba3bb06f09d8ead47ef571c`
- Lean toolchain: `leanprover/lean4:v4.28.0`

The Quaxar base includes the follow-up production-only `lending_adapter/core.rs` repair discovered by clean-checkout regression compilation and pushed to implementation PR #46.

## Migration integrity

- 390 non-generated Lean project files copied byte-for-byte.
- 41 Model, 318 Properties, and 23 FFI Lean modules.
- 11 verification-wire Rust modules with no Lean/Quaxar dependency.
- 8 lean-ffi Rust/build files and 13 native C/H bridge files with no Quaxar dependency.
- 34 parity-harness Rust/build files grouped by Protocol, Vault, Lending, and executable vectors.
- Nine externally compiled migrated Quaxar test files; one private Vault LWAB test preserved byte-for-byte and covered through public harness routes.
- No tracked `.lake`, Cargo `target`, cache, binary, or core artifact.
- No active absolute developer path.
- Every bridge Rust source file is at most 200 lines.

## Validation

- `scripts/check-layout`: pass.
- `scripts/check-rust`: offline Cargo metadata and formatting pass.
- Focused relocated Lean build: pass, 3323 jobs; existing nonfatal lint warnings only.
- All domain scripts: pass with Lean rebuild skipped after the focused Lean run.
- Migrated public Rust regressions: 31 tests passed, zero failed.
- verification-wire, lean-ffi, and parity-harness Cargo check: pass.
- Reorganized parity harness debug and release: pass.

Both parity profiles reproduced:

```text
VAULT COUNTS | source=50 | applicable=50 | ABI=50 | semantic=50 | unavailable=0 | divergences=0
VAULT WIRE COUNTS | semantic_routes=12 | guard_results=8 | malformed_codec_only=72 | byte_divergences=0
LENDING COUNTS | source_exports=34 | applicable_exports=34 | abi_invoked_exports=34 | semantic_compared_exports=34 | unavailable_exports=0 | divergences=0 | raw=16 | terminal=11 | scalar=7 | bounded_executable_checks=682
```

Protocol counters also retained zero divergence classes and zero concrete divergence observations.

## Claim boundary

The Lean theorems are universal only under their written premises. Debug/release equality above is bounded executable comparison over the catalogued harness vectors. ABI reachability is not semantic parity, malformed codec cases do not contribute to semantic coverage, and this evidence is not a universal Rust↔Lean refinement proof.
