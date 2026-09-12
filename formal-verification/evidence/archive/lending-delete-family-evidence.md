# Lending delete-family parity evidence — 2026-09-12

Authoritative Lean source: `formal_verification/XRPL/FFI/Lending/Wire/Transitions.lean` exports raw tag 5 / response 133 as `Loan.delete r.loan r.vault r.broker`, and terminal tag 21 / response 149 as `Loan.delete_terminal r.loan r.vault r.broker`.

Implemented Quaxar `ledger::lending_lwab` dispatches both tags and decodes/encodes complete `BrokerRequest`/`BrokerVault` LWAB material. The raw implementation follows `LoanDelete.lean`: pending deletion restores available assets, releases reserved principal, revalidates the vault, rounds/clamps broker debt after principal removal, and decrements the broker count; active deletion decrements the count and clears debt only when it becomes zero. All unmodified broker fields, identities, Number fields, optional maximum, numeric type, and Vault fields remain lossless. This authoritative raw model has no identity, authorization, obligation, or preclaim rejection branch; the parity vectors preserve that behavior rather than inventing a guard.

Terminal tag 21 calls raw once and runs one modeled association over all asset-valued fields (total, available, reserved, optional maximum, loss). Association failures return only the tagged model error; no raw post-state is exposed.

Focused coverage compares identical canonical frames against Lean and Quaxar: pending/active success, complete typed `BrokerResult`, identity/authorization material, lawfulness failure, broker debt/count and cover preservation, terminal association success/failure, malformed magic/tag/truncation/trailing/body, response-byte equality, and repeatability. Tags are registered only after these comparisons.

Validation (all with `CARGO_BUILD_JOBS=1`):
- `cargo test -p ledger lwab_delete_preserves --lib` — pass.
- `cargo test -p ledger lwab_delete_preserves --lib --release` — pass.
- `cargo run --quiet` — pass: `semantic_compared_exports=14`, `unavailable_exports=20`, `divergences=0`, `bounded_executable_checks=419`.
- `cargo run --release --quiet` — same pass and counts.

No Lean model, C++ rippled source, credentials, git branch, commit, push, reset, restore, revert, clean, or discard action was used.
