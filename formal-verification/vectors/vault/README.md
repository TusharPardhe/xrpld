# Vault vectors

Rust-backed executable Vault route, guard, and malformed constructors live in `rust/crates/parity-harness/src/vault/vault_wire.rs`. Public adapter regressions live in `rust/tests/vault/`; the private source-coupled LWAB test is preserved separately and mapped to public route coverage.

Stable IDs and classifications are defined in `../schemas/catalog.toml`. Malformed codec checks are excluded from semantic counts.
