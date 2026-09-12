# Source-coupled regression source

`vault_lwab_internal.rs` is preserved byte-for-byte from the original dirty
Quaxar worktree. It uses private `vault_lwab` modules and therefore is not a
standalone Cargo test target. Its unique terminal-association, envelope, and
round-trip assertions are exercised through public APIs by the parity harness
`vault_wire.rs`; the migration mapping is recorded in `../../MIGRATION.md`.
