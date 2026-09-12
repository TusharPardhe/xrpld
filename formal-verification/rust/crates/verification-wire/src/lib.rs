//! Lossless LWAB v1 Lending codec and typed records.  This crate has no FFI or Quaxar dependency.
#[path = "lending_wire.rs"]
mod lending_wire;
pub use lending_wire::*;
