//! Exact value types for version-one Lean Lending wire frames.

#[path = "lending_wire_types_identity.rs"]
mod lending_wire_types_identity;
#[path = "lending_wire_types_model.rs"]
mod lending_wire_types_model;

pub use lending_wire_types_identity::*;
pub use lending_wire_types_model::*;
