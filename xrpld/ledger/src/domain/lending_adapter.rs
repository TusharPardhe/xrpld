//! Lossless XLS-66 domain core. Ledger handlers load/persist records; this
//! module owns only pure identity-preserving guards, math, and transitions.

mod core;
mod model;
mod operations;
mod terminal;

pub mod lossless {
    pub use super::core::*;
    pub use super::model::*;
    pub use super::operations::*;
}

pub use lossless::*;
