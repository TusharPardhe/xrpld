//! First `xrpld/app` caller seams above the landed tx and rpc validity
//! surfaces.
//!
//! This crate ports the deterministic validity-control-flow shells from
//! the reference implementation and the current application-runtime facade that sits above
//! the landed SHAMap family seams.

#![allow(
    clippy::collapsible_if,
    clippy::redundant_closure,
    clippy::too_many_arguments,
    clippy::type_complexity
)]

// Every executable hosting the application runtime must use the same allocator
// that the periodic sweep purges. Keeping this in the library also covers the
// standalone `quaxar-app` binary and prevents false allocator telemetry.
#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

// Keep transient, cross-thread SHAMap acquisition graphs in one normal arena
// so released size classes can immediately reuse the same page runs. Testnet
// full-state measurement showed four arenas stranded active pages above the
// xrpld RSS baseline; jemalloc still creates a separate oversize arena.
#[cfg(not(target_env = "msvc"))]
const JEMALLOC_CONF: &std::ffi::CStr = c"narenas:1,dirty_decay_ms:0,muzzy_decay_ms:0";

#[cfg(not(target_env = "msvc"))]
#[used]
#[allow(non_upper_case_globals)]
#[unsafe(no_mangle)]
pub static _rjem_malloc_conf: Option<&'static libc::c_char> =
    Some(unsafe { &*JEMALLOC_CONF.as_ptr().cast::<libc::c_char>() });

#[cfg(all(test, not(target_env = "msvc")))]
mod allocator_configuration_tests {
    #[test]
    fn jemalloc_configuration_bounds_arenas_and_zeroes_decay() {
        assert_eq!(
            super::JEMALLOC_CONF.to_bytes(),
            b"narenas:1,dirty_decay_ms:0,muzzy_decay_ms:0"
        );
    }
}
// Organized module groups
pub mod amendments;
pub mod bootstrap;
pub mod consensus;
pub mod job;
pub mod ledger;
pub mod ledger_to_json;
pub mod load;
pub mod network;
pub mod node_family;
pub mod paging;
pub mod preflight;
pub mod runtime;
pub mod server;
pub mod shamap;
pub mod state;
pub mod tx_queue;
pub mod validator;
pub mod work;

// Re-export module paths from the `paths` subdirectory (preserved as-is)
pub mod paths;

// Re-export all public items for backward compatibility
pub use amendments::{amendment_status::*, negative_unl_vote::*};
pub use basics::log::{LogSeverity, Logs};
pub use bootstrap::{bootstrap::*, build_ledger::*};
pub use consensus::{censorship_detector::*, fetch_pack::*, rcl_cx_peer_pos::*};
pub use consensus::{consensus_trans_set_sf::*, driver::*, rcl_consensus::*, rcl_validations::*};
pub use job::{job_queue::*, job_types::*};
pub use ledger::{
    inbound_ledgers::*, ledger_history::*, ledger_master_runtime::*, ledger_master_state::*,
    ledger_persistence_runtime::*, loaded_ledger_runtime::*, open_ledger::*,
};
pub use ledger_to_json::{ledger_to_json_context::*, ledger_to_json_entrypoint::*};
pub use load::{deliver_max::*, fee_vote::*, load_fee_track::*, load_manager::*};
pub use network::{
    network_ops::*, network_ops_runtime::*, network_ops_strand::*,
    network_ops_validation_runtime::*,
};
pub use node_family::node_family::*;
pub use paging::account_tx_paging::*;
pub use runtime::component_runtime::*;
pub use runtime::{main_runtime::*, overlay_runtime::*, resolver_runtime::*};
pub use server::{grpc_server::*, server_okay::*, server_ports::*};
pub use shamap::{
    shamap_store::*, shamap_store_app_runtime::*, shamap_store_backend::*,
    shamap_store_bootstrap::*, shamap_store_component::*, shamap_store_config::*,
    shamap_store_copy::*, shamap_store_health::*, shamap_store_paths::*,
    shamap_store_relational::*, shamap_store_rotation::*, shamap_store_runloop::*,
    shamap_store_runtime_state::*, shamap_store_saved_state::*, shamap_store_saved_state_db::*,
    shamap_store_service::*, shamap_store_sql::*, shamap_store_worker::*,
};
pub use state::{
    app_registry::*, application_root::*, basic_app::*, collector_manager::*, manifest::*,
    node_identity::*, node_store_scheduler::*, overlay_status::*, status_metrics::*,
    status_rpc_state::*, stop_tree::*, time_keeper::*, tuning::*,
};
pub use tx_queue::{transaction::*, transaction_master::*, txq::*, vote_tx_set::*};
pub use validator::{validator_keys::*, validator_list::*, validator_site::*};
pub use xrpl_core::{LoadMonitorJournalFactory, ServiceRegistry};

// ── Dynamic log level reload ────────────────────────────────────────────────
use std::sync::OnceLock;

type LogReloadFn = Box<dyn Fn(&str) -> Result<(), String> + Send + Sync>;
static LOG_RELOAD_FN: OnceLock<LogReloadFn> = OnceLock::new();

/// Called by main at startup to register the tracing reload handle.
pub fn set_log_reload_fn(f: impl Fn(&str) -> Result<(), String> + Send + Sync + 'static) {
    LOG_RELOAD_FN.set(Box::new(f)).ok();
}

/// Reload the tracing filter at runtime. Returns Err if not initialized or invalid filter.
pub fn reload_log_filter(filter: &str) -> Result<(), String> {
    let f = LOG_RELOAD_FN.get().ok_or("Log reload not initialized")?;
    f(filter)
}

/// Wrap a real `Arc<Ledger>` as the `consensus::RclCxLedger` view that the
/// `Consensus<Adaptor>` state machine and the `ConsensusRunner` trait use.
/// `RclCxLedger` is a thin, clone-cheap wrapper over `Arc<Ledger>` that
/// exposes only the id/seq/close-time accessors the generic algorithm needs.
/// Matches the reference's implicit `RCLCxLedger{ledger}` construction at
/// each `startRound`/`gotTxSet` call site.
pub fn consensus_ledger_from_ledger(
    ledger_arc: &std::sync::Arc<::ledger::Ledger>,
) -> ::consensus::RclCxLedger {
    ::consensus::RclCxLedger::new(std::sync::Arc::clone(ledger_arc))
}

/// A no-op `ledger::LedgerJournal`, re-exported under this name for call
/// sites (e.g. `xrpld/main`'s ledger-catch-up logic) that construct a
/// [`consensus::rcl_validation::RclValidatedLedger`] via
/// [`validated_ledger_from_ledger`] without a real diagnostics journal
/// wired in.
pub use ::ledger::NullLedgerJournal as NullRclValidationJournal;

/// Wrap a real `&ledger::Ledger` as the ancestor-trie-carrying
/// `RclValidatedLedger` that the validations tracker needs for
/// `get_preferred`/`get_preferred_lcl` queries.  `RclValidatedLedger`
/// eagerly caches its ancestor hash vector so that Byzantine-safe ledger
/// preference resolution does not need to re-traverse the ledger chain.
/// Matches the reference's implicit `RCLValidatedLedger{ledger}` construction.
pub fn validated_ledger_from_ledger(
    ledger: &::ledger::Ledger,
    journal: &impl ::ledger::LedgerJournal,
) -> consensus::rcl_validation::RclValidatedLedger {
    consensus::rcl_validation::RclValidatedLedger::from_ledger_with_journal(ledger, journal)
}
