//! App-owned bootstrap assembly for the migrated runtime shell.
//!
//! This stays inside the app crate and only assembles the pieces that the app
//! crate can truthfully own today: config loading, `ApplicationRoot` setup,
//! default node-family ownership, optional SHAMap store ownership, and the
//! `MainRuntime` shell.

use crate::state::app_registry::RelayUntrustedPolicy;
use crate::state::manifest::ManifestLimits;
use crate::{
    ApplicationRoot, ApplicationRootOptions, BootstrapOverlayHandoff, DescriptorLimitProvider,
    MainRuntime, PendingReplayStartup, SHAMapStoreComponent, SHAMapStoreComponentRuntime,
    SHAMapStoreHealthRuntime, SHAMapStoreOperatingMode, SHAMapStoreRuntime,
    adjust_descriptor_limit, bootstrap_shamap_store,
};
use basics::base_uint::Uint256;
use basics::basic_config::{BasicConfig, IniFileSections};
use basics::blob::Blob;
use basics::chrono::NetClockTimePoint;
use basics::memory::malloc_trim::{MallocTrimLogger, MallocTrimReport, malloc_trim};
use basics::string_utilities::str_unhex;
use basics::tagged_cache::{CacheClock, MonotonicClock, TaggedCache};
use ledger::{
    Ledger, LedgerConfig, LedgerHeader, LedgerInfoProvider, LedgerJournal, LedgerReplay,
    NullOrderBookDBJournal, NullOrderBookDBRuntime, load_by_hash, load_by_index,
};
use nodestore::{FetchType, ManagerImp, NodeObjectType as NodeStoreObjectType};
use overlay::Overlay;
use overlay::inbound::LedgerDataIngressDisposition;
use protocol::{
    JsonValue, REGISTERED_FEATURES, STLedgerEntry, STParsedJSONObject, STTx, SerialIter,
    Serializer, TxMeta, feature_id,
};
use quaxar_core::{
    DatabaseCon, LEDGER_DB_INIT, LEDGER_DB_NAME, TRANSACTION_DB_INIT, TRANSACTION_DB_NAME,
    build_database_con_setup,
};
use rusqlite::{OptionalExtension, params};
use shamap::family::{
    FullBelowCache, NullFullBelowCache, NullMissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher,
};
use shamap::item::SHAMapItem;
use shamap::mutation::MutableTree;
use shamap::node_object::NodeObject as SHAMapNodeObject;
use shamap::search::NodePathEntry;
use shamap::storage::NodeObjectType as SHAMapNodeObjectType;
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::SHAMapNodeType;
use shamap::tree_node_cache::TreeNodeCache;
use std::fs;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
use xrpl_core::{HashRouter, ServiceRegistry, StartUpType};

/// Match rippled `ApplicationImp::doSweep`: trim only after periodic cache cleanup.
const APPLICATION_SWEEP_MALLOC_TRIM_TAG: &str = "Application::doSweep";
#[derive(Debug, Clone, Copy)]
struct SweepMallocTrimLogger;
impl MallocTrimLogger for SweepMallocTrimLogger {
    fn debug(&self, message: &str) {
        tracing::debug!(target: "app", "{message}");
    }
}
fn trim_after_application_sweep_with(
    trim: impl FnOnce(&str) -> MallocTrimReport,
) -> MallocTrimReport {
    trim(APPLICATION_SWEEP_MALLOC_TRIM_TAG)
}
fn trim_after_application_sweep() -> MallocTrimReport {
    trim_after_application_sweep_with(|tag| malloc_trim(tag, &SweepMallocTrimLogger))
}

/// Sweep rippled's application-owned NodeCache as part of `Application::doSweep`.
fn sweep_temp_node_cache<C>(cache: &TaggedCache<Uint256, Blob, C>)
where
    C: CacheClock,
{
    cache.sweep();
}

/// The cache and lifecycle work performed by one configured `Application::doSweep`.
/// Both the housekeeping timer and deterministic tests use this sequence so new
/// sweep work cannot be added to one without exercising the other.
trait ApplicationSweepActions {
    fn sweep_inbound_ledgers(&self);
    fn sweep_node_family(&self);
    fn sweep_ledger_master(&self);
    fn sweep_transaction_master(&self);
    fn expire_validations(&self);
    fn trim_allocator(&self);
}

fn run_application_sweep<C>(
    temp_node_cache: &TaggedCache<Uint256, Blob, C>,
    actions: &impl ApplicationSweepActions,
) where
    C: CacheClock,
{
    actions.sweep_inbound_ledgers();
    sweep_temp_node_cache(temp_node_cache);
    actions.sweep_node_family();
    actions.sweep_ledger_master();
    actions.sweep_transaction_master();
    actions.expire_validations();
    // Keep allocator purging after every cache/lifecycle sweep, as rippled's
    // ApplicationImp::doSweep does.
    actions.trim_allocator();
}

struct ProductionApplicationSweep<'a> {
    root: &'a ApplicationRoot,
    inbound: &'a crate::ledger::inbound_ledgers::InboundLedgers,
}

impl ApplicationSweepActions for ProductionApplicationSweep<'_> {
    fn sweep_inbound_ledgers(&self) {
        self.inbound.sweep();
    }

    fn sweep_node_family(&self) {
        let before_size = self
            .root
            .shared_tree_cache()
            .map(|cache| cache.size())
            .unwrap_or(0);
        if let Some(node_family) = self.root.node_family() {
            // NodeFamily owns both caches, so its sweep is the only lifecycle
            // path for the shared FullBelow generation and tree-node entries.
            node_family.sweep();
        }
        let after_size = self
            .root
            .shared_tree_cache()
            .map(|cache| cache.size())
            .unwrap_or(0);
        if before_size != after_size {
            tracing::info!(target: "app",
                before_size, after_size,
                freed = before_size.saturating_sub(after_size),
                "TreeNodeCache sweep (matching rippled doSweep)"
            );
        }

        // NodeFamily::sweep() above expires the shared FullBelow cache used by
        // every inbound acquisition.
    }

    fn sweep_ledger_master(&self) {
        // LedgerMaster sweep — matching rippled's doSweep. This expires
        // completed inbound-ledger history and fetch-pack cache entries once
        // their normal cache policy permits it.
        if let Some(ledger_master_runtime) = self.root.ledger_master_runtime() {
            ledger_master_runtime.ledger_master().sweep();
        }
    }

    fn sweep_transaction_master(&self) {
        // TransactionMaster sweep — matching rippled's doSweep which sweeps
        // the MasterTransaction TaggedCache (65,536 entries, 30min TTL).
        // Without this, completed transactions accumulate indefinitely.
        self.root.transaction_master().sweep();
    }

    fn expire_validations(&self) {
        // Application::doSweep expires validation maps on the same configured
        // SweepInterval; without it, historical validation sets never age out.
        self.root.expire_validations();
    }

    fn trim_allocator(&self) {
        let trim = trim_after_application_sweep();
        tracing::debug!(target: "app", event = "application_sweep_allocator_trim",
            supported = trim.supported, trim_result = trim.trim_result,
            rss_delta_kb = trim.delta_kb(), duration_us = trim.duration_us,
            minflt_delta = trim.minflt_delta, majflt_delta = trim.majflt_delta,
            "allocator trim completed after periodic cache sweep");
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppBootstrapOptions {
    pub config_path: PathBuf,
    pub standalone: bool,
    pub start_valid: bool,
    pub elb_support: bool,
    pub io_threads: usize,
    pub job_queue_threads: usize,
    pub debug: bool,
    pub silent: bool,
    pub verbose: bool,
    pub quiet: bool,
    pub quorum: Option<usize>,
    pub newnodeid: bool,
    pub nodeid: Option<String>,
    pub definitions: bool,
    pub start_type: StartUpType,
    pub start_ledger: Option<String>,
    pub trap_tx_hash: Option<Uint256>,
    pub force_ledger_present_range: Option<(u32, u32)>,
    pub vacuum: bool,
    pub import: bool,
    pub rpc_ip: Option<String>,
    pub rpc_port: Option<u16>,
    pub unittest: Option<String>,
    pub unittest_arg: Option<String>,
    pub unittest_log: bool,
    pub unittest_ipv6: bool,
    pub unittest_jobs: Option<usize>,
    pub rpc_parameters: Vec<String>,
}

impl Default for AppBootstrapOptions {
    fn default() -> Self {
        Self {
            config_path: PathBuf::from("quaxar.cfg"),
            standalone: false,
            start_valid: false,
            elb_support: false,
            io_threads: 6,
            job_queue_threads: 0,
            debug: false,
            silent: false,
            verbose: false,
            quiet: false,
            quorum: None,
            newnodeid: false,
            nodeid: None,
            definitions: false,
            start_type: StartUpType::Normal,
            start_ledger: None,
            trap_tx_hash: None,
            force_ledger_present_range: None,
            vacuum: false,
            import: false,
            rpc_ip: None,
            rpc_port: None,
            unittest: None,
            unittest_arg: None,
            unittest_log: false,
            unittest_ipv6: false,
            unittest_jobs: None,
            rpc_parameters: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppBootstrapReport {
    pub config_path: PathBuf,
    pub startup_ledger_mode: StartUpType,
    pub io_threads: usize,
    pub job_queue_threads: usize,
    pub sweep_interval_seconds: u64,
    pub ledger_history: u32,
    pub path_search_old: u32,
    pub path_search: u32,
    pub path_search_fast: u32,
    pub path_search_max: u32,
    pub has_overlay_runtime: bool,
    pub overlay_network_id: Option<u32>,
    pub cluster_node_count: usize,
    pub has_node_family: bool,
    pub has_server_ports_setup: bool,
    pub has_server_runtime: bool,
    pub server_configured_ports: Vec<String>,
    pub deferred_protocols: Vec<String>,
    pub has_resolver_runtime: bool,
    pub has_ledger_runtime: bool,
    pub has_ledger_master_runtime: bool,
    pub has_network_ops_runtime: bool,
    pub has_network_ops_validation_runtime: bool,
    pub has_consensus_runtime: bool,
    pub has_validator_site_runtime: bool,
    pub has_perf_log_runtime: bool,
    pub has_node_store: bool,
    pub node_store_kind: Option<String>,
    pub has_shamap_store_service: bool,
    /// True only while replay startup is waiting for the exact incomplete
    /// parent to finish the normal inbound History acquisition lifecycle.
    pub replay_startup_pending: bool,
    pub fd_required: usize,
}

#[derive(Debug)]
pub struct AppBootstrapRoot {
    pub root: ApplicationRoot,
    pub report: AppBootstrapReport,
}

#[derive(Debug)]
pub struct AppBootstrapRuntime {
    pub runtime: Arc<MainRuntime>,
    pub report: AppBootstrapReport,
    pub sweep_interval_seconds: u64,
}

#[derive(Debug, Default)]
struct BootstrapSHAMapStoreRuntime {
    stopping: AtomicBool,
}

impl SHAMapStoreRuntime for BootstrapSHAMapStoreRuntime {
    fn start_background_work(&mut self) {}

    fn stop_background_work(&mut self) {
        self.stopping.store(true, Ordering::Release);
    }

    fn minimum_sql_seq(&self) -> Option<u32> {
        None
    }
}

impl SHAMapStoreHealthRuntime for BootstrapSHAMapStoreRuntime {
    fn is_stopping(&self) -> bool {
        self.stopping.load(Ordering::Acquire)
    }

    fn operating_mode(&self) -> SHAMapStoreOperatingMode {
        SHAMapStoreOperatingMode::Other
    }

    fn validated_ledger_age(&self) -> Duration {
        Duration::default()
    }
}

impl SHAMapStoreComponentRuntime for BootstrapSHAMapStoreRuntime {}

struct PendingProductionSHAMapStore {
    bootstrap: crate::SHAMapStoreBootstrap,
    backend_factory: Arc<dyn crate::SHAMapStoreRotatingBackendFactory>,
}

struct BootstrapNodeFamilyCacheRuntime {
    node_family: Arc<dyn crate::NodeFamilyRuntime>,
    tree_cache: Arc<TreeNodeCache<MonotonicClock, basics::hardened_hash::HardenedHashBuilder>>,
    full_below: crate::NodeFamilyFullBelowCache,
}

impl crate::SHAMapStoreNodeFamilyCacheRuntime for BootstrapNodeFamilyCacheRuntime {
    fn tree_node_cache_keys(&self) -> Vec<Uint256> {
        self.tree_cache.get_keys()
    }

    fn clear_full_below_cache(&self) {
        self.full_below.clear();
    }

    fn visit_state_map_nodes(
        &self,
        ledger: &Ledger,
        visit: &mut dyn FnMut(
            &basics::memory::intrusive_pointer::SharedIntrusive<shamap::tree_node::SHAMapTreeNode>,
        ) -> bool,
    ) -> Result<(), shamap::traversal::TraversalError> {
        self.node_family.visit_state_map_nodes(ledger, visit)
    }
}

struct BootstrapRotatingNodeStoreRuntime {
    database: Arc<dyn nodestore::DatabaseRotating>,
    ledger_master_runtime: Arc<crate::AppLedgerMasterRuntime>,
    owner_wake: Arc<dyn Fn() + Send + Sync>,
}

impl crate::SHAMapStoreNodeStoreRuntime for BootstrapRotatingNodeStoreRuntime {
    fn fetch_node_object(&self, hash: &Uint256, ledger_seq: u32) -> bool {
        nodestore::Database::fetch_node_object(
            self.database.as_ref(),
            hash,
            ledger_seq,
            FetchType::Synchronous,
            true,
        )
        .is_some()
    }

    fn copy_to_writable_batch(&self, hashes: &[Uint256]) -> Result<usize, String> {
        self.database.copy_to_writable_batch(hashes)
    }

    fn copy_to_writable_batch_detailed(
        &self,
        hashes: &[Uint256],
    ) -> Result<(usize, Vec<Uint256>), String> {
        self.database.copy_to_writable_batch_detailed(hashes)
    }

    fn store_account_nodes(&self, nodes: Vec<(Uint256, basics::blob::Blob)>) -> Result<(), String> {
        self.database.store_account_nodes(nodes)
    }

    fn set_rotation_in_flight(&self, in_flight: bool) {
        self.database.set_rotation_in_flight(in_flight);
        if in_flight {
            // DatabaseRotating advances its generation at the beginning of
            // the exposure window, before the potentially long copy phase.
            // Publish that identity immediately so no operation minted during
            // the copy can carry the retired generation and self-cancel.
            self.ledger_master_runtime.publish_store_rotation(
                nodestore::Database::store_generation(self.database.as_ref()),
            );
            (self.owner_wake)();
        }
    }

    fn rotate_with(&self, new_backend: Box<dyn nodestore::Backend>) -> (String, String) {
        let mut names = None;
        self.database
            .rotate(new_backend, &mut |writable_name, archive_name| {
                names = Some((writable_name.to_owned(), archive_name.to_owned()));
            });
        self.ledger_master_runtime
            .publish_store_rotation(nodestore::Database::store_generation(
                self.database.as_ref(),
            ));
        (self.owner_wake)();
        names.expect("rotating NodeStore callback must publish backend names")
    }
}

#[derive(Clone)]
struct BootstrapLedgerDbProvider {
    relational: Arc<crate::SqliteSHAMapStoreRelational>,
}

#[derive(Debug, Default)]
struct BootstrapLedgerJournal;

impl LedgerJournal for BootstrapLedgerJournal {
    fn info(&self, message: &str) {
        tracing::info!(target: "bootstrap", %message, "durable ledger load");
    }

    fn warn(&self, message: &str) {
        tracing::warn!(target: "bootstrap", %message, "durable ledger load");
    }
}

impl BootstrapLedgerDbProvider {
    fn new(relational: Arc<crate::SqliteSHAMapStoreRelational>) -> Self {
        Self { relational }
    }

    fn query_one(&self, sql: &str, bind: impl rusqlite::Params) -> Option<LedgerHeader> {
        let ledger_db = self.relational.ledger_db();
        let connection = ledger_db.get_session();
        match connection
            .query_row(sql, bind, |row| {
                let close_time_resolution = row.get::<_, u32>(6)?;
                let close_flags = row.get::<_, u32>(7)?;
                Ok(LedgerHeader {
                    hash: parse_sql_hash(row.get::<_, String>(0)?)?,
                    seq: row.get::<_, u32>(1)?,
                    parent_hash: parse_sql_hash(row.get::<_, String>(2)?)?,
                    drops: row.get::<_, u64>(3)?,
                    close_time: row.get::<_, u32>(4)?,
                    parent_close_time: row.get::<_, u32>(5)?,
                    close_time_resolution: u8::try_from(close_time_resolution).map_err(|_| {
                        rusqlite::Error::FromSqlConversionFailure(
                            6,
                            rusqlite::types::Type::Integer,
                            Box::new(std::io::Error::other("invalid close time resolution")),
                        )
                    })?,
                    close_flags: u8::try_from(close_flags).map_err(|_| {
                        rusqlite::Error::FromSqlConversionFailure(
                            7,
                            rusqlite::types::Type::Integer,
                            Box::new(std::io::Error::other("invalid close flags")),
                        )
                    })?,
                    account_hash: parse_sql_hash(row.get::<_, String>(8)?)?,
                    tx_hash: parse_sql_hash(row.get::<_, String>(9)?)?,
                    ..LedgerHeader::default()
                })
            })
            .optional()
        {
            Ok(header) => header,
            Err(error) => {
                tracing::warn!(target: "bootstrap", %error,
                    "durable ledger header query failed");
                None
            }
        }
    }
}

impl LedgerInfoProvider for BootstrapLedgerDbProvider {
    fn get_ledger_info_by_index(&self, ledger_index: u32) -> Option<LedgerHeader> {
        self.query_one(
            "SELECT LedgerHash, LedgerSeq, PrevHash, TotalCoins, ClosingTime, PrevClosingTime, CloseTimeRes, CloseFlags, AccountSetHash, TransSetHash FROM Ledgers WHERE LedgerSeq = ?1 ORDER BY LedgerSeq DESC LIMIT 1",
            params![i64::from(ledger_index)],
        )
    }

    fn get_ledger_info_by_hash(
        &self,
        ledger_hash: basics::sha_map_hash::SHAMapHash,
    ) -> Option<LedgerHeader> {
        self.query_one(
            "SELECT LedgerHash, LedgerSeq, PrevHash, TotalCoins, ClosingTime, PrevClosingTime, CloseTimeRes, CloseFlags, AccountSetHash, TransSetHash FROM Ledgers WHERE LedgerHash = ?1 LIMIT 1",
            params![ledger_hash.as_uint256().to_string()],
        )
    }

    fn get_newest_ledger_info(&self) -> Option<LedgerHeader> {
        self.query_one(
            "SELECT LedgerHash, LedgerSeq, PrevHash, TotalCoins, ClosingTime, PrevClosingTime, CloseTimeRes, CloseFlags, AccountSetHash, TransSetHash FROM Ledgers ORDER BY LedgerSeq DESC LIMIT 1",
            [],
        )
    }
}

#[derive(Clone)]
struct BootstrapNodeStoreFetcher {
    node_store: crate::SHAMapStoreNodeStore,
}

/// Bootstrap adapter for the shared validator-site owner. ApplicationRoot
/// performs list application, trusted-manifest durability, and v1 suppression
/// aware rebroadcasting; this sink only bridges the generic site interface.
struct BootstrapValidatorSiteSink(crate::ApplicationRoot);

impl crate::ValidatorSiteSink for BootstrapValidatorSiteSink {
    fn apply_lists(
        &mut self,
        manifest: &str,
        version: u32,
        blobs: &[crate::ValidatorBlobInfo],
        site_uri: String,
        hash: basics::base_uint::Uint256,
    ) -> crate::PublisherListStats {
        let stats = self
            .0
            .apply_validator_lists(manifest, version, blobs, site_uri, hash);
        synchronize_unl_blocked(&self.0);
        broadcast_validator_list_collection(&self.0, &stats, hash);
        stats
    }

    fn load_lists(&self) -> Vec<String> {
        self.0.validators().load_lists()
    }
}

impl BootstrapNodeStoreFetcher {
    fn new(node_store: crate::SHAMapStoreNodeStore) -> Self {
        Self { node_store }
    }
}

impl SHAMapNodeFetcher for BootstrapNodeStoreFetcher {
    fn fetch_node_object(
        &self,
        hash: basics::sha_map_hash::SHAMapHash,
        ledger_seq: u32,
    ) -> Option<SHAMapNodeObject> {
        let fetched = match &self.node_store {
            crate::SHAMapStoreNodeStore::Single(database) => database.fetch_node_object(
                hash.as_uint256(),
                ledger_seq,
                FetchType::Synchronous,
                false,
            ),
            crate::SHAMapStoreNodeStore::Rotating(database) => database.fetch_node_object(
                hash.as_uint256(),
                ledger_seq,
                FetchType::Synchronous,
                false,
            ),
        }?;

        Some(SHAMapNodeObject::new(
            match fetched.object_type() {
                NodeStoreObjectType::Ledger => SHAMapNodeObjectType::Ledger,
                NodeStoreObjectType::AccountNode => SHAMapNodeObjectType::AccountNode,
                NodeStoreObjectType::TransactionNode => SHAMapNodeObjectType::TransactionNode,
                NodeStoreObjectType::Unknown | NodeStoreObjectType::Dummy => {
                    SHAMapNodeObjectType::Unknown
                }
            },
            fetched.data().to_vec(),
            *fetched.hash(),
        ))
    }
}

pub fn parse_bootstrap_args<I>(args: I) -> Result<AppBootstrapOptions, String>
where
    I: IntoIterator<Item = String>,
{
    let mut options = AppBootstrapOptions::default();
    let mut iter = args.into_iter();
    let _ = iter.next(); // Skip binary name

    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--conf" => {
                let Some(raw_path) = iter.next() else {
                    return Err("--conf requires a file path".to_owned());
                };
                options.config_path = PathBuf::from(raw_path);
            }
            "--debug" => {
                options.debug = true;
            }
            "--help" | "-h" => {
                return Err(usage());
            }
            "--quorum" => {
                let Some(raw_value) = iter.next() else {
                    return Err("--quorum requires a numeric value".to_owned());
                };
                let quorum = raw_value
                    .parse::<usize>()
                    .map_err(|_| format!("invalid --quorum value: {raw_value}"))?;
                if quorum == 0 {
                    return Err("invalid --quorum value: 0".to_owned());
                }
                options.quorum = Some(quorum);
            }
            "--silent" => {
                options.silent = true;
            }
            "--standalone" | "-a" => {
                options.standalone = true;
            }
            "--verbose" | "-v" => {
                options.verbose = true;
            }
            "--quiet" | "-q" => {
                options.quiet = true;
            }
            "--newnodeid" => {
                options.newnodeid = true;
            }
            "--nodeid" => {
                let Some(id) = iter.next() else {
                    return Err("--nodeid requires a value".to_owned());
                };
                options.nodeid = Some(id);
            }
            "--definitions" => {
                options.definitions = true;
            }
            "--force_ledger_present_range" => {
                let Some(range_str) = iter.next() else {
                    return Err(
                        "--force_ledger_present_range requires a value (min,max)".to_owned()
                    );
                };
                let parts: Vec<&str> = range_str.split(',').collect();
                if parts.len() != 2 {
                    return Err(format!(
                        "invalid --force_ledger_present_range: expected min,max got {range_str}"
                    ));
                }
                let min = parts[0].parse::<u32>().map_err(|_| {
                    format!("invalid min in --force_ledger_present_range: {}", parts[0])
                })?;
                let max = parts[1].parse::<u32>().map_err(|_| {
                    format!("invalid max in --force_ledger_present_range: {}", parts[1])
                })?;
                options.force_ledger_present_range = Some((min, max));
            }
            "--version" => {
                options.rpc_parameters.push("version".to_string());
                return Ok(options);
            }
            "--import" => {
                options.import = true;
            }
            "--ledger" => {
                let Some(ledger) = iter.next() else {
                    return Err("--ledger requires a value".to_owned());
                };
                options.start_ledger = Some(ledger);
                if options.start_type != StartUpType::Replay {
                    options.start_type = StartUpType::Load;
                }
            }
            "--ledgerfile" => {
                let Some(ledger) = iter.next() else {
                    return Err("--ledgerfile requires a value".to_owned());
                };
                options.start_ledger = Some(ledger);
                options.start_type = StartUpType::LoadFile;
            }
            "--load" => {
                options.start_type = StartUpType::Load;
            }
            "--net" => {
                options.start_type = StartUpType::Network;
            }
            "--replay" => {
                options.start_type = StartUpType::Replay;
            }
            "--trap_tx_hash" => {
                let Some(hash_str) = iter.next() else {
                    return Err("--trap_tx_hash requires a hex value".to_owned());
                };
                let hash = Uint256::from_hex(&hash_str)
                    .map_err(|_| format!("invalid --trap_tx_hash value: {hash_str}"))?;
                options.trap_tx_hash = Some(hash);
            }
            "--start" => {
                options.start_type = StartUpType::Fresh;
            }
            "--vacuum" => {
                options.vacuum = true;
            }
            "--valid" => {
                options.start_valid = true;
            }
            "--rpc" => {
                // Marker flag
            }
            "--rpc_ip" => {
                let Some(ip) = iter.next() else {
                    return Err("--rpc_ip requires a value".to_owned());
                };
                options.rpc_ip = Some(ip);
            }
            "--rpc_port" => {
                let Some(raw_port) = iter.next() else {
                    return Err("--rpc_port requires a numeric value".to_owned());
                };
                options.rpc_port = Some(
                    raw_port
                        .parse::<u16>()
                        .map_err(|_| format!("invalid --rpc_port value: {raw_port}"))?,
                );
            }
            "--unittest" | "-u" => {
                options.unittest = Some(iter.next().unwrap_or_default());
            }
            "--unittest-arg" => {
                options.unittest_arg = Some(iter.next().unwrap_or_default());
            }
            "--unittest-log" => {
                options.unittest_log = true;
            }
            "--unittest-ipv6" => {
                options.unittest_ipv6 = true;
            }
            "--unittest-jobs" => {
                let Some(raw_value) = iter.next() else {
                    return Err("--unittest-jobs requires a numeric value".to_owned());
                };
                options.unittest_jobs = Some(
                    raw_value
                        .parse::<usize>()
                        .map_err(|_| format!("invalid --unittest-jobs value: {raw_value}"))?,
                );
            }
            "--io-threads" => {
                let Some(raw_value) = iter.next() else {
                    return Err("--io-threads requires a numeric value".to_owned());
                };
                options.io_threads = raw_value
                    .parse::<usize>()
                    .map_err(|_| format!("invalid --io-threads value: {raw_value}"))?;
            }
            "--job-queue-threads" => {
                let Some(raw_value) = iter.next() else {
                    return Err("--job-queue-threads requires a numeric value".to_owned());
                };
                options.job_queue_threads = raw_value
                    .parse::<usize>()
                    .map_err(|_| format!("invalid --job-queue-threads value: {raw_value}"))?;
            }
            other if other.starts_with('-') => {
                return Err(format!("unrecognized argument: {other}"));
            }
            positional => {
                options.rpc_parameters.push(positional.to_string());
            }
        }
    }

    Ok(options)
}

pub fn load_basic_config_file(path: impl AsRef<Path>) -> Result<BasicConfig, String> {
    let path = path.as_ref();
    tracing::info!(target: "bootstrap", config_path = %path.display(), "Loading configuration");
    let contents = fs::read_to_string(path)
        .map_err(|error| format!("failed to read config file {}: {error}", path.display()))?;
    let mut config = parse_basic_config_text(&contents)?;

    // Load [validators_file] if present (mimics C++ Config::loadValidatorFile)
    if config.exists("validators_file") {
        let validators_file = config
            .section("validators_file")
            .legacy()
            .unwrap_or_default();
        if !validators_file.is_empty() {
            let vf_path = if Path::new(&validators_file).is_absolute() {
                PathBuf::from(&validators_file)
            } else {
                path.parent()
                    .unwrap_or(Path::new("."))
                    .join(&validators_file)
            };
            match fs::read_to_string(&vf_path) {
                Ok(vf_contents) => {
                    tracing::info!(target: "bootstrap", path = %vf_path.display(), "Loading validators file");
                    let vf_config = parse_basic_config_text(&vf_contents)?;
                    // Merge validator sections into main config
                    for section_name in
                        ["validator_list_sites", "validator_list_keys", "validators"]
                    {
                        if vf_config.exists(section_name) {
                            let values = vf_config.section(section_name).values().to_vec();
                            if !values.is_empty() {
                                config.section_mut(section_name).append_lines(values);
                            }
                        }
                    }
                }
                Err(e) => {
                    tracing::warn!(target: "bootstrap", path = %vf_path.display(), error = %e, "Failed to load validators file");
                }
            }
        }
    }

    Ok(config)
}

pub fn build_bootstrap_runtime(
    config: &BasicConfig,
    options: &AppBootstrapOptions,
) -> Result<AppBootstrapRuntime, String> {
    let bootstrap = build_bootstrap_root(config, options)?;
    let node_size_profile = crate::NodeSizeResourceProfile::for_node_size(
        bootstrap.root.status_rpc_node_size().as_deref(),
    );
    let sweep_interval_seconds =
        configured_sweep_interval(config, node_size_profile.sweep_interval_seconds)?;
    let runtime = Arc::new(MainRuntime::new(bootstrap.root));
    // - standalone → Full (node operates without network)
    // - start_valid → Full (node starts fully synced)
    // - non-standalone → Connected (node starts connected to network)
    {
        use crate::network::network_ops::NetworkOpsOperatingMode;
        let mode = if options.standalone || options.start_valid {
            NetworkOpsOperatingMode::Full
        } else {
            NetworkOpsOperatingMode::Connected
        };
        runtime
            .root()
            .set_network_ops_operating_mode_with_reason(mode, "startup");
    }
    Ok(AppBootstrapRuntime {
        runtime,
        report: bootstrap.report,
        sweep_interval_seconds,
    })
}

pub fn build_bootstrap_root(
    config: &BasicConfig,
    options: &AppBootstrapOptions,
) -> Result<AppBootstrapRoot, String> {
    let manifest_limits = ManifestLimits::from_config(config)?;
    let configured_node_size = configured_node_size_from_config(config);
    let node_size_profile =
        crate::NodeSizeResourceProfile::for_node_size(configured_node_size.as_deref());
    let mut effective_options = options.clone();
    let fast_load = node_db_fast_load(config);
    if fast_load
        && !matches!(
            effective_options.start_type,
            StartUpType::Replay | StartUpType::LoadFile
        )
    {
        // Matches rippled Main.cpp: fast_load selects Load unless an earlier
        // explicit Replay or LoadFile branch already selected the startup mode.
        effective_options.start_type = StartUpType::Load;
    }
    let options = &effective_options;
    let io_threads = config_legacy_usize(config, "io_workers").unwrap_or(options.io_threads);
    let requested_job_queue_threads =
        config_legacy_usize(config, "workers").unwrap_or(options.job_queue_threads);
    let job_queue_threads = if requested_job_queue_threads != 0 {
        requested_job_queue_threads
    } else {
        default_job_queue_threads(config, options.standalone)
    }
    .max(1);
    let ledger_history = config_legacy_u32(config, "ledger_history").unwrap_or(0);
    // Match rippled Config: [network_quorum] is an exact single unsigned
    // value and is checked against raw legacy [peers_max] (zero/absent = 21),
    // not the derived directional overlay limits.
    let network_quorum = config_single_unsigned(config, "network_quorum")?.unwrap_or(1);
    let raw_peers_max = config_single_unsigned(config, "peers_max")?.unwrap_or(0);
    let effective_peers_max = if raw_peers_max == 0 {
        21
    } else {
        raw_peers_max
    };
    if network_quorum > effective_peers_max {
        return Err(format!(
            "[network_quorum] {network_quorum} exceeds configured [peers_max] {effective_peers_max}"
        ));
    }
    let path_search_old = config_legacy_u32(config, "path_search_old").unwrap_or(2);
    let path_search = config_legacy_u32(config, "path_search").unwrap_or(2);
    let path_search_fast = config_legacy_u32(config, "path_search_fast").unwrap_or(2);
    let path_search_max = config_path_search_max(config);

    let mut root = ApplicationRoot::with_options(ApplicationRootOptions {
        io_threads,
        job_queue_threads,
        start_valid: options.start_valid,
        elb_support: options.elb_support,
        standalone: options.standalone,
        start_type: options.start_type,
        start_ledger: options.start_ledger.clone(),
        import: options.import,
        quorum: options.quorum,
        network_quorum,
        ledger_fetch_depth: ledger_history,
        ..ApplicationRootOptions::default()
    })
    .map_err(|error| error.to_string())?;
    root.configure_manifest_limits(manifest_limits);

    root.set_path_search_levels(path_search_old, path_search, path_search_fast);
    let _ = root.set_path_search_max(path_search_max);
    for (section, is_validation) in [("relay_validations", true), ("relay_proposals", false)] {
        if config.exists(section) {
            let value = config.section(section).legacy().unwrap_or_default();
            let policy = RelayUntrustedPolicy::parse(&value)
                .map_err(|_| format!("invalid value specified in [{section}] section"))?;
            if is_validation {
                root.set_relay_untrusted_validations_policy(policy);
            } else {
                root.set_relay_untrusted_proposals_policy(policy);
            }
        }
    }
    // Configure TxQ for standalone mode (higher min_txn prevents fee escalation).
    if options.standalone {
        root.tx_q().set_standalone(true);
    }
    // Apply [transaction_queue] config overrides.
    let txq_setup = parse_txq_setup(config);
    if config.exists("transaction_queue") {
        root.tx_q().reconfigure_setup(txq_setup);
    }
    let _ = root.attach_default_resolver_runtime();
    // Construct LedgerMaster from the already-resolved node-size policy rather
    // than retaining its generic defaults (medium: 64 ledgers / 180 seconds).
    let ledger_master_runtime = Arc::new(crate::AppLedgerMasterRuntime::new(
        node_size_profile.ledger_master_config(),
    ));
    let _ = root.attach_ledger_master_runtime(ledger_master_runtime);
    let _ = root.attach_default_network_ops_validation_runtime();
    let _ = root.attach_default_network_ops_runtime();
    attach_relational_database_if_configured(&mut root, config, options, ledger_history)?;
    let _ = root
        .attach_server_ports_from_config(config, options.standalone)
        .map_err(|error| error.to_string())?;
    let _ = root.load_peer_reservations()?;
    let _ = root.load_cluster_nodes_from_config(config)?;

    // Standalone mode operates without network peers — skip overlay entirely.
    if !options.standalone {
        let _ =
            root.attach_configured_overlay_runtime(config, Arc::new(BootstrapOverlayHandoff))?;
    }

    // Start built-in SNTP client if [sntp_servers] is configured.  This
    // allows nodes in LXC containers, Docker, or managed VPS environments
    // (where host NTP cannot be configured by the operator) to discipline
    // their clock independently, matching rippled's former [sntp_servers]
    // support.
    if !options.standalone {
        let sntp_servers: Vec<String> = config
            .section("sntp_servers")
            .values()
            .iter()
            .map(|s| s.to_string())
            .filter(|s| !s.is_empty())
            .collect();
        if !sntp_servers.is_empty() {
            tracing::info!(target: "bootstrap",
                count = sntp_servers.len(),
                "Starting built-in SNTP client ([sntp_servers] configured)"
            );
            root.start_sntp_client(sntp_servers);
        }
    }

    // Preserve section presence: ValidatorKeys distinguishes no configured
    // source from a present-but-invalid source. `legacy` also enforces the
    // single-value configuration contract instead of silently ignoring it.
    if config.exists("validation_seed") {
        let seed = config
            .legacy("validation_seed")
            .map_err(|error| format!("invalid [validation_seed] configuration: {error}"))?;
        root.set_validation_seed(seed);
    }
    // Preserve [validator_token] presence even when empty so ValidatorKeys
    // rejects malformed configured tokens rather than treating them as absent.
    if config.exists("validator_token") {
        let token_values = config.section("validator_token").values();
        root.set_validator_token(token_values.to_vec());
        tracing::info!(target: "app", "Validator token configured");
    }

    let _ = root.attach_default_consensus_runtime();

    let pending_shamap_store = bootstrap_shamap_store_if_configured(
        &mut root,
        config,
        options.standalone,
        ledger_history,
        io_threads,
    )?;
    let node_store_kind = pending_shamap_store
        .as_ref()
        .map(|pending| pending.bootstrap.node_store_kind().to_owned());
    let sweep_interval_seconds =
        configured_sweep_interval(config, node_size_profile.sweep_interval_seconds)?;
    root.set_status_rpc_node_size(configured_node_size.clone());
    attach_bootstrap_node_family(&mut root, configured_node_size.as_deref());
    attach_production_shamap_store_runtime(&mut root, pending_shamap_store)?;
    initialize_startup_ledger_state(&root, options, config)?;
    root.bind_default_component_runtimes();

    // Wire up node identity (pubkey_node in server_info) from wallet DB,
    // matching reference Application::setup() -> getNodeIdentity().
    {
        use crate::state::node_identity::load_or_generate_node_identity;
        let identity = load_or_generate_node_identity(&root.wallet_db());
        root.set_node_identity(identity);
    }

    // Restore persisted validator/publisher manifests before ValidatorList
    // resolves configured and live signing keys, matching ApplicationImp
    // startup's ValidatorManifests/PublisherManifests load sequence.
    root.manifest_cache()
        .load_from_wallet(root.wallet_db().as_ref(), "ValidatorManifests")?;
    root.publisher_manifest_cache()
        .load_from_wallet(root.wallet_db().as_ref(), "PublisherManifests")?;

    // Match ApplicationImp::setup: validate one local key source, install the
    // configured validator manifest and any revocations into the same cache
    // used by ValidatorList, then pass the derived signing key to load().
    let validator_keys = crate::validator::validator_keys::ValidatorKeys::from_sources(
        root.config().validation_seed.as_deref(),
        root.config().validator_token.as_deref(),
    );
    if validator_keys.config_invalid() {
        return Err("invalid [validation_seed] or [validator_token] configuration".to_owned());
    }
    if let Some(keys) = validator_keys.keys.as_ref() {
        root.set_validation_public_key(keys.public_key);
    }
    if !validator_keys.manifest.is_empty() {
        let manifest = crate::validator::validator_list::deserialize_manifest_base64_bounded(
            &validator_keys.manifest,
        )
        .ok_or_else(|| "invalid configured validator manifest".to_owned())?;
        if root.manifest_cache().apply_manifest(manifest)
            == crate::state::manifest::ManifestDisposition::Invalid
        {
            return Err("configured validator manifest rejected".to_owned());
        }
    }
    let raw_revocation = config
        .section("validator_key_revocation")
        .values()
        .iter()
        .map(|line| line.trim())
        .collect::<String>();
    if !raw_revocation.is_empty() {
        let revocation =
            crate::validator::validator_list::deserialize_manifest_base64_bounded(&raw_revocation)
                .filter(crate::state::manifest::Manifest::revoked)
                .ok_or_else(|| "invalid [validator_key_revocation] manifest".to_owned())?;
        if root.manifest_cache().apply_manifest(revocation)
            == crate::state::manifest::ManifestDisposition::Invalid
        {
            return Err("validator key revocation rejected".to_owned());
        }
    }

    // Rippled parity: setMaxDisallowedLedger after the local signing key has
    // been configured, so validators reject stale proposal ledgers.
    if root.validation_public_key().is_some()
        && let Some(max_seq) = root
            .relational_database()
            .as_ref()
            .and_then(|db| db.max_ledger_seq())
    {
        root.set_max_disallowed_ledger(max_seq);
    }

    // Wire up validator list publisher keys from config, matching reference
    // Application::setup() → validators->load(...)
    {
        let publisher_keys: Vec<String> = config.section("validator_list_keys").values().to_vec();
        let list_threshold = validator_list_threshold_from_config(config, publisher_keys.len())?;
        tracing::debug!(target: "bootstrap", ?publisher_keys, ?list_threshold,
            "Validator list keys and threshold loaded");
        let config_keys: Vec<String> = config.section("validators").values().to_vec();
        if !root.validators().load(
            root.validation_public_key(),
            &config_keys,
            &publisher_keys,
            list_threshold,
        ) {
            return Err("invalid entry in validator configuration".to_owned());
        }
        // Configured local manifests become durable as soon as their master
        // keys are listed, rather than waiting for shutdown.
        root.persist_manifest_caches()?;
        install_trusted_first_manifest_provider(&root);
        // When using static [validators] (no validator_list_sites), we must
        // explicitly promote key_listings to trusted_master_keys. Without this,
        // validations from peers are dropped as "untrusted".
        if config.section("validator_list_sites").empty() && !config_keys.is_empty() {
            root.validators()
                .update_trusted(&std::collections::HashSet::new(), 0);
        }
    }

    // Wire up validator list sites from config and do initial fetch,
    // matching reference Application::setup() → validatorSites_->start()
    {
        let site_uris: Vec<String> = config.section("validator_list_sites").values().to_vec();
        tracing::debug!(target: "bootstrap", ?site_uris, "Validator list sites loaded");
        let site = root.validator_sites();
        if !site.load(&site_uris) {
            return Err("invalid entry in [validator_list_sites]".to_owned());
        }
        let mut sink = BootstrapValidatorSiteSink(root.clone());
        // With no configured endpoint, rippled starts from usable persisted
        // cache files. On configured-endpoint failure, ValidatorSite performs
        // this same fallback during its owned refresh loop.
        if site_uris.is_empty() {
            let _ = site.load_cached_lists(&sink);
        }
        let transport = crate::ReqwestValidatorSiteTransport;
        site.refresh_due(&mut sink, &transport, std::time::SystemTime::now());
        // Initial trusted manifests must survive a crash before the recurring
        // runtime receives its first later refresh.
        root.persist_manifest_caches()?;
        // Mark validators as trusted after loading the list.
        let validators = root.validators();
        validators.update_trusted(
            &std::collections::HashSet::new(),
            root.current_close_time_seconds(),
        );
        synchronize_unl_blocked(&root);
    }

    let report = AppBootstrapReport {
        config_path: options.config_path.clone(),
        startup_ledger_mode: options.start_type,
        io_threads,
        job_queue_threads,
        sweep_interval_seconds,
        ledger_history,
        path_search_old,
        path_search,
        path_search_fast,
        path_search_max,
        has_overlay_runtime: root.overlay_runtime().is_some(),
        overlay_network_id: root
            .overlay_runtime()
            .and_then(|overlay| overlay.network_id()),
        cluster_node_count: root.shared_cluster().size(),
        has_node_family: root.node_family().is_some(),
        has_server_ports_setup: root.server_ports_setup().is_some(),
        has_server_runtime: root.runtime_bindings().server.is_some(),
        server_configured_ports: root
            .server_ports_setup()
            .map(|setup| setup.ports.iter().map(|port| port.name.clone()).collect())
            .unwrap_or_default(),
        deferred_protocols: root.server_handler().snapshot().deferred_protocols,
        has_resolver_runtime: root.resolver_runtime().is_some(),
        has_ledger_runtime: root.runtime_bindings().ledger.is_some(),
        has_ledger_master_runtime: root.ledger_master_runtime().is_some(),
        has_network_ops_runtime: root.network_ops_runtime().is_some(),
        has_network_ops_validation_runtime: root.network_ops_validation_runtime().is_some(),
        has_consensus_runtime: root.consensus_runtime().is_some(),
        has_validator_site_runtime: root.runtime_bindings().validator_site.is_some(),
        has_perf_log_runtime: root.runtime_bindings().perf_log.is_some(),
        has_node_store: node_store_kind.is_some(),
        node_store_kind,
        has_shamap_store_service: root.shamap_store_service().is_some(),
        replay_startup_pending: root.pending_replay_startup().is_some(),
        fd_required: root.fd_required(),
    };

    Ok(AppBootstrapRoot { root, report })
}

pub fn build_bootstrap_runtime_from_path(
    path: impl AsRef<Path>,
    mut options: AppBootstrapOptions,
) -> Result<AppBootstrapRuntime, String> {
    options.config_path = path.as_ref().to_path_buf();
    let config = load_basic_config_file(&options.config_path)?;
    build_bootstrap_runtime(&config, &options)
}

pub fn build_bootstrap_runtime_from_args<I>(args: I) -> Result<AppBootstrapRuntime, String>
where
    I: IntoIterator<Item = String>,
{
    let options = parse_bootstrap_args(args)?;
    let config_path = options.config_path.clone();
    build_bootstrap_runtime_from_path(config_path, options)
}

pub fn run_from_args<I>(args: I) -> Result<(), String>
where
    I: IntoIterator<Item = String>,
{
    let bootstrap = build_bootstrap_runtime_from_args(args)?;
    run_bootstrap_runtime(bootstrap)
}

pub fn run_bootstrap_runtime(bootstrap: AppBootstrapRuntime) -> Result<(), String> {
    let runtime = Arc::clone(&bootstrap.runtime);
    let standalone = runtime.root().standalone();
    let confidential_crypto_required = protocol::REGISTERED_FEATURES.iter().any(|feature| {
        feature.name == protocol::FEATURE_CONFIDENTIAL_TRANSFER_NAME && feature.supported
    });
    protocol::confidential_transfer::validate_confidential_crypto_startup(
        confidential_crypto_required,
    )?;
    ensure_descriptor_budget(bootstrap.report.fd_required)?;
    runtime.start()?;
    tracing::info!(target: "app", "Node startup complete");

    // For --start mode: `root.on_closed_ledger` (called during genesis
    // ledger load, see `build_bootstrap_root`) already seeded
    // `ApplicationRoot`'s single closed-ledger tracker with the genesis
    // ledger, so consensus can find it as a parent. The first round is
    // started in the event loop once peers are connected (so proposals
    // arrive before the idle timeout closes it).

    // Standalone mode: no overlay, no consensus thread. The node operates in
    // Full mode with the genesis ledger as validated. Ledger advancement is
    // driven exclusively by `ledger_accept` RPC calls.
    if standalone {
        tracing::info!(
            target: "app",
            validated_seq = runtime.root().validated_ledger_seq(),
            "Standalone mode active — no peers, no consensus. Use ledger_accept to advance."
        );

        let stop_requested = Arc::new(AtomicBool::new(false));
        let stop_thread = spawn_shutdown_watcher(Arc::clone(&runtime), Arc::clone(&stop_requested));

        runtime.wait_for_stop();

        stop_requested.store(true, Ordering::Release);
        let _ = stop_thread.join();
        if let Err(error) = runtime.root().persist_manifest_caches() {
            tracing::error!(target: "manifest", %error,
                "failed to persist manifests during standalone shutdown");
        }
        runtime.shutdown();
        return Ok(());
    }

    // Spawn a dedicated consensus event loop for --start mode (private networks).
    //
    // WHY: In normal operation, the catchup loop in main.rs drives consensus by
    // draining proposals/validations from the overlay and ticking the consensus
    // timer. However, when using --start mode (StartUpType::Fresh), the node
    // boots directly into bootstrap without entering the catchup loop. Without
    // this thread, proposals and validations from peers are never consumed and
    // the consensus timer never fires, so the network stalls after genesis.
    //
    // This thread replicates only the consensus-driving subset of the catchup
    // loop: proposal processing, validation processing, map-complete handling,
    // and timer ticks. It does NOT do ledger acquisition or inbound ledger
    // processing — those are unnecessary when starting fresh.
    let consensus_stop = Arc::new(AtomicBool::new(false));

    // Spawn JobQueue worker threads (matches rippled's JobQueue thread pool).
    // Without these, jobs added via add_job() (e.g. RPC-submitted transactions
    // routed through submit_transaction_to_network_ops) sit in the queue
    // forever and never reach process_transaction, so they never enter the
    // open ledger's transaction set or get included in consensus.
    {
        let jq_template = runtime.root().job_queue();
        let worker_count = jq_template.worker_thread_count().max(1);
        for i in 0..worker_count {
            let jq = jq_template.clone();
            std::thread::Builder::new()
                .name(format!("jobqueue-worker-{i}"))
                .spawn(move || {
                    jq.run_worker_loop();
                })
                .expect("failed to spawn jobqueue worker thread");
        }
    }
    let consensus_thread = if bootstrap.report.has_overlay_runtime {
        // Unified consensus path for all startup modes (mirrors rippled's single
        // Application::run() path). The strand drives consensus from whatever the
        // current closed ledger is, regardless of how it was obtained.
        //
        // need_network_ledger control (matching rippled):
        //   - Network mode: set true in initialize_startup_ledger_state.
        //     The node still starts consensus immediately (rippled does too),
        //     but mode promotion to TRACKING is blocked until a network ledger
        //     is acquired and accepted.
        //   - All other modes: stays false unless explicitly set.
        //
        // NOTE: rippled always calls beginConsensus() regardless of
        // needNetworkLedger. The flag only gates mode promotion and tx
        // submission — NOT consensus timer ticks or round starts.
        let stop_flag = Arc::clone(&consensus_stop);
        let rt = Arc::clone(&runtime);
        let sweep_interval_seconds = bootstrap.sweep_interval_seconds;
        Some(
            std::thread::Builder::new()
                .name("start-mode-consensus".into())
                .spawn(move || {
                    run_start_mode_consensus_loop(
                        rt.clone(),
                        stop_flag.clone(),
                        bootstrap.report.ledger_history,
                        sweep_interval_seconds,
                    );
                })
                .expect("failed to spawn start-mode-consensus thread"),
        )
    } else {
        None
    };

    let stop_requested = Arc::new(AtomicBool::new(false));
    let stop_thread = spawn_shutdown_watcher(Arc::clone(&runtime), Arc::clone(&stop_requested));

    runtime.wait_for_stop();

    // Quiesce bootstrap-owned consensus/acquisition work before managed
    // shutdown reaches NodeStore. MainRuntime::run() cannot do this itself
    // because these handles are owned only by this bootstrap path.
    consensus_stop.store(true, Ordering::Release);
    if let Some(handle) = consensus_thread {
        let _ = handle.join();
    }

    stop_requested.store(true, Ordering::Release);
    let _ = stop_thread.join();
    if let Err(error) = runtime.root().persist_manifest_caches() {
        tracing::error!(target: "manifest", %error,
            "failed to persist manifests after consensus shutdown");
    }
    runtime.shutdown();
    Ok(())
}

/// Overlay service loop for --start mode private networks.
///
/// Consensus is delegated to `NetworkOpsStrand` which owns the runner and
/// drives proposals, timer ticks, accept, and mode promotion on a dedicated
/// thread.  This loop handles the remaining overlay duties: serving
/// GetLedger requests, draining completed ledger acquisitions, processing
/// fetch packs, ticking inbound transactions, and draining validator lists.
const CANDIDATE_ACQUIRE_TICK: Duration = Duration::from_millis(250);

fn ledger_data_sequence_is_admissible(
    packet_type: i32,
    ledger_seq: u32,
    valid_ledger_seq: Option<u32>,
    validated_age: Duration,
) -> bool {
    // Matches PeerImp::onMessage(TMLedgerData): candidate transaction sets
    // never carry a ledger sequence. Ordinary data is rejected only while the
    // local validated ledger is fresh, avoiding a permanent future-sequence
    // gate during initial catchup.
    if packet_type == 3 {
        return ledger_seq == 0;
    }
    validated_age > Duration::from_secs(10)
        || valid_ledger_seq.is_none_or(|valid_seq| ledger_seq <= valid_seq.saturating_add(10))
}

/// PeerImp rejects empty and oversized TMLedgerData node vectors before
/// relaying or scheduling them. Candidate payloads need this explicit gate so
/// an empty transaction-set reply incurs kFeeInvalidData rather than entering
/// InboundTransactions as a no-op.
fn ledger_data_nodes_are_admissible(node_count: usize) -> bool {
    (1..=HARD_MAX_REPLY_NODES).contains(&node_count)
}

/// Result of the bootstrap-owned, non-candidate `TMLedgerData` handoff.
/// `charge_unsolicited` is kept separate from the transport disposition so a
/// deferred frame stays exclusively transport-owned and never reaches the
/// peer-resource path before Worker 2 has admitted it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BootstrapLedgerDataRouting {
    disposition: LedgerDataIngressDisposition,
    charge_unsolicited: bool,
}

/// Route one parsed Base/transaction/state reply through the same live
/// bootstrap admission branch installed below. This preserves Worker 2's
/// ownership boundary: an admitted lease is consumed exactly once by actor
/// routing, while `Deferred` creates no actor route or lease ownership.
fn route_bootstrap_ledger_data(
    inbound: &Arc<crate::ledger::inbound_ledgers::InboundLedgers>,
    hash: Uint256,
    peer_id: overlay::PeerId,
    message: &overlay::TmLedgerData,
) -> BootstrapLedgerDataRouting {
    let packet_type = match message.r#type {
        0 => ledger::InboundLedgerDataType::Base,
        1 => ledger::InboundLedgerDataType::TransactionNode,
        2 => ledger::InboundLedgerDataType::StateNode,
        _ => unreachable!("bootstrap ledger-data helper only accepts non-candidate types"),
    };
    let mut nodes = Vec::with_capacity(message.nodes.len());
    for (packet_index, node) in message.nodes.iter().enumerate() {
        let Some(node) = crate::ledger::inbound_ledgers::wire_ledger_node::decode_wire_ledger_node(
            node,
            packet_type,
            packet_index,
        ) else {
            return BootstrapLedgerDataRouting {
                disposition: LedgerDataIngressDisposition::Delivered,
                charge_unsolicited: true,
            };
        };
        nodes.push(node);
    }
    inbound.note_wire_ledger_data(nodes.len());
    let packet = ledger::InboundLedgerPacket::new(packet_type, nodes);
    let stale_packet =
        (packet.packet_type == ledger::InboundLedgerDataType::StateNode).then(|| packet.clone());

    // An admission lease is the only authority to enqueue actor-owned work.
    // On Deferred, this function returns before route/stale/charge handling;
    // the overlay transport retains exactly its decoded frame for retry.
    let routed = match inbound.reserve_response_admission(&hash, &packet) {
        crate::ledger::inbound_ledgers::LedgerDataAdmission::Admitted(lease) => inbound
            .route_admitted_response_with_seq(
                &hash,
                lease,
                peer_id as u64,
                Some(message.ledger_seq),
                packet,
            ),
        crate::ledger::inbound_ledgers::LedgerDataAdmission::Deferred => {
            return BootstrapLedgerDataRouting {
                disposition: LedgerDataIngressDisposition::Deferred,
                charge_unsolicited: false,
            };
        }
        crate::ledger::inbound_ledgers::LedgerDataAdmission::Unmatched => {
            crate::ledger::inbound_ledgers::LedgerDataRouteDisposition::Unmatched
        }
        crate::ledger::inbound_ledgers::LedgerDataAdmission::Terminal => {
            crate::ledger::inbound_ledgers::LedgerDataRouteDisposition::Terminal
        }
    };
    if routed == crate::ledger::inbound_ledgers::LedgerDataRouteDisposition::Accepted {
        return BootstrapLedgerDataRouting {
            disposition: LedgerDataIngressDisposition::Delivered,
            charge_unsolicited: false,
        };
    }
    if routed.may_stash_as_stale()
        && let Some(packet) = stale_packet
    {
        // `InboundLedgersImp::gotStaleData` remains the terminal treatment for
        // a valid untracked state-node reply. Base/transaction replies fall
        // through to the source-equivalent useless-data peer charge below.
        let stored = inbound.stash_stale_packet(&packet);
        inbound.note_stale_packet_result(stored);
        return BootstrapLedgerDataRouting {
            disposition: LedgerDataIngressDisposition::Delivered,
            charge_unsolicited: false,
        };
    }
    BootstrapLedgerDataRouting {
        disposition: LedgerDataIngressDisposition::Delivered,
        charge_unsolicited: routed
            != crate::ledger::inbound_ledgers::LedgerDataRouteDisposition::AdmissionLeaseInvalid,
    }
}

/// Mirrors `InboundTransactionsImp::gotData`: candidate-set data is charged by
/// its delivery outcome, rather than silently discarding an unknown or bad set.
fn candidate_ledger_data_charge(
    status: &ledger::InboundTransactionsDataStatus,
) -> Option<(resource::Charge, &'static str)> {
    match status {
        ledger::InboundTransactionsDataStatus::NoAcquire => {
            Some(((*resource::FEE_USELESS_DATA).clone(), "ledger_data"))
        }
        ledger::InboundTransactionsDataStatus::MissingNodeId => {
            Some(((*resource::FEE_MALFORMED_REQUEST).clone(), "ledger_data"))
        }
        ledger::InboundTransactionsDataStatus::InvalidNodeId => {
            Some(((*resource::FEE_INVALID_DATA).clone(), "ledger_data"))
        }
        ledger::InboundTransactionsDataStatus::Applied(stats) if !stats.is_useful() => Some((
            (*resource::FEE_USELESS_DATA).clone(),
            "ledger_data not useful",
        )),
        ledger::InboundTransactionsDataStatus::Applied(_) => None,
    }
}

fn process_candidate_ledger_data(
    root: &crate::ApplicationRoot,
    overlay: &Arc<overlay::OverlayImpl>,
    peer_id: overlay::PeerId,
    hash: Uint256,
    message: overlay::TmLedgerData,
) {
    let peer = overlay.find_peer_by_short_id(peer_id);
    let mut guard = root
        .inbound_transactions()
        .lock()
        .expect("inbound_transactions mutex");
    let status = guard.got_data(hash, peer.clone(), &message);
    if let Some((fee, context)) = candidate_ledger_data_charge(&status)
        && let Some(peer) = peer
    {
        peer.charge(fee, context.to_owned());
    }
    if let Some(acquire) = guard.acquire(hash)
        && acquire.is_complete()
    {
        let set = Arc::new(acquire.map().clone());
        guard.give_set(hash, set, true);
    }
}

/// Every `PeerImp::getLedger` selector resolves to a ledger before this single
/// retention gate is applied. Keep hash, sequence, and closed selectors on the
/// same floor rather than letting hash-only requests bypass history policy.
fn sequence_is_fetchable_at_floor(sequence: u32, earliest_fetch: u32) -> bool {
    sequence >= earliest_fetch
}

fn run_start_mode_consensus_loop(
    runtime: Arc<MainRuntime>,
    stop: Arc<AtomicBool>,
    configured_ledger_history: u32,
    configured_sweep_interval_seconds: u64,
) {
    use crate::network::network_ops_strand::{NetworkOpsStrand, NetworkOpsStrandDeps};

    tracing::info!(target: "consensus", "Overlay service loop starting (consensus delegated to NetworkOpsStrand)");

    let consensus_rt = match runtime.root().consensus_runtime() {
        Some(rt) => rt,
        None => {
            tracing::error!(target: "consensus", "No consensus runtime available, exiting");
            return;
        }
    };

    // Consensus event channel for validations and ledger promotions
    let (event_tx, event_rx) = crate::consensus::driver::consensus_event_channel();
    let (shared_completed_tx, shared_completed_rx) = std::sync::mpsc::sync_channel::<
        crate::ledger::inbound_ledgers::CompletedInboundLedger,
    >(1_024);

    let lm_rt_for_shared_inbound = runtime.root().ledger_master_runtime();
    let mut worker_handles = Vec::<std::thread::JoinHandle<()>>::new();
    // Bootstrap installs the one NodeFamily before this loop. Inbound SHAMap
    // acquisition must use its exact tree and full-below caches; creating a
    // fallback cache would split traversal generation/lifecycle ownership.
    let Some(app_tree_cache) = runtime.root().shared_tree_cache_arc().map(Arc::clone) else {
        tracing::error!(target: "consensus", "NodeFamily tree cache missing before consensus loop");
        return;
    };
    let Some(node_family_full_below_cache) = runtime.root().node_family_full_below_cache() else {
        tracing::error!(target: "consensus", "NodeFamily FullBelow cache missing before consensus loop");
        return;
    };

    let shared_inbound = match lm_rt_for_shared_inbound
        .as_ref()
        .and_then(|lm_rt| lm_rt.inbound_ledgers.lock().ok()?.clone())
    {
        Some(inbound) => {
            if !Arc::ptr_eq(inbound.full_below_cache(), &node_family_full_below_cache) {
                tracing::error!(target: "consensus", "existing InboundLedgers does not use the NodeFamily FullBelow cache");
                return;
            }
            inbound
        }
        None => Arc::new(
            crate::ledger::inbound_ledgers::InboundLedgers::new_with_budget(
                Arc::clone(&app_tree_cache),
                Arc::clone(&node_family_full_below_cache),
                lm_rt_for_shared_inbound
                    .as_ref()
                    .map(|runtime| runtime.ledger_master().fetch_pack_cache_arc())
                    .unwrap_or_else(|| {
                        Arc::new(ledger::FetchPackCache::new(
                            65_536,
                            time::Duration::seconds(45),
                            basics::tagged_cache::MonotonicClock::default(),
                        ))
                    }),
                shared_completed_tx.clone(),
                runtime.root().network_ops_state().need_network_ledger_arc(),
                crate::NodeSizeResourceProfile::for_node_size(
                    runtime.root().status_rpc_node_size().as_deref(),
                )
                .acquisition_budget(),
            ),
        ),
    };

    // Tree and FullBelow cache ownership was established by NodeFamily before
    // this loop. Do not attach registry-owned aliases on ApplicationRoot.

    if let Some(lm_rt) = lm_rt_for_shared_inbound.as_ref() {
        lm_rt.install_inbound_ledgers(Arc::clone(&shared_inbound));
    }

    // Match rippled InboundLedger::done: a structurally complete Consensus or
    // Generic ledger enters LedgerHistory before its queued AcqDone-equivalent
    // work. The callback is intentionally installed before acquisitions begin;
    // History material follows its separately validated persistence path.
    if let Some(lm_rt) = lm_rt_for_shared_inbound.as_ref() {
        let ledger_master = lm_rt.ledger_master();
        let root = runtime.root().clone();
        shared_inbound.set_completed_ledger_store(Arc::new(move |ledger| {
            // Publish one normalized ledger instance to both early exact-hash
            // consumers. A fast next validation can otherwise supersede the
            // only waiter before this completion reaches the validation trie.
            let ledger = root.ledger_with_node_fetcher(ledger);
            ledger_master
                .ledger_history()
                .insert(Arc::clone(&ledger), false);
            root.validations().register_ledger(&ledger);
        }));
        let root = runtime.root().clone();
        shared_inbound.set_completed_ledger_revoker(Arc::new(move |identity| {
            root.revoke_provisional_inbound_ledger(identity);
        }));
        let root = runtime.root().clone();
        shared_inbound.set_publication_advance_notifier(Arc::new(move || {
            root.request_publication_advance();
        }));
    }

    // Attach the synchronous SHAMap node store before acquisitions begin.
    if let Some(ns) = runtime.root().node_store().as_ref() {
        shared_inbound.set_node_store(ns.clone());
    }
    if let Some(overlay_rt) = runtime.root().overlay_runtime() {
        {
            let mut guard = runtime
                .root()
                .inbound_transactions()
                .lock()
                .expect("inbound_transactions mutex");
            guard.set_peer_set_builder(Arc::new(overlay::OverlayPeerSetBuilder::new(
                overlay_rt.overlay(),
            )));
        }
        if let Ok(mut replayer) = runtime.root().get_ledger_replayer().lock() {
            replayer.set_peer_set_builder(Arc::new(overlay::OverlayPeerSetBuilder::new(
                overlay_rt.overlay(),
            )));
        } else {
            tracing::error!(target: "ledger", "ledger replayer lock poisoned; replay peer set remains unavailable");
        }
        shared_inbound.set_overlay_rt(overlay_rt);
    }

    // M4.2-C3: install the coordinator as the single session lifecycle owner
    // before any acquisition begins. The coordinator publishes the service
    // phase into the same SharedNetworkOpsState every other component reads,
    // and it never reads a mode back. From this point `acquire` delegates to
    // coordinator sessions and returns None for new starts, exactly like
    // rippled `InboundLedgers::acquire`.
    shared_inbound.set_phase_mode_owner(runtime.root().network_ops_mode_owner());
    if shared_inbound.install_coordinator() {
        tracing::info!(
            target: "inbound_ledger",
            "coordinator installed as the single acquisition session lifecycle owner"
        );
        // M6-D: seed the coordinator's initial phase from the bootstrap startup
        // intent so it alone owns the mode from install (the legacy startup
        // write in `build_bootstrap_runtime` remains only as the pre-install
        // seed and the rollback path). Quaxar preserves its legacy startup
        // mode seed: networked -> Connected, `start_valid` -> Full from the
        // hydrated LCL. rippled seeds `DISCONNECTED`/`FULL` in the NetworkOPs
        // constructor (`rippled/src/xrpld/app/misc/NetworkOPs.cpp:318`).
        shared_inbound.coordinator_startup(startup_coordinator_phase(runtime.root()));
    } else {
        tracing::warn!(
            target: "inbound_ledger",
            "coordinator install deferred: NodeStore or phase state unavailable; legacy acquisition remains the lifecycle owner"
        );
    }

    // Spawn consensus event loop (validation/ledger promotion)
    let event_loop_app = runtime.root().clone();
    let event_loop_stop = Arc::clone(&stop);
    worker_handles.push(crate::consensus::driver::spawn_event_loop(
        event_loop_app,
        Arc::clone(&shared_inbound),
        event_rx,
        event_loop_stop,
    ));

    // Validation forwarding thread
    {
        let (val_notify_tx, val_notify_rx) = std::sync::mpsc::sync_channel::<()>(1);
        if let Some(overlay_rt) = runtime.root().overlay_runtime() {
            overlay_rt
                .overlay()
                .queued_inbound()
                .set_validation_notify(val_notify_tx);
        }
        let fwd_stop = Arc::clone(&stop);
        let fwd_runtime = Arc::clone(&runtime);
        let fwd_event_tx = event_tx.clone();
        if let Some(overlay_rt) = runtime.root().overlay_runtime() {
            let direct_event_tx = event_tx.clone();
            let validation_root = runtime.root().clone();
            let validation_overlay = overlay_rt.overlay();
            overlay_rt
                .overlay()
                .queued_inbound()
                .set_validation_router(Box::new(move |mut queued| {
                    // Match PeerImp::onMessage(TMValidation): parse only far
                    // enough to establish time and trust, then apply the
                    // drop_untrusted policy before source retention or crypto.
                    let mut serial = protocol::SerialIter::new(&queued.message.validation);
                    let mut validation = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        protocol::STValidation::from_serial_iter_default_node_id(&mut serial, false)
                    }))
                    .ok()
                    .and_then(Result::ok);
                    let Some(ref mut parsed_validation) = validation else {
                        return;
                    };
                    let now = validation_root.shared_time_keeper().close_time();
                    parsed_validation.set_seen(now.as_seconds());
                    let current = {
                        let validations = validation_root
                            .validations()
                            .validations()
                            .lock()
                            .expect("shared app validations mutex must not be poisoned");
                        consensus::rcl_support::is_current(
                            validations.parms(),
                            now,
                            NetClockTimePoint::from(parsed_validation.get_sign_time()),
                            NetClockTimePoint::from(parsed_validation.get_seen_time()),
                        )
                    };
                    if !current {
                        return;
                    }
                    let signer = *parsed_validation.get_signer_public();
                    let trusted = validation_root.validators().trusted(signer);
                    if !trusted
                        && validation_root
                            .relay_untrusted_validations_policy()
                            .should_drop()
                    {
                        return;
                    }
                    if !validation_overlay.admit_validation_source(
                        queued.suppression,
                        signer,
                        queued.peer_id,
                    ) {
                        return;
                    }
                    if !trusted
                        && (validation_overlay.peer_is_diverged(queued.peer_id)
                            || validation_root.load_fee_track_loaded_local())
                    {
                        return;
                    }
                    let job_type = if trusted {
                        crate::job::job_types::JobType::JtValidationT
                    } else {
                        crate::job::job_types::JobType::JtValidationUt
                    };
                    let event_tx = direct_event_tx.clone();
                    queued.validation = validation;
                    if !validation_root.job_queue().add_job(
                        job_type,
                        "checkValidation",
                        move || {
                            // The event-loop parser performs the signature
                            // check after scheduling, matching checkValidation.
                            let _ = event_tx
                                .send(crate::consensus::driver::ConsensusEvent::Validation(
                                    Box::new(queued),
                                ));
                        },
                    ) {
                        tracing::debug!(target: "consensus", "validation job rejected during shutdown");
                    }
                }));
        }
        worker_handles.push(
            std::thread::Builder::new()
                .name("validation-forwarder".into())
                .spawn(move || {
                    loop {
                        match val_notify_rx.recv_timeout(Duration::from_millis(25)) {
                            Ok(()) => {}
                            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                                if fwd_stop.load(Ordering::Acquire) {
                                    break;
                                }
                                continue;
                            }
                            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => break,
                        }
                        if fwd_stop.load(Ordering::Acquire) {
                            break;
                        }
                        let root = fwd_runtime.root();
                        let Some(overlay_rt) = root.overlay_runtime() else {
                            continue;
                        };
                        let validations = overlay_rt.overlay().take_validations();
                        for queued in validations {
                            match fwd_event_tx.send(
                                crate::consensus::driver::ConsensusEvent::Validation(Box::new(
                                    queued,
                                )),
                            ) {
                                Ok(()) => {}
                                Err(_) => return,
                            }
                        }
                    }
                })
                .expect("spawn validation-forwarder thread"),
        );
    }

    // Transaction relay router. PeerImp schedules `RcvCheckTx` on the JobQueue;
    // the worker stages the transaction and NetworkOPs schedules `JtBatch`.
    if let Some(overlay_rt) = runtime.root().overlay_runtime() {
        let router_root = runtime.root().clone();
        let job_queue = router_root.job_queue().clone();
        overlay_rt
            .overlay()
            .queued_inbound()
            .set_transaction_router(Box::new(move |peer_id, message| {
                // Mirror PeerImp::handleTransaction: record the inbound
                // source and reject a recently processed relay before it
                // consumes a JtTransaction worker. The source record also
                // prevents `should_relay` from echoing the transaction back
                // to this peer after it enters the local open ledger.
                let Some(network_ops_runtime) = router_root.network_ops_runtime() else {
                    return;
                };
                if !should_schedule_relayed_transaction(
                    network_ops_runtime.hash_router().as_ref(),
                    message.id,
                    peer_id,
                ) {
                    return;
                }

                let root = router_root.clone();
                let queue = job_queue.clone();
                let inbound = message.message;
                let raw_transaction = inbound.raw_transaction;
                let relay_metadata = crate::tx_queue::transaction::TransactionRelayMetadata::new(
                    inbound.status,
                    inbound.receive_timestamp,
                    inbound.deferred,
                );
                let _ = queue.add_job(
                    crate::job::job_types::JobType::JtTransaction,
                    "RcvCheckTx",
                    move || {
                        let mut serial = protocol::SerialIter::new(&raw_transaction);
                        let st_tx =
                            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                protocol::STTx::from_serial_iter(&mut serial)
                            })) {
                                Ok(tx) => tx,
                                Err(_) => return,
                            };
                        let st_tx = Arc::new(st_tx);
                        let mut transaction: crate::SharedTransaction =
                            Arc::new(std::sync::Mutex::new(
                                crate::tx_queue::transaction::Transaction::new_with_relay_metadata(
                                    Arc::clone(&st_tx),
                                    relay_metadata,
                                ),
                            ));
                        if let Some(network_ops_runtime) = root.network_ops_runtime() {
                            let batch_root = root.clone();
                            let _ = network_ops_runtime.process_transaction(
                                &mut transaction,
                                false,
                                false,
                                false,
                                || batch_root.enqueue_network_ops_transaction_batch(),
                                || {},
                            );
                        }
                    },
                );
            }));
    }

    // Replay delta router. This is the live bridge for the parity-flow edge
    // `peer replay response -> LedgerReplayer::got_replay_delta`; malformed
    // payloads are charged exactly where rippled rejects them in PeerImp.
    if let Some(overlay_rt) = runtime.root().overlay_runtime() {
        let router_root = runtime.root().clone();
        let router_overlay = overlay_rt.overlay();
        overlay_rt
            .overlay()
            .queued_inbound()
            .set_replay_delta_response_router(Box::new(move |peer_id, response| {
                if !router_root.on_replay_delta_response(&response)
                    && let Some(peer) = router_overlay.find_peer_by_short_id(peer_id)
                {
                    peer.charge(
                        (*resource::FEE_INVALID_DATA).clone(),
                        "replay_delta_response".to_owned(),
                    );
                }
            }));
    }

    // Ledger-replay request/response routing. These are the peer-facing
    // counterparts of LedgerReplayMsgHandler.cpp's four message methods.
    if let Some(overlay_rt) = runtime.root().overlay_runtime() {
        let overlay = overlay_rt.overlay();
        let inbound = overlay.queued_inbound();
        let request_root = runtime.root().clone();
        let request_overlay = Arc::clone(&overlay);
        inbound.set_proof_path_request_router(Box::new(move |peer_id, request| {
            let response = request_root.proof_path_response_for(&request);
            if let Some(peer) = request_overlay.find_peer_by_short_id(peer_id) {
                peer.send(overlay::Message::new(
                    overlay::ProtocolMessage::new(overlay::ProtocolPayload::ProofPathResponse(
                        response,
                    )),
                    None,
                ));
            }
        }));

        let proof_root = runtime.root().clone();
        let proof_overlay = Arc::clone(&overlay);
        inbound.set_proof_path_response_router(Box::new(move |peer_id, response| {
            if !proof_root.on_proof_path_response(&response)
                && let Some(peer) = proof_overlay.find_peer_by_short_id(peer_id)
            {
                peer.charge(
                    (*resource::FEE_INVALID_DATA).clone(),
                    "proof_path_response".to_owned(),
                );
            }
        }));

        let delta_root = runtime.root().clone();
        let delta_overlay = Arc::clone(&overlay);
        inbound.set_replay_delta_request_router(Box::new(move |peer_id, request| {
            let response = delta_root.replay_delta_response_for(&request);
            if let Some(peer) = delta_overlay.find_peer_by_short_id(peer_id) {
                peer.send(overlay::Message::new(
                    overlay::ProtocolMessage::new(overlay::ProtocolPayload::ReplayDeltaResponse(
                        response,
                    )),
                    None,
                ));
            }
        }));
    }

    // LedgerData router
    if let Some(overlay_rt) = runtime.root().overlay_runtime() {
        let router_root = runtime.root().clone();
        let router_overlay = overlay_rt.overlay();
        let router_shared_inbound = Arc::clone(&shared_inbound);
        overlay_rt
            .overlay()
            .queued_inbound()
            .set_ledger_data_router(Box::new(move |peer_id, message| {
                use overlay::Overlay;

                if !ledger_data_sequence_is_admissible(
                    message.r#type,
                    message.ledger_seq,
                    router_root.validated_ledger_seq(),
                    router_root.validated_ledger_age(),
                ) {
                    router_shared_inbound.note_wire_ledger_data_invalid_hash();
                    if let Some(peer) = router_overlay.find_peer_by_short_id(peer_id) {
                        peer.charge(
                            (*resource::FEE_INVALID_DATA).clone(),
                            "TMLedgerData invalid ledger sequence".to_owned(),
                        );
                    }
                    return overlay::inbound::LedgerDataIngressDisposition::Delivered;
                }

                // PeerImp validates the node vector before cookie relaying.
                // In particular, an empty candidate payload is invalid data,
                // not a harmless incomplete response.
                if !ledger_data_nodes_are_admissible(message.nodes.len()) {
                    router_shared_inbound.note_wire_ledger_data_invalid_hash();
                    if let Some(peer) = router_overlay.find_peer_by_short_id(peer_id) {
                        peer.charge(
                            (*resource::FEE_INVALID_DATA).clone(),
                            "TMLedgerData invalid node count".to_owned(),
                        );
                    }
                    return LedgerDataIngressDisposition::Delivered;
                }

                // Request-cookie relay (matching rippled PeerImp::onMessage TMLedgerData)
                if let Some(cookie) = message.request_cookie {
                    router_shared_inbound.note_wire_ledger_data_relayed();
                    // Forward to the peer that originally requested this data
                    if let Some(requesting_peer) = router_overlay.find_peer_by_short_id(cookie) {
                        let mut fwd = message.clone();
                        fwd.request_cookie = None; // Clear cookie on relay
                        let relay_msg = overlay::ProtocolMessage::new(
                            overlay::ProtocolPayload::LedgerData(fwd),
                        );
                        requesting_peer.send(overlay::Message::new(relay_msg, None));
                    }
                    return LedgerDataIngressDisposition::Delivered; // Don't process relayed responses locally
                }

                let Some(hash) = Uint256::from_slice(&message.ledger_hash) else {
                    router_shared_inbound.note_wire_ledger_data_invalid_hash();
                    return LedgerDataIngressDisposition::Delivered;
                };
                match message.r#type {
                    3 => {
                        // PeerImp::onMessage(TMLedgerData) moves candidate-set
                        // processing to JtTxnData. Keep the peer callback
                        // bounded: `got_data` can advance a SHAMap acquisition.
                        let candidate_root = router_root.clone();
                        let candidate_overlay = router_overlay.clone();
                        let queued_message = message;
                        if !router_root.job_queue().add_job(
                            crate::job::job_types::JobType::JtTxnData,
                            "RcvPeerData",
                            move || {
                                process_candidate_ledger_data(
                                    &candidate_root,
                                    &candidate_overlay,
                                    peer_id,
                                    hash,
                                    queued_message,
                                );
                            },
                        ) {
                            tracing::debug!(target: "consensus", peer_id,
                                "candidate ledger-data job rejected during shutdown");
                        }
                    }
                    0..=2 => {
                        // M4.2-C3: coordinator-owned sessions admit and route
                        // through the coordinator first. The coordinator
                        // enforces the bounded packet/byte budget and enqueues
                        // an owned PacketAdmitted event; an admitted frame is
                        // never routed twice. `Unmatched` (no coordinator
                        // route) falls through to the legacy actor admission
                        // path so base/transaction unmatched replies keep
                        // their source-equivalent useless-data charge.
                        if router_shared_inbound.coordinator_installed() {
                            use crate::ledger::inbound_ledgers::CoordinatorLedgerDataDisposition;
                            let disposition = router_shared_inbound
                                .coordinator_route_ledger_data(peer_id, &message);
                            match disposition {
                                // No coordinator route: fall through only to
                                // the rippled-equivalent unmatched treatment.
                                // In coordinator mode the registry returns
                                // `Unmatched` before consulting any legacy
                                // actor, so state nodes may seed fetch-pack
                                // while base/transaction replies retain their
                                // source-equivalent useless-data charge.
                                CoordinatorLedgerDataDisposition::Unmatched => {}
                                // Admission capacity exhausted: the overlay
                                // retains the frame for retry, with no
                                // actor-side effect and no peer charge.
                                CoordinatorLedgerDataDisposition::Deferred => {
                                    return LedgerDataIngressDisposition::Deferred;
                                }
                                // Consumed by the coordinator owner loop or a
                                // terminal session; never routed again.
                                CoordinatorLedgerDataDisposition::Delivered
                                | CoordinatorLedgerDataDisposition::Terminal => {
                                    return LedgerDataIngressDisposition::Delivered;
                                }
                                // Malformed coordinator payload: charge the
                                // source exactly like a legacy invalid reply.
                                CoordinatorLedgerDataDisposition::Invalid => {
                                    if let Some(peer) =
                                        router_overlay.find_peer_by_short_id(peer_id)
                                    {
                                        peer.charge(
                                            (*resource::FEE_INVALID_DATA).clone(),
                                            "TMLedgerData invalid node payload".to_owned(),
                                        );
                                    }
                                    return LedgerDataIngressDisposition::Delivered;
                                }
                            }
                        }
                        let routing = route_bootstrap_ledger_data(
                            &router_shared_inbound,
                            hash,
                            peer_id,
                            &message,
                        );
                        // AdmissionLeaseInvalid is a stale lease after
                        // terminal/sweep cleanup, never stale fetch-pack data.
                        // Base and transaction-node unmatched replies remain
                        // source-equivalent useless peer work.
                        if routing.charge_unsolicited
                            && let Some(peer) = router_overlay.find_peer_by_short_id(peer_id)
                        {
                            peer.charge(
                                (*resource::FEE_USELESS_DATA).clone(),
                                "Unsolicited TmLedgerData response".to_owned(),
                            );
                        }
                        return routing.disposition;
                    }
                    _ => {}
                }
                LedgerDataIngressDisposition::Delivered
            }));
        let drained = overlay_rt
            .overlay()
            .queued_inbound()
            .drain_ledger_data_to_router();
        if drained > 0 {
            tracing::info!(target: "consensus", drained, "Replayed buffered ledger-data packets after router installation");
        }
    }

    // Wire instant-wake notification for proposals arriving from peers.
    // This removes the 50ms poll latency in the consensus strand loop.
    if let Some(overlay_rt) = runtime.root().overlay_runtime() {
        let notify_root = runtime.root().clone();
        overlay_rt
            .overlay()
            .queued_inbound()
            .set_proposal_notify(Box::new(move || {
                notify_root.notify_consensus_event();
            }));
    }

    /// The coordinator's initial phase derived from the bootstrap startup
    /// intent. Quaxar preserves its legacy startup mode seed: networked ->
    /// `Connected`, `start_valid` -> `Full` from the hydrated LCL and its
    /// published ledger (the loaded ledger is published during
    /// `initialize_startup_ledger_state`). rippled seeds the constructor mode
    /// from `startValid` (`NetworkOPs.cpp:318`) and only later promotes with
    /// peer heartbeat logic; Quaxar's `Connected` seed is the retained
    /// divergence documented in the M6-D design note.
    fn startup_coordinator_phase(root: &ApplicationRoot) -> acquisition::SyncPhase {
        if root.config().start_valid {
            if let (Some(lcl), Some(published)) = (root.closed_ledger(), root.published_ledger()) {
                return acquisition::SyncPhase::Full {
                    lcl: acquisition::LedgerIdentity::new(
                        *lcl.header().hash.as_uint256(),
                        lcl.header().seq,
                    ),
                    published: acquisition::LedgerIdentity::new(
                        *published.header().hash.as_uint256(),
                        published.header().seq,
                    ),
                };
            }
        }
        acquisition::SyncPhase::Connected
    }

    fn recover_deferred_replay_parent(
        root: &ApplicationRoot,
        shared_inbound: &Arc<crate::ledger::inbound_ledgers::InboundLedgers>,
        shared_completed_rx: &std::sync::mpsc::Receiver<
            crate::ledger::inbound_ledgers::CompletedInboundLedger,
        >,
        stop: &AtomicBool,
        sweep_interval_seconds: u64,
    ) -> bool {
        let Some(initial) = root.pending_replay_startup() else {
            return true;
        };

        // The replay parent must become a normal completed inbound ledger before
        // it can be installed as the closed ledger. Do not start a consensus
        // strand against a synthetic or partial parent, and do not block that
        // strand waiting for peer I/O: acquisition workers and the overlay router
        // continue independently while this bootstrap coordinator retries.
        //
        // M6-D: when the coordinator is installed it owns the mode from
        // `install_coordinator`; the recovery intent is submitted as acquire
        // demand (a coordinator input fact) instead of this direct Syncing
        // write. The legacy write remains the rollback path for the
        // coordinator-less setup. rippled reaches the same Syncing state via
        // NetworkOPs `setState` from `InboundLedgers::acquire` promotion
        // (`NetworkOPs.cpp` `beginConsensus`/`setState` paths).
        if !shared_inbound.coordinator_installed() {
            root.set_network_ops_operating_mode_with_reason(
                crate::NetworkOpsOperatingMode::Syncing,
                "replay_parent_recovery",
            );
        }
        tracing::info!(target: "bootstrap",
            parent_seq = initial.parent_seq,
            parent_hash = %initial.parent_hash,
            "requesting incomplete replay parent through inbound history acquisition"
        );

        let mut last_sweep = std::time::Instant::now();
        let sweep_interval = Duration::from_secs(sweep_interval_seconds.max(1));
        while !stop.load(Ordering::Acquire) {
            let Some(pending) = root.pending_replay_startup() else {
                return true;
            };

            // acquire() only starts/touches an acquisition and returns immediately.
            // Its worker-owned AccountStateSF/TransactionStateSF lifecycle writes
            // all accepted nodes and performs the NodeStore sync before exposing a
            // completed ledger here.
            //
            // M6-D: in coordinator mode acquire() mints a coordinator session and
            // returns None for a new start, exactly like rippled
            // `InboundLedgers::acquire`. The durable completion then arrives on
            // the completed-ledger channel the strand would otherwise drain (it is
            // not yet spawned while replay is gated). Consume that channel here so
            // replay can proceed; the coordinator durably persisted the parent
            // before the handoff, so the skipped strand `storeLedger` is redundant.
            let coordinator_mode = shared_inbound.coordinator_installed();
            // The registry's `need_network_ledger` admission gate rejects
            // `History` acquires whenever the derived atomic is true. Legacy
            // replay startups never set the atomic (StartUpType::Replay), but
            // the coordinator derives it true for `Connected`/`Syncing`, so the
            // replay parent must be requested as `Generic` in coordinator mode:
            // it is a required startup ledger, not history backfill.
            let parent_reason = if coordinator_mode {
                crate::ledger::inbound_ledgers::AcquireReason::Generic
            } else {
                crate::ledger::inbound_ledgers::AcquireReason::History
            };
            let parent_complete = if coordinator_mode {
                shared_inbound.acquire(pending.parent_hash, pending.parent_seq, parent_reason);
                let mut complete = false;
                while let Ok(completed) = shared_completed_rx.try_recv() {
                    if completed.ledger.header().hash.as_uint256() == &pending.parent_hash {
                        complete = true;
                    }
                }
                complete
            } else {
                shared_inbound
                    .acquire(pending.parent_hash, pending.parent_seq, parent_reason)
                    .is_some()
            };
            if parent_complete {
                match replay_startup_ledger_from_storage(
                    root,
                    pending.start_ledger.as_deref(),
                    pending.trap_tx_hash,
                ) {
                    Ok(ReplayStartupResult::Complete) => {
                        root.clear_pending_replay_startup(pending.parent_hash);
                        tracing::info!(target: "bootstrap",
                            parent_seq = pending.parent_seq,
                            parent_hash = %pending.parent_hash,
                            "inbound history acquisition completed replay parent; replay startup resumed"
                        );
                        return true;
                    }
                    Ok(ReplayStartupResult::ParentIncomplete(updated)) => {
                        // A completed acquisition must normally make this false.
                        // Retain the exact (possibly reloaded) request rather than
                        // admitting a partial parent if a store/backend race is
                        // observed; the existing sweep/retry lifecycle will retry.
                        root.defer_replay_startup(updated);
                    }
                    Err(error) => {
                        tracing::error!(target: "bootstrap", %error,
                            "replay startup failed after parent acquisition"
                        );
                        root.signal_stop(format!(
                            "replay startup failed after historical parent acquisition: {error}"
                        ));
                        return false;
                    }
                }
            }

            // NetworkOps normally owns this at the configured sweep cadence. It
            // has not been started while replay is gated, so invoke the same
            // registry lifecycle here to allow failed history requests to age out
            // and retry without any consensus-strand work.
            if last_sweep.elapsed() >= sweep_interval {
                shared_inbound.sweep();
                last_sweep = std::time::Instant::now();
            }
            root.wait_consensus_or_timeout(Duration::from_millis(250));
        }
        false
    }

    if !recover_deferred_replay_parent(
        runtime.root(),
        &shared_inbound,
        &shared_completed_rx,
        stop.as_ref(),
        configured_sweep_interval_seconds,
    ) {
        // The coordinator either observed shutdown or recorded a fatal replay
        // error. In both cases no strand was started, so stop the shared
        // acquisition workers before returning to the bootstrap owner.
        shared_inbound.stop();
        return;
    }

    // ===================================================================
    // Spawn NetworkOpsStrand — it owns the ConsensusRunner and drives
    // proposals, timer ticks, accept, checkAccept, tryAdvance, mode
    // promotion, and history backfill on its own dedicated thread.
    // The strand also now handles storeLedger drain and pending acquisition.
    // ===================================================================
    let mut strand = NetworkOpsStrand::spawn(NetworkOpsStrandDeps {
        root: runtime.root().clone(),
        consensus_rt: Arc::clone(&consensus_rt),
        shared_inbound: Arc::clone(&shared_inbound),
        configured_ledger_history,
        configured_ledger_fetch_size: crate::NodeSizeResourceProfile::for_node_size(
            runtime.root().status_rpc_node_size().as_deref(),
        )
        .ledger_fetch_size,
        min_peer_count: if runtime.root().config().start_valid {
            0
        } else {
            runtime.root().config().network_quorum
        },
        shared_completed_rx: Some(shared_completed_rx),
    });

    // `TransactionAcquire::mapComplete` publishes directly into the sole
    // consensus FIFO. There is no intermediate receiver/forwarder that a
    // later heartbeat could overtake. Saturation returns false so
    // InboundTransactions retains its durable replay marker.
    {
        let ingress = strand.ingress.clone();
        runtime
            .root()
            .inbound_transactions()
            .lock()
            .expect("inbound_transactions mutex")
            .set_map_complete_sink(Arc::new(move |hash, set| ingress.publish_tx_set(hash, set)));
    }

    // ===================================================================
    // Wire verified trusted proposals into the same FIFO as consensus timers.
    // Proposals arriving from peers enter the strand command FIFO directly,
    // bypassing the polling loop without creating another ordering domain.
    // ===================================================================
    if let Some(overlay_rt) = runtime.root().overlay_runtime() {
        let consensus_ingress = strand.ingress.clone();
        let proposal_root = runtime.root().clone();
        let proposal_overlay = overlay_rt.overlay();
        overlay_rt
            .overlay()
            .queued_inbound()
            .set_proposal_router(Box::new(move |proposal| {
                let trusted = proposal_root.validators().trusted(proposal.public_key);
                let policy = proposal_root.relay_untrusted_proposals_policy();
                // Drop policy precedes HashRouter source admission and the
                // later signature check, exactly as in PeerImp::onMessage.
                if !trusted && policy.should_drop() {
                    return;
                }
                if !proposal_overlay.admit_proposal_source(
                    proposal.suppression,
                    proposal.public_key,
                    proposal.peer_id,
                ) {
                    return;
                }
                let cluster = proposal_overlay
                    .find_peer_by_short_id(proposal.peer_id)
                    .is_some_and(|peer| peer.cluster());
                if !trusted
                    && (proposal_overlay.peer_is_diverged(proposal.peer_id)
                        || (!cluster && proposal_root.load_fee_track_loaded_local()))
                {
                    return;
                }
                let ingress = consensus_ingress.clone();
                let job_root = proposal_root.clone();
                let job_type = if trusted {
                    crate::job::job_types::JobType::JtProposalT
                } else {
                    crate::job::job_types::JobType::JtProposalUt
                };
                if !proposal_root
                    .job_queue()
                    .add_job(job_type, "checkPropose", move || {
                        // Only cluster traffic bypasses the scheduled
                        // signature check. Untrusted traffic never enters the
                        // consensus strand; it may still relay under `all`.
                        if !cluster && !proposal.check_sign() {
                            return;
                        }
                        if trusted {
                            // rippled's JtProposalT calls directly into the
                            // mutex-protected consensus engine, so a busy
                            // consensus owner applies backpressure rather than
                            // silently discarding a trusted proposal. The
                            // strand is Quaxar's single owner; blocking until
                            // it drains is the equivalent lossless handoff.
                            if !ingress.publish_trusted_proposal(proposal) {
                                tracing::debug!(
                                    target: "consensus",
                                    "trusted proposal dropped because the consensus strand stopped"
                                );
                            }
                        } else if policy.should_relay() || cluster {
                            if let Some(overlay_runtime) = job_root.overlay_runtime() {
                                overlay_runtime.overlay().relay_proposal(
                                    proposal.message,
                                    proposal.suppression,
                                    proposal.public_key,
                                );
                            }
                        }
                    })
                {
                    tracing::debug!(target: "consensus", "proposal job rejected during shutdown");
                }
            }));
    }

    // ===================================================================
    // NEW: Wire get_ledger_router → JobQueue dispatch
    // GetLedger requests are dispatched directly to the job queue from the
    // network thread, matching rippled's PeerImp::onMessage(TMGetLedger).
    // ===================================================================
    if let Some(overlay_rt) = runtime.root().overlay_runtime() {
        let router_root = runtime.root().clone();
        let router_overlay_rt = Arc::clone(&overlay_rt);
        let get_ledger_fetch_depth = configured_ledger_history;
        overlay_rt
            .overlay()
            .queued_inbound()
            .set_get_ledger_router(Box::new(move |peer_id, message| {
                // PeerImp rejects a request more than ten ledgers ahead while
                // the validated ledger is fresh. This app-owned router has the
                // live LedgerMaster age/sequence required for that check.
                if router_root.validated_ledger_age() <= Duration::from_secs(10)
                    && message.ledger_seq.is_some_and(|seq| {
                        seq > router_root
                            .validated_ledger_seq()
                            .unwrap_or_default()
                            .saturating_add(10)
                    })
                {
                    if let Some(peer) = router_overlay_rt.overlay().find_peer_by_short_id(peer_id) {
                        peer.charge(
                            (*resource::FEE_INVALID_DATA).clone(),
                            "TMGetLedger invalid ledger sequence".to_owned(),
                        );
                    }
                    return;
                }
                let req = overlay::PeerMessage { peer_id, message };
                // `PeerImp::onMessage(TMGetLedger)` queues every valid request,
                // including liTS_CANDIDATE, on JtLedgerReq. Candidate-set map
                // walks are just as peer-controlled and must not run inline on
                // the overlay callback path.
                let job_root = router_root.clone();
                let job_overlay_rt = Arc::clone(&router_overlay_rt);
                router_root.job_queue().add_job(
                    crate::job::job_types::JobType::JtLedgerReq,
                    "RcvGetLedger",
                    move || {
                        serve_one_get_ledger_request(
                            &job_root,
                            &job_overlay_rt,
                            req,
                            get_ledger_fetch_depth,
                        );
                    },
                );
            }));
    }

    // ===================================================================
    // NEW: Wire get_objects_router → JobQueue dispatch
    // GetObjectByHash/FetchPack requests are dispatched directly to the job
    // queue from the network thread.
    // ===================================================================
    if let Some(overlay_rt) = runtime.root().overlay_runtime() {
        let router_root = runtime.root().clone();
        let router_overlay_rt = Arc::clone(&overlay_rt);
        let router_shared_inbound = Arc::clone(&shared_inbound);
        // `LedgerMaster::getEarliestFetch` uses the configured history depth.
        // Keep that policy with the live overlay router rather than deriving a
        // separate retention range in a transport-only helper.
        let fetch_pack_depth = configured_ledger_history;
        overlay_rt
            .overlay()
            .queued_inbound()
            .set_get_objects_router(Box::new(move |peer_id, message| {
                let msg_envelope = overlay::PeerMessage { peer_id, message };
                let msg = &msg_envelope.message;
                // PeerImp's send-queue overload admission applies to every
                // query before dispatching by object type, including FetchPack
                // and otTRANSACTIONS requests.
                if msg.query
                    && router_overlay_rt
                        .overlay()
                        .find_peer_by_short_id(peer_id)
                        .is_some_and(|peer| {
                            !get_object_query_send_queue_is_admissible(peer.send_queue_size())
                        })
                {
                    return;
                }
                if !msg.query {
                    // Match PeerImp's reply path: a fetch pack is segmented by
                    // ledger sequence, and nodes for a ledger that is already
                    // complete are ignored as late data. Generic object replies
                    // continue to populate the shared content-addressed cache.
                    let is_fetch_pack = msg.r#type
                        == overlay::message::wire::tm_get_object_by_hash::ObjectType::OtFetchPack
                            as i32;
                    let ledger_master = router_root
                        .ledger_master_runtime()
                        .map(|runtime| runtime.ledger_master());
                    let mut stored = 0usize;
                    let mut pack_seq = 0u32;
                    let mut store_current_pack = true;
                    let mut progress = false;

                    for obj in &msg.objects {
                        let (Some(hash_bytes), Some(data)) = (&obj.hash, &obj.data) else {
                            continue;
                        };
                        let Some(hash) = Uint256::from_slice(hash_bytes) else {
                            continue;
                        };

                        if is_fetch_pack
                            && let Some(ledger_seq) = obj.ledger_seq
                            && ledger_seq != pack_seq
                        {
                            pack_seq = ledger_seq;
                            store_current_pack = ledger_master
                                .as_ref()
                                .is_none_or(|master| !master.have_ledger(ledger_seq));
                            progress |= store_current_pack;
                        }
                        if is_fetch_pack && !store_current_pack {
                            continue;
                        }

                        // InboundLedgers and LedgerMaster share the one
                        // rippled-parity fetch-pack cache owner.
                        router_shared_inbound.store_fetch_pack(hash, data.clone());
                        stored += 1;
                    }

                    if is_fetch_pack {
                        tracing::debug!(target: "consensus", peer_id, pack_seq, stored, progress,
                            "processed fetch-pack reply");
                        let dispatch = ledger_master
                            .as_ref()
                            .is_none_or(|master| master.got_fetch_pack(progress, pack_seq));
                        if dispatch {
                            let ready_root = router_root.clone();
                            let ready_inbound = Arc::clone(&router_shared_inbound);
                            let ready_master = ledger_master.clone();
                            let rejected_master = ledger_master.clone();
                            let queued = router_root.job_queue().add_job(
                                crate::job::job_types::JobType::JtLedgerData,
                                "GotFetchPack",
                                move || {
                                    // A reply can contain no useful/complete
                                    // nodes; it still releases the single-flight
                                    // completion path, as in gotFetchPack.
                                    ready_root.signal_fetch_pack_ready();
                                    ready_inbound.finish_fetch_pack_pass();
                                    if let Some(master) = ready_master {
                                        master.finish_got_fetch_pack();
                                    }
                                },
                            );
                            if !queued {
                                // `gotFetchPack` owns an atomic single-flight
                                // flag. Clear it synchronously when shutdown
                                // refuses the completion job.
                                if let Some(master) = rejected_master {
                                    master.finish_got_fetch_pack();
                                }
                            }
                        }
                    } else if should_schedule_coordinator_fetch_pack_wake(
                        stored,
                        router_shared_inbound.coordinator_installed(),
                    ) {
                        // Coordinator plans request state and transaction nodes
                        // through TMGetObjectByHash. Those replies populate the
                        // same fetch-pack cache as rippled's PeerImp reply path,
                        // but are not `otFETCH_PACK` and therefore do not enter
                        // LedgerMaster's gotFetchPack single-flight. Wake the
                        // coordinator through its typed pass on JtLedgerData,
                        // never from the overlay callback: this makes the newly
                        // cached nodes visible to the owning plan immediately
                        // and preserves the no-blocking-ingress boundary.
                        let ready_inbound = Arc::clone(&router_shared_inbound);
                        let _ = router_root.job_queue().add_job(
                            crate::job::job_types::JobType::JtLedgerData,
                            "CoordinatorGetObjectReply",
                            move || ready_inbound.finish_fetch_pack_pass(),
                        );
                    }
                } else if msg.r#type
                    == overlay::message::wire::tm_get_object_by_hash::ObjectType::OtFetchPack as i32
                {
                    // PeerImp handles FetchPack separately from generic object
                    // serving: fast admission happens on ingress, then the
                    // expensive history/map traversal is serialized on JtPack.
                    let Some(peer) = router_overlay_rt.overlay().find_peer_by_short_id(peer_id)
                    else {
                        return;
                    };
                    match classify_fetch_pack_request(
                        router_root.load_fee_track_loaded_local(),
                        router_root.validated_ledger_age(),
                        router_root
                            .job_queue()
                            .job_count(crate::job::job_types::JobType::JtPack),
                        msg.ledger_hash.as_deref(),
                    ) {
                        FetchPackAdmission::Busy => (),
                        FetchPackAdmission::Malformed => {
                            peer.charge(
                                (*resource::FEE_MALFORMED_REQUEST).clone(),
                                "FetchPack hash size malformed".to_owned(),
                            );
                        }
                        FetchPackAdmission::Accepted(ledger_hash) => {
                            peer.charge(
                                (*resource::FEE_HEAVY_BURDEN_PEER).clone(),
                                "FetchPack request".to_owned(),
                            );
                            let job_root = router_root.clone();
                            let job_overlay_rt = Arc::clone(&router_overlay_rt);
                            let job_peer_id = peer_id;
                            let issued_at = std::time::Instant::now();
                            let job_fetch_depth = fetch_pack_depth;
                            let _ = router_root.job_queue().add_job(
                                crate::job::job_types::JobType::JtPack,
                                "MakeFetchPack",
                                move || {
                                    serve_fetch_pack_request(
                                        &job_root,
                                        &job_overlay_rt,
                                        job_peer_id,
                                        ledger_hash,
                                        issued_at,
                                        job_fetch_depth,
                                    );
                                },
                            );
                        }
                    }
                } else if msg.r#type
                    == overlay::message::wire::tm_get_object_by_hash::ObjectType::OtTransactions
                        as i32
                {
                    // PeerImp routes reduce-relay object requests through its
                    // dedicated JtRequestedTxn lane and answers with a
                    // TMTransactions batch rather than a GetObjects reply.
                    let Some(peer) = router_overlay_rt.overlay().find_peer_by_short_id(peer_id)
                    else {
                        return;
                    };
                    if !peer.tx_reduce_relay_enabled() {
                        peer.charge(
                            (*resource::FEE_MALFORMED_REQUEST).clone(),
                            "TMGetObjectByHash transactions disabled".to_owned(),
                        );
                        return;
                    }
                    if !transaction_object_request_is_admissible(&msg.objects) {
                        peer.charge(
                            (*resource::FEE_MALFORMED_REQUEST).clone(),
                            "TMGetObjectByHash transactions malformed".to_owned(),
                        );
                        return;
                    }
                    let job_root = router_root.clone();
                    let job_overlay_rt = Arc::clone(&router_overlay_rt);
                    if !router_root.job_queue().add_job(
                        crate::job::job_types::JobType::JtRequestedTxn,
                        "DoTxs",
                        move || {
                            serve_requested_transactions(&job_root, &job_overlay_rt, &msg_envelope);
                        },
                    ) {
                        tracing::debug!(target: "overlay", peer_id,
                            "requested-transaction job rejected during shutdown");
                    }
                } else {
                    match classify_generic_get_object_request(
                        msg.ledger_hash.as_deref(),
                        msg.objects.len(),
                    ) {
                        GenericGetObjectAdmission::MalformedLedgerHash => {
                            if let Some(peer) =
                                router_overlay_rt.overlay().find_peer_by_short_id(peer_id)
                            {
                                peer.charge(
                                    (*resource::FEE_MALFORMED_REQUEST).clone(),
                                    "get object ledger hash".to_owned(),
                                );
                            }
                        }
                        GenericGetObjectAdmission::Oversized => {
                            if let Some(peer) =
                                router_overlay_rt.overlay().find_peer_by_short_id(peer_id)
                            {
                                peer.charge(
                                    (*resource::FEE_INVALID_DATA).clone(),
                                    "oversized get object request".to_owned(),
                                );
                            }
                        }
                        GenericGetObjectAdmission::Accepted => {
                            let job_root = router_root.clone();
                            let job_overlay_rt = Arc::clone(&router_overlay_rt);
                            let queued = router_root.job_queue().add_job(
                                crate::job::job_types::JobType::JtLedgerReq,
                                "RcvGetObjByHash",
                                move || {
                                    serve_get_object_by_hash_request(
                                        &job_root,
                                        &job_overlay_rt,
                                        &msg_envelope,
                                    );
                                },
                            );
                            // PeerImp bills this base burden only after bounded
                            // job admission succeeds, closing the enqueue-flood
                            // window without charging shutdown rejections.
                            if queued
                                && let Some(peer) =
                                    router_overlay_rt.overlay().find_peer_by_short_id(peer_id)
                            {
                                peer.charge(
                                    (*resource::FEE_MODERATE_BURDEN_PEER).clone(),
                                    "received a get object by hash request".to_owned(),
                                );
                            }
                        }
                    }
                }
            }));
    }

    // TransactionAcquire is a TimeoutCounter with a 250 ms interval in
    // rippled. Keep its retry/add-peer cadence independent from the one-second
    // cache/overlay housekeeping loop below.
    {
        let candidate_stop = Arc::clone(&stop);
        let candidate_root = runtime.root().clone();
        worker_handles.push(
            std::thread::Builder::new()
                .name("candidate-acquire-timer".into())
                .spawn(move || {
                    while !candidate_stop.load(Ordering::Acquire) {
                        std::thread::sleep(CANDIDATE_ACQUIRE_TICK);
                        if candidate_stop.load(Ordering::Acquire) {
                            break;
                        }
                        candidate_root
                            .inbound_transactions()
                            .lock()
                            .expect("inbound_transactions mutex")
                            .tick_pending_acquires();
                    }
                })
                .expect("spawn candidate-acquire-timer thread"),
        );
    }

    // ===================================================================
    // NEW: Spawn housekeeping timer thread (1s interval)
    // Handles validator list draining, inbound_transactions tick, and
    // TreeNodeCache sweep — matching rippled's doSweep timer.
    // ===================================================================
    {
        let hk_stop = Arc::clone(&stop);
        let hk_runtime = Arc::clone(&runtime);
        let hk_shared_inbound = Arc::clone(&shared_inbound);
        let hk_sweep_interval = configured_sweep_interval_seconds;
        worker_handles.push(
            std::thread::Builder::new()
            .name("housekeeping-timer".into())
            .spawn(move || {
                // rippled sweeps TreeNodeCache every SweepInterval (60s for medium)
                let mut last_cache_sweep = std::time::Instant::now();
                while !hk_stop.load(Ordering::Acquire) {
                    std::thread::sleep(Duration::from_secs(1));
                    if hk_stop.load(Ordering::Acquire) {
                        break;
                    }
                    let root = hk_runtime.root();

                    // TreeNodeCache sweep — matching rippled's doSweep which calls
                    // nodeFamily_.sweep() at SweepInterval cadence (config-based per node_size).
                    // InboundLedgers::sweep belongs to this same doSweep cadence:
                    // rippled does not sweep inbound ledgers on every overlay tick.
                    if last_cache_sweep.elapsed() >= Duration::from_secs(hk_sweep_interval) {
                        run_application_sweep(
                            root.temp_node_cache(),
                            &ProductionApplicationSweep {
                                root,
                                inbound: hk_shared_inbound.as_ref(),
                            },
                        );

                        last_cache_sweep = std::time::Instant::now();
                    }

                    let Some(overlay_rt) = root.overlay_runtime() else {
                        continue;
                    };

                    // ─── Overlay timer duties (matching rippled OverlayImpl::Timer) ───
                    // Ping peers every 60s and delete_idle_peers every 4s.
                    {
                        use overlay::Overlay;

                        // delete_idle_peers every 4 ticks (matching CHECK_IDLE_PEERS = 4)
                        static IDLE_TICK: std::sync::atomic::AtomicU32 =
                            std::sync::atomic::AtomicU32::new(0);
                        let tick = IDLE_TICK.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if tick.is_multiple_of(4) {
                            overlay_rt.overlay().delete_idle_peers();
                        }

                        // relay_history sweep every 60s — prunes entries for disconnected peers
                        // preventing unbounded memory growth on long-lived nodes.
                        static LAST_RELAY_SWEEP: std::sync::atomic::AtomicU64 =
                            std::sync::atomic::AtomicU64::new(0);
                        let now_secs = std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                            .map(|d| d.as_secs())
                            .unwrap_or(0);
                        let last_sweep =
                            LAST_RELAY_SWEEP.load(std::sync::atomic::Ordering::Relaxed);
                        if now_secs.saturating_sub(last_sweep) >= 60 {
                            LAST_RELAY_SWEEP.store(now_secs, std::sync::atomic::Ordering::Relaxed);
                            overlay_rt.overlay().sweep_relay_history(5000);
                        }

                        // OverlayImpl calls sendEndpoints every second, but
                        // PeerFinder::buildEndpointsForPeers handouts only when
                        // its 151-second broadcast deadline is due. Build a
                        // distinct, bounded handout for each peer: an IPv6
                        // unspecified self entry at hop 0 plus filtered live
                        // endpoints, never a once-per-second full fanout.
                        static LAST_ENDPOINT_HANDOUT_SECS: std::sync::atomic::AtomicU64 =
                            std::sync::atomic::AtomicU64::new(0);
                        let now_secs = std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                            .map(|d| d.as_secs())
                            .unwrap_or(0);
                        let last_handout = LAST_ENDPOINT_HANDOUT_SECS
                            .load(std::sync::atomic::Ordering::Relaxed);
                        if now_secs.saturating_sub(last_handout)
                            >= ENDPOINT_HANDOUT_INTERVAL.as_secs()
                        {
                            LAST_ENDPOINT_HANDOUT_SECS.store(
                                now_secs,
                                std::sync::atomic::Ordering::Relaxed,
                            );
                            let peers = overlay_rt.overlay().active_peers();
                            let listener_port = overlay_rt
                                .listener_setup()
                                .map(|setup| setup.port);
                            let candidates = peers
                                .iter()
                                .map(|peer| peer.remote_address())
                                .collect::<Vec<_>>();
                            let now = std::time::Instant::now();

                            for peer in &peers {
                                let endpoints_v2 = build_endpoint_handout(
                                    listener_port,
                                    peer.remote_address(),
                                    candidates.iter().copied(),
                                    |endpoint, hops| {
                                        if peer.should_filter_recent_endpoint(
                                            endpoint,
                                            hops,
                                            now,
                                            ENDPOINT_HANDOUT_TTL,
                                        ) {
                                            return false;
                                        }
                                        peer.remember_recent_endpoint(
                                            endpoint,
                                            hops,
                                            now,
                                            ENDPOINT_HANDOUT_TTL,
                                        );
                                        true
                                    },
                                );
                                if !endpoints_v2.is_empty() {
                                    peer.send(overlay::Message::new(
                                        overlay::ProtocolMessage::new(
                                            overlay::ProtocolPayload::Endpoints(
                                                overlay::TmEndpoints {
                                                    version: 2,
                                                    endpoints_v2,
                                                },
                                            ),
                                        ),
                                        None,
                                    ));
                                }
                            }
                        }

                        // Per-peer PeerImp timers send cookie-bound pings and
                        // enforce the matching timeout. Do not duplicate that
                        // lifecycle in this global housekeeping loop.
                    }

                    let (manifests, validator_lists, validator_list_collections) =
                        take_validator_list_inbound(&overlay_rt.overlay());

                    // Drain accepted manifest updates, install them in the shared
                    // validator ManifestCache, and relay only newly accepted blobs.
                    // This is OverlayImpl::onManifests parity; do not echo a
                    // peer's accepted manifests back to that peer.
                    for inbound in manifests {
                        let mut relay_list = Vec::new();
                        let mut trusted_manifest_accepted = false;
                        // Bound untrusted work to the configured per-message cap,
                        // but never drop a trusted validator manifest merely
                        // because it follows untrusted gossip.
                        let max_untrusted_count = root.manifest_limits().max_untrusted_count;
                        let mut untrusted_processed = 0usize;
                        let mut skipped_untrusted = false;

                        for wire_manifest in inbound.message.list {
                            if wire_manifest.stobject.len() > MAX_MANIFEST_BYTES {
                                continue;
                            }
                            let Some(manifest) = crate::state::manifest::deserialize_manifest(
                                &wire_manifest.stobject,
                            ) else {
                                tracing::debug!(
                                    target: "overlay",
                                    peer_id = inbound.peer_id,
                                    "discarding malformed manifest"
                                );
                                continue;
                            };

                            let master_key = manifest.master_key;
                            let is_trusted = root.validators().listed(master_key);
                            let Some(policy) = manifest_rate_limit_policy(
                                is_trusted,
                                &mut untrusted_processed,
                                max_untrusted_count,
                            ) else {
                                skipped_untrusted = true;
                                continue;
                            };

                            let disposition = root
                                .manifest_cache()
                                .apply_manifest_with_policy(manifest, policy);
                            if relay_accepted_manifest(disposition) {
                                if is_trusted {
                                    root.manifest_cache().promote_to_trusted(&master_key);
                                    trusted_manifest_accepted = true;
                                }
                                // Relay every newly accepted manifest. Stale cache
                                // entries and rejected admissions are not relayed.
                                relay_list.push(wire_manifest);
                            }
                        }

                        if skipped_untrusted
                            && let Some(peer) = overlay_rt.overlay().find_peer_by_short_id(inbound.peer_id)
                        {
                            peer.charge(
                                (*resource::FEE_MALFORMED_REQUEST).clone(),
                                "too many untrusted manifests".to_owned(),
                            );
                        }

                        if trusted_manifest_accepted
                            && let Err(error) = root.persist_manifest_caches()
                        {
                            tracing::error!(target: "manifest", %error,
                                "failed to persist newly accepted trusted manifest");
                        }

                        if !relay_list.is_empty() {
                            let message = overlay::Message::new(
                                overlay::ProtocolMessage::new(overlay::ProtocolPayload::Manifests(
                                    overlay::TmManifests {
                                        list: relay_list,
                                        ..Default::default()
                                    },
                                )),
                                None,
                            );
                            for peer in overlay_rt.overlay().active_peers() {
                                if peer.id() != inbound.peer_id {
                                    peer.send(message.clone());
                                }
                            }
                        }
                    }

                    // Drain validator list messages and apply them to the local UNL
                    let messages = validator_lists;
                    if !messages.is_empty() {
                        for msg in messages {
                            let tm = &msg.message;
                            let manifest_b64 = basics::base64::base64_encode(&tm.manifest);
                            let blob_info = crate::validator::validator_list::ValidatorBlobInfo {
                                blob: basics::base64::base64_encode(&tm.blob),
                                signature: basics::str_hex::str_hex(&tm.signature),
                                manifest: None,
                            };
                            let hash = crate::validator::validator_list::validator_list_collection_hash(
                                &manifest_b64,
                                tm.version,
                                std::slice::from_ref(&blob_info),
                            );
                            let stats = root.apply_validator_lists_from_peer(
                                msg.peer_id,
                                &manifest_b64,
                                tm.version,
                                &[blob_info],
                                String::new(),
                                hash,
                            );
                            synchronize_unl_blocked(root);
                            broadcast_validator_list_collection(root, &stats, hash);
                            tracing::trace!(
                                target: "overlay",
                                version = tm.version,
                                ?stats,
                                "applied TMValidatorList from peer"
                            );
                        }
                    }

                    // v2 validator-list collections use the same application
                    // and replay semantics as v1, but preserve all current and
                    // pending blobs for peers that negotiated the v2 feature.
                    for collection in validator_list_collections {
                        apply_validator_list_collection_from_peer(
                            root,
                            collection.peer_id,
                            &collection.message,
                        );
                    }
                }
            })
            .expect("spawn housekeeping-timer thread"),
        );
    }

    // ===================================================================
    // Wait for stop signal (replaces the polling while loop)
    // All duties are now callback-driven or timer-driven.
    // ===================================================================
    while !stop.load(Ordering::Acquire) {
        std::thread::sleep(Duration::from_millis(500));
    }

    // Mirror ApplicationImp::run: NetworkOPs stops first, then the active
    // InboundLedgers registry quiesces its acquisitions and worker pool before
    // bootstrap returns to MainRuntime::shutdown (which stops NodeStore).
    strand.stop();
    shared_inbound.stop();
    for handle in worker_handles {
        let _ = handle.join();
    }
    tracing::info!(target: "consensus", "Overlay service loop stopped");
}

/// PeerFinder::Tuning::kSecondsPerMessage. OverlayImpl ticks every second,
/// but peer endpoint handouts are intentionally much less frequent.
const ENDPOINT_HANDOUT_INTERVAL: Duration = Duration::from_secs(151);
const ENDPOINT_HANDOUT_TTL: Duration = Duration::from_secs(30);
const ENDPOINT_HANDOUT_LIMIT: usize = 12; // 2 * PeerFinder::kMaxHops

fn canonical_endpoint_ip(ip: std::net::IpAddr) -> std::net::IpAddr {
    match ip {
        std::net::IpAddr::V6(ipv6) => ipv6
            .to_ipv4_mapped()
            .map(std::net::IpAddr::V4)
            .unwrap_or(std::net::IpAddr::V6(ipv6)),
        std::net::IpAddr::V4(_) => ip,
    }
}

/// Bootstrap-local equivalent of PeerFinder::Logic::buildEndpointsForPeers:
/// give each target a bounded, deduplicated handout and let its recent-endpoint
/// state suppress repeated work. Active peer addresses are the live endpoints
/// available to this bootstrap-owned runtime; the application PeerFinder owns
/// longer-lived cache discovery separately.
fn build_endpoint_handout<F>(
    listening_port: Option<u16>,
    recipient: std::net::SocketAddr,
    candidates: impl IntoIterator<Item = std::net::SocketAddr>,
    mut admit: F,
) -> Vec<overlay::message::wire::tm_endpoints::TmEndpointv2>
where
    F: FnMut(std::net::SocketAddr, u32) -> bool,
{
    let mut endpoints = Vec::with_capacity(ENDPOINT_HANDOUT_LIMIT);
    if let Some(port) = listening_port {
        endpoints.push(overlay::message::wire::tm_endpoints::TmEndpointv2 {
            // Rippled advertises an unspecified IPv6 address: recipients use
            // their socket's remote address for hop-zero self advertisements.
            endpoint: std::net::SocketAddr::new(std::net::Ipv6Addr::UNSPECIFIED.into(), port)
                .to_string(),
            hops: 0,
        });
    }

    let mut seen_ips = std::collections::BTreeSet::new();
    let candidates = candidates
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>();
    for endpoint in candidates {
        if endpoints.len() >= ENDPOINT_HANDOUT_LIMIT
            || canonical_endpoint_ip(endpoint.ip()) == canonical_endpoint_ip(recipient.ip())
        {
            continue;
        }
        let hops = 1;
        if !seen_ips.insert(canonical_endpoint_ip(endpoint.ip())) || !admit(endpoint, hops) {
            continue;
        }
        endpoints.push(overlay::message::wire::tm_endpoints::TmEndpointv2 {
            endpoint: endpoint.to_string(),
            hops,
        });
    }
    endpoints
}

const MAX_MANIFEST_BYTES: usize = 358;

/// Select startup manifest gossip like rippled OverlayImpl::getManifestsMessage:
/// every listed (trusted) manifest precedes an independently capped tail of
/// untrusted gossip. The caller snapshots cache bytes before consulting the
/// ValidatorList, avoiding manifest-cache/validator-list lock inversion.
fn trusted_first_manifest_payloads(
    entries: impl IntoIterator<Item = (bool, Vec<u8>)>,
    manifest_limits: ManifestLimits,
) -> Vec<Vec<u8>> {
    let mut trusted = Vec::new();
    let mut untrusted = Vec::new();
    for (is_trusted, serialized) in entries {
        if is_trusted {
            trusted.push(serialized);
        } else {
            untrusted.push(serialized);
        }
    }
    trusted.truncate(manifest_limits.max_trusted_count);
    trusted.extend(
        untrusted
            .into_iter()
            .take(manifest_limits.max_untrusted_count),
    );
    trusted
}

/// The application root attaches an early generic provider while constructing
/// the overlay. Reinstall it after manifests and ValidatorList have loaded so
/// newly connected peers receive all listed identities first, then only the
/// bounded untrusted tail used by the reference startup gossip path.
fn install_trusted_first_manifest_provider(root: &crate::ApplicationRoot) {
    let Some(overlay_rt) = root.overlay_runtime() else {
        return;
    };
    let manifests = Arc::clone(root.manifest_cache());
    let validators = root.validators();
    let manifest_limits = root.manifest_limits();
    overlay_rt
        .overlay()
        .set_manifests_message_provider(move || {
            let entries = manifests
                .serialized_manifests()
                .into_iter()
                .filter_map(|serialized| {
                    if serialized.len() > crate::validator::validator_list::MAX_MANIFEST_BYTES {
                        return None;
                    }
                    let manifest = crate::state::manifest::deserialize_manifest(&serialized)?;
                    Some((validators.listed(manifest.master_key), serialized))
                });
            let list = trusted_first_manifest_payloads(entries, manifest_limits)
                .into_iter()
                .map(|stobject| overlay::message::wire::TmManifest { stobject })
                .collect::<Vec<_>>();
            (!list.is_empty()).then(|| {
                overlay::ProtocolMessage::new(overlay::ProtocolPayload::Manifests(
                    overlay::TmManifests {
                        list,
                        ..Default::default()
                    },
                ))
            })
        });
}

fn synchronize_unl_blocked(root: &crate::ApplicationRoot) {
    root.set_unl_blocked(root.validators().unl_blocked());
}

/// `Config::validatorListThreshold`: no value and explicit zero select the
/// computed default; a nonzero threshold must be a single positive integer no
/// greater than the number of configured publisher keys.
fn validator_list_threshold_from_config(
    config: &BasicConfig,
    publisher_key_count: usize,
) -> Result<Option<usize>, String> {
    let values = config.section("validator_list_threshold").values();
    match values {
        [] => Ok(None),
        [raw] => {
            let threshold = raw.trim().parse::<usize>().map_err(|_| {
                "[validator_list_threshold] must contain a non-negative integer".to_owned()
            })?;
            if threshold == 0 {
                return Ok(None);
            }
            if threshold > publisher_key_count {
                return Err(
                    "Value in config section [validator_list_threshold] exceeds the number of configured list keys"
                        .to_owned(),
                );
            }
            Ok(Some(threshold))
        }
        _ => Err(
            "Config section [validator_list_threshold] should contain single value only".to_owned(),
        ),
    }
}

/// Convert a peer collection only after the same bounded manifest admission
/// used by `Manifest.cpp`; version and blob-count checks mirror PeerImp.
fn validator_list_collection_blobs(
    collection: &overlay::TmValidatorListCollection,
) -> Option<(String, u32, Vec<crate::ValidatorBlobInfo>)> {
    if collection.version < 2
        || collection.manifest.is_empty()
        || collection.manifest.len() > crate::validator::validator_list::MAX_MANIFEST_BYTES
        || collection.blobs.is_empty()
        || collection.blobs.len() > crate::validator::validator_list::MAX_SUPPORTED_BLOBS
    {
        return None;
    }
    let mut blobs = Vec::with_capacity(collection.blobs.len());
    for blob in &collection.blobs {
        if blob.manifest.as_ref().is_some_and(|manifest| {
            manifest.len() > crate::validator::validator_list::MAX_MANIFEST_BYTES
        }) {
            return None;
        }
        blobs.push(crate::ValidatorBlobInfo {
            blob: basics::base64::base64_encode(&blob.blob),
            signature: basics::str_hex::str_hex(&blob.signature),
            manifest: blob
                .manifest
                .as_ref()
                .map(|manifest| basics::base64::base64_encode(manifest)),
        });
    }
    Some((
        basics::base64::base64_encode(&collection.manifest),
        collection.version,
        blobs,
    ))
}

#[derive(Debug)]
struct ValidatorListCollectionMessage {
    message: overlay::Message,
    hash: Uint256,
}

fn build_validator_list_collection_messages(
    collection: &crate::ValidatorListCollectionForBroadcast,
    peer_sequence: usize,
    max_message_size: usize,
) -> Vec<ValidatorListCollectionMessage> {
    let blobs = collection
        .blobs
        .iter()
        .filter(|entry| entry.sequence > peer_sequence)
        .filter_map(|entry| {
            Some(overlay::message::wire::ValidatorBlobInfo {
                manifest: entry
                    .blob
                    .manifest
                    .as_ref()
                    .map(|manifest| basics::base64::base64_decode(manifest)),
                blob: basics::base64::base64_decode(&entry.blob.blob),
                signature: basics::string_utilities::str_unhex(&entry.blob.signature)?,
            })
        })
        .collect::<Vec<_>>();
    if blobs.is_empty() {
        return Vec::new();
    }

    fn build_part(
        version: u32,
        manifest: &[u8],
        blobs: &[overlay::message::wire::ValidatorBlobInfo],
        max_message_size: usize,
        messages: &mut Vec<ValidatorListCollectionMessage>,
    ) {
        let collection = overlay::TmValidatorListCollection {
            version,
            manifest: manifest.to_vec(),
            blobs: blobs.to_vec(),
        };
        let payload = overlay::ProtocolPayload::ValidatorListCollection(collection);
        if overlay::HEADER_BYTES.saturating_add(payload.encoded_len()) <= max_message_size {
            let hash = protocol::sha512_half(payload.encode_to_vec());
            messages.push(ValidatorListCollectionMessage {
                message: overlay::Message::new(overlay::ProtocolMessage::new(payload), None),
                hash,
            });
        } else if blobs.len() > 1 {
            let middle = blobs.len() / 2;
            build_part(
                version,
                manifest,
                &blobs[..middle],
                max_message_size,
                messages,
            );
            build_part(
                version,
                manifest,
                &blobs[middle..],
                max_message_size,
                messages,
            );
        }
    }

    let mut messages = Vec::new();
    build_part(
        collection.version.max(2),
        &basics::base64::base64_decode(&collection.manifest),
        &blobs,
        max_message_size,
        &mut messages,
    );
    messages
}

/// Send v2 collections with PeerImp-compatible recipient filtering, bounded
/// frames, and both original and emitted-message suppression records.
fn broadcast_validator_list_collection(
    root: &crate::ApplicationRoot,
    stats: &crate::PublisherListStats,
    hash: Uint256,
) {
    use overlay::{Overlay, ProtocolFeature};

    if stats.best_disposition() > crate::ListDisposition::KnownSequence {
        return;
    }
    let Some(publisher) = stats.publisher_key else {
        return;
    };
    let Some(to_skip) = root.validator_list_relay_skip(hash) else {
        return;
    };
    let Some(collection) = root.validators().collection_for_broadcast(publisher) else {
        return;
    };
    let Some(overlay_rt) = root.overlay_runtime() else {
        return;
    };
    for peer in overlay_rt.overlay().active_peers() {
        if to_skip.contains(&peer.id())
            || !peer.supports_feature(ProtocolFeature::ValidatorList2Propagation)
        {
            continue;
        }
        let peer_sequence = peer.publisher_list_sequence(publisher).unwrap_or_default();
        if peer_sequence >= collection.max_sequence {
            continue;
        }
        let messages = build_validator_list_collection_messages(
            &collection,
            peer_sequence,
            overlay::MAXIMUM_MESSAGE_SIZE,
        );
        // Match the reference empty-placeholder behavior: do not rebuild an
        // unsendable oversized collection for this peer on every refresh.
        peer.set_publisher_list_sequence(publisher, collection.max_sequence);
        for message in messages {
            peer.send(message.message);
            root.add_validator_list_suppression_peer(message.hash, peer.id());
        }
        root.add_validator_list_suppression_peer(hash, peer.id());
    }
}

/// Apply a received v2 collection through the shared ValidatorList state and
/// then run the bootstrap-owned UNL synchronization and v2 propagation.
fn apply_validator_list_collection_from_peer(
    root: &crate::ApplicationRoot,
    peer_id: overlay::PeerId,
    collection: &overlay::TmValidatorListCollection,
) {
    let Some((manifest, version, blobs)) = validator_list_collection_blobs(collection) else {
        return;
    };
    let hash = crate::validator::validator_list::validator_list_collection_hash(
        &manifest, version, &blobs,
    );
    let stats = root.apply_validator_lists_from_peer(
        peer_id,
        &manifest,
        version,
        &blobs,
        String::new(),
        hash,
    );
    synchronize_unl_blocked(root);
    broadcast_validator_list_collection(root, &stats, hash);
}

/// Atomically consume only bootstrap-owned validator queues, leaving every
/// unrelated inbound family to its designated consumer.
fn take_validator_list_inbound(
    overlay: &Arc<overlay::OverlayImpl>,
) -> (
    Vec<overlay::PeerMessage<overlay::TmManifests>>,
    Vec<overlay::PeerMessage<overlay::TmValidatorList>>,
    Vec<overlay::PeerMessage<overlay::TmValidatorListCollection>>,
) {
    overlay.queued_inbound().take_validator_messages()
}

/// Apply rippled's trust-first `TMManifests` admission rule. Trusted entries
/// never consume the untrusted-work budget, so they remain processable after
/// a peer has sent its 300th untrusted manifest.
fn manifest_rate_limit_policy(
    is_trusted: bool,
    untrusted_processed: &mut usize,
    max_untrusted_count: usize,
) -> Option<crate::state::manifest::ManifestRateLimitCapPolicy> {
    if is_trusted {
        return Some(crate::state::manifest::ManifestRateLimitCapPolicy::Uncapped);
    }
    if *untrusted_processed >= max_untrusted_count {
        return None;
    }
    *untrusted_processed += 1;
    Some(crate::state::manifest::ManifestRateLimitCapPolicy::Capped)
}

fn relay_accepted_manifest(disposition: crate::state::manifest::ManifestDisposition) -> bool {
    disposition == crate::state::manifest::ManifestDisposition::Accepted
}

/// Matches PeerImp::processLedgerRequest: every non-candidate request is
/// refused once the peer reaches the drop-send-queue threshold. A relay cookie
/// bypasses resource charging only; it does not bypass this overload gate.
fn get_ledger_send_queue_is_admissible(itype: i32, send_queue_depth: usize) -> bool {
    itype == 3 || send_queue_depth < overlay::DROP_SEND_QUEUE
}

fn serve_one_get_ledger_request(
    root: &crate::ApplicationRoot,
    overlay_rt: &Arc<crate::runtime::overlay_runtime::AppOverlayRuntime>,
    req: overlay::PeerMessage<overlay::TmGetLedger>,
    fetch_depth: u32,
) {
    use overlay::Overlay;

    let itype = req.message.itype;
    let serving_peer = overlay_rt.overlay().find_peer_by_short_id(req.peer_id);

    // `PeerImp::processLedgerRequest` charges every non-relayed request before
    // resolving it. Normal ledger requests additionally refuse local overload
    // for non-cluster peers; candidate requests retain rippled's exception.
    if req.message.request_cookie.is_none()
        && let Some(peer) = serving_peer.as_ref()
    {
        peer.charge(
            (*resource::FEE_MODERATE_BURDEN_PEER).clone(),
            "received get ledger request".to_owned(),
        );
    }
    if serving_peer
        .as_ref()
        .is_some_and(|peer| !get_ledger_send_queue_is_admissible(itype, peer.send_queue_size()))
    {
        return;
    }
    if itype != 3
        && root.load_fee_track_loaded_local()
        && serving_peer.as_ref().is_some_and(|peer| !peer.cluster())
    {
        return;
    }

    // `PeerImp::getLedger` selects by hash, then sequence, then ltCLOSED.
    let hash = if let Some(hash_bytes) = req.message.ledger_hash.as_deref() {
        match Uint256::from_slice(hash_bytes) {
            Some(h) => h,
            None => return,
        }
    } else if let Some(seq) = req.message.ledger_seq {
        // Seq-only request: look up hash from validated range.
        // rippled rejects sequences below getEarliestFetch() (PeerImp.cpp:3336).
        if let Some(lm_rt) = root.ledger_master_runtime() {
            let lm = lm_rt.ledger_master();
            if !sequence_is_fetchable_at_floor(seq, root.earliest_ledger_fetch(fetch_depth)) {
                return;
            }
            match lm.get_ledger_by_seq(seq, &ledger::NullLedgerJournal) {
                Some(ledger) if ledger.header().seq == seq => *ledger.header().hash.as_uint256(),
                _ => return,
            }
        } else {
            return;
        }
    } else if req.message.ltype == Some(2) {
        match root.closed_ledger() {
            Some(ledger) => *ledger.header().hash.as_uint256(),
            None => return,
        }
    } else {
        return;
    };

    let mut nodes: Vec<overlay::message::wire::TmLedgerNode> = Vec::new();

    // liTS_CANDIDATE (3) uses InboundTransactions, not LedgerMaster.
    // Handle it before the ledger lookup which would early-return for
    // tx-set hashes that aren't ledger hashes.
    if itype == 3 {
        let mut guard = root
            .inbound_transactions()
            .lock()
            .expect("inbound_transactions mutex");
        let set = guard.get_set(hash, false);
        if set.is_none() {
            drop(guard);
            // `PeerImp::getTxSet` relays an indirect miss exactly once. The
            // cookie identifies the requesting peer so the eventual reply
            // routes back without a second relay loop.
            if req.message.query_type.is_some() && req.message.request_cookie.is_none() {
                let mut relayed = req.message.clone();
                relayed.request_cookie = Some(req.peer_id as u64);
                if let Some(peer) = overlay_rt
                    .overlay()
                    .active_peers()
                    .into_iter()
                    .find(|peer| peer.id() != req.peer_id && peer.has_tx_set(hash))
                {
                    peer.send(overlay::Message::new(
                        overlay::ProtocolMessage::new(overlay::ProtocolPayload::GetLedger(relayed)),
                        None,
                    ));
                }
            }
            return;
        }
        drop(guard);
        let sync_tree = set.unwrap();
        let mut fetch = |_h: basics::sha_map_hash::SHAMapHash| -> Option<
            basics::memory::intrusive_pointer::SharedIntrusive<
                shamap::nodes::tree_node::SHAMapTreeNode,
            >,
        > { None };
        let requested_node_ids = &req.message.node_i_ds;
        let default_depth = if serving_peer
            .as_ref()
            .is_some_and(|peer| peer.is_high_latency())
        {
            2
        } else {
            1
        };
        let query_depth = req.message.query_depth.unwrap_or(default_depth);

        // Candidate sets follow the same requested-node traversal contract as
        // rippled: no root expansion shortcut, no transaction leaves, bounded
        // requested-node loop, and response limits applied during assembly.
        for node_id_bytes in requested_node_ids {
            if nodes.len() >= overlay::SOFT_MAX_REPLY_NODES {
                break;
            }
            let Some(node_id) = shamap::nodes::node_id::deserialize_shamap_node_id(node_id_bytes)
            else {
                continue;
            };
            let mut data: Vec<(shamap::nodes::node_id::SHAMapNodeId, Vec<u8>)> = Vec::new();
            if sync_tree
                .get_node_fat(node_id, &mut data, false, query_depth, &mut fetch)
                .is_ok()
            {
                for (nid, ndata) in data {
                    if nodes.len() >= HARD_MAX_REPLY_NODES {
                        break;
                    }
                    nodes.push(overlay::message::wire::TmLedgerNode {
                        nodeid: Some(nid.get_raw_string()),
                        nodedata: ndata,
                        reference: None,
                    });
                }
            }
            if nodes.len() >= HARD_MAX_REPLY_NODES {
                break;
            }
        }

        if nodes.is_empty() {
            tracing::warn!(target: "consensus", %hash, "liTS_CANDIDATE: serialization produced empty nodes");
            return;
        }

        let response_data = overlay::TmLedgerData {
            ledger_hash: hash.data().to_vec(),
            ledger_seq: 0,
            r#type: 3,
            nodes,
            request_cookie: req.message.request_cookie.map(|c| c as u32),
            error: None,
        };
        tracing::info!(target: "consensus",
            %hash,
            nodes_count = response_data.nodes.len(),
            first_node_data_len = response_data.nodes.first().map(|n| n.nodedata.len()).unwrap_or(0),
            "liTS_CANDIDATE: sending response (as type 3)"
        );
        let response =
            overlay::ProtocolMessage::new(overlay::ProtocolPayload::LedgerData(response_data));
        let message = overlay::Message::new(response, None);
        if let Some(peer) = overlay_rt.overlay().find_peer_by_short_id(req.peer_id) {
            peer.send(message);
        }
        return;
    }

    let Some(lm_rt) = root.ledger_master_runtime() else {
        return;
    };
    let lm = lm_rt.ledger_master();
    let earliest_fetch = root.earliest_ledger_fetch(fetch_depth);

    let ledger = lm
        .get_ledger_by_hash(basics::sha_map_hash::SHAMapHash::new(hash))
        .or_else(|| {
            root.closed_ledger()
                .filter(|ledger| ledger.header().hash.as_uint256() == &hash)
        });
    let Some(ledger) = ledger else {
        // `PeerImp::getLedger` relays an indirect miss only when it did not
        // already carry a cookie.
        if req.message.query_type.is_some() && req.message.request_cookie.is_none() {
            let mut relayed = req.message.clone();
            relayed.request_cookie = Some(req.peer_id as u64);
            if let Some(peer) = overlay_rt
                .overlay()
                .active_peers()
                .into_iter()
                .find(|peer| {
                    peer.id() != req.peer_id
                        && peer.has_ledger(hash, req.message.ledger_seq.unwrap_or_default())
                })
            {
                peer.send(overlay::Message::new(
                    overlay::ProtocolMessage::new(overlay::ProtocolPayload::GetLedger(relayed)),
                    None,
                ));
            }
        }
        return;
    };
    // Apply the same earliest-fetch retention guard after every selector
    // resolves: hash, sequence, and ltCLOSED all share this PeerImp rule.
    if !sequence_is_fetchable_at_floor(ledger.header().seq, earliest_fetch) {
        return;
    }
    if req
        .message
        .ledger_seq
        .is_some_and(|sequence| sequence != ledger.header().seq)
    {
        if req.message.request_cookie.is_none()
            && let Some(peer) = serving_peer.as_ref()
        {
            peer.charge(
                (*resource::FEE_MALFORMED_REQUEST).clone(),
                "TMGetLedger resolved ledger sequence mismatch".to_owned(),
            );
        }
        return;
    }

    match itype {
        0 => {
            // li_BASE: header + state root + tx root (matching rippled sendLedgerBase)
            let header_data = protocol::serialize_ledger_header(&ledger.header(), false);
            nodes.push(overlay::message::wire::TmLedgerNode {
                nodeid: None,
                nodedata: header_data,
                reference: None,
            });
            // State map root
            if !ledger.header().account_hash.is_zero() {
                if let Ok(root_data) = ledger.state_map().serialize_root() {
                    nodes.push(overlay::message::wire::TmLedgerNode {
                        nodeid: None,
                        nodedata: root_data,
                        reference: None,
                    });
                }
            }
            // Tx map root
            if !ledger.header().tx_hash.is_zero() {
                if let Ok(root_data) = ledger.tx_map().serialize_root() {
                    nodes.push(overlay::message::wire::TmLedgerNode {
                        nodeid: None,
                        nodedata: root_data,
                        reference: None,
                    });
                }
            }
        }
        1 | 2 => {
            // liTX_NODE (1) or liAS_NODE (2): serve requested SHAMap nodes
            let map = if itype == 1 {
                ledger.tx_map()
            } else {
                ledger.state_map()
            };
            let fat_leaves = true; // rippled: fatLeaves{true} for both liTX_NODE and liAS_NODE
            let default_depth = if serving_peer
                .as_ref()
                .is_some_and(|peer| peer.is_high_latency())
            {
                2
            } else {
                1
            };
            let depth = req.message.query_depth.unwrap_or(default_depth); // rippled: kMaxQueryDepth=3

            // rippled kSoftMaxReplyNodes = 8192: stop processing requested
            // node IDs once we've accumulated this many output nodes.
            const SOFT_MAX_REPLY_NODES: usize = 8192;

            for node_id_bytes in &req.message.node_i_ds {
                if nodes.len() >= SOFT_MAX_REPLY_NODES {
                    break;
                }
                let Some(node_id) =
                    shamap::nodes::node_id::deserialize_shamap_node_id(node_id_bytes)
                else {
                    continue;
                };
                let mut data: Vec<(shamap::nodes::node_id::SHAMapNodeId, Vec<u8>)> = Vec::new();
                let mut fetch = |_h: basics::sha_map_hash::SHAMapHash| -> Option<
                    basics::memory::intrusive_pointer::SharedIntrusive<
                        shamap::nodes::tree_node::SHAMapTreeNode,
                    >,
                > { None };
                if map
                    .get_node_fat(node_id, &mut data, fat_leaves, depth, &mut fetch)
                    .is_ok()
                {
                    for (nid, ndata) in &data {
                        nodes.push(overlay::message::wire::TmLedgerNode {
                            nodeid: Some(nid.get_raw_string()),
                            nodedata: ndata.clone(),
                            reference: None,
                        });
                        if nodes.len() >= HARD_MAX_REPLY_NODES {
                            break;
                        }
                    }
                }
                if nodes.len() >= HARD_MAX_REPLY_NODES {
                    break;
                }
            }
        }
        _ => return,
    }

    if nodes.is_empty() {
        return;
    }

    let response = overlay::ProtocolMessage::new(overlay::ProtocolPayload::LedgerData(
        overlay::TmLedgerData {
            ledger_hash: hash.data().to_vec(),
            ledger_seq: ledger.header().seq,
            r#type: itype,
            nodes,
            request_cookie: req.message.request_cookie.map(|c| c as u32),
            error: None,
        },
    ));
    let message = overlay::Message::new(response, None);
    if let Some(peer) = overlay_rt.overlay().find_peer_by_short_id(req.peer_id) {
        peer.send(message);
    }
}

/// FetchPack requests use dedicated PeerImp/JtPack admission, rather than the
/// generic `JtLedgerReq` node-store route. This mirrors the reference limits:
/// never queue under local load, when the validated ledger is old, or once the
/// pack queue already contains more than ten waiting jobs.
const FETCH_PACK_MAX_QUEUED_JOBS: usize = 10;
const FETCH_PACK_MAX_VALIDATED_LEDGER_AGE: Duration = Duration::from_secs(40);
const FETCH_PACK_REQUEST_STALE_AFTER: Duration = Duration::from_secs(1);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FetchPackAdmission {
    Busy,
    Malformed,
    Accepted(Uint256),
}

fn classify_fetch_pack_request(
    loaded_local: bool,
    validated_ledger_age: Duration,
    queued_pack_jobs: usize,
    ledger_hash: Option<&[u8]>,
) -> FetchPackAdmission {
    if loaded_local
        || validated_ledger_age > FETCH_PACK_MAX_VALIDATED_LEDGER_AGE
        || queued_pack_jobs > FETCH_PACK_MAX_QUEUED_JOBS
    {
        return FetchPackAdmission::Busy;
    }
    ledger_hash
        .and_then(Uint256::from_slice)
        .map_or(FetchPackAdmission::Malformed, FetchPackAdmission::Accepted)
}

fn fetch_pack_failure_charge(
    error: ledger::FetchPackBuildError,
) -> Option<(resource::Charge, &'static str)> {
    match error {
        ledger::FetchPackBuildError::Stale => None,
        ledger::FetchPackBuildError::RequestedLedgerMissing
        | ledger::FetchPackBuildError::RequestedLedgerPredecessorMissing
        | ledger::FetchPackBuildError::Traversal => Some((
            (*resource::FEE_REQUEST_NO_REPLY).clone(),
            "get_object ledger",
        )),
        ledger::FetchPackBuildError::RequestedLedgerOpen => Some((
            (*resource::FEE_MALFORMED_REQUEST).clone(),
            "get_object ledger open",
        )),
        ledger::FetchPackBuildError::RequestedLedgerTooEarly => Some((
            (*resource::FEE_MALFORMED_REQUEST).clone(),
            "get_object ledger early",
        )),
    }
}

/// Execute a previously admitted FetchPack request. The peer is looked up only
/// after cheap stale/load checks, which is the Rust equivalent of rippled's
/// weak peer capture: a disconnected peer cannot keep an expensive map walk
/// alive or receive a stale response.
fn serve_fetch_pack_request(
    root: &crate::ApplicationRoot,
    overlay_rt: &Arc<crate::runtime::overlay_runtime::AppOverlayRuntime>,
    peer_id: overlay::PeerId,
    have_hash: Uint256,
    issued_at: std::time::Instant,
    fetch_depth: u32,
) {
    use overlay::Overlay;

    if issued_at.elapsed() > FETCH_PACK_REQUEST_STALE_AFTER
        || root.load_fee_track_loaded_local()
        || root.validated_ledger_age() > FETCH_PACK_MAX_VALIDATED_LEDGER_AGE
    {
        return;
    }
    let Some(peer) = overlay_rt.overlay().find_peer_by_short_id(peer_id) else {
        return;
    };
    let Some(lm_rt) = root.ledger_master_runtime() else {
        return;
    };
    let lm = lm_rt.ledger_master();
    let Some(node_fetcher) = root.node_fetcher_from_store() else {
        peer.charge(
            (*resource::FEE_REQUEST_NO_REPLY).clone(),
            "get_object ledger node store unavailable".to_owned(),
        );
        return;
    };
    let deadline = issued_at + FETCH_PACK_REQUEST_STALE_AFTER;
    let objects = match lm.make_fetch_pack_with_fetcher(
        have_hash,
        root.earliest_ledger_fetch(fetch_depth),
        deadline,
        node_fetcher.as_ref(),
    ) {
        Ok(objects) => objects,
        Err(error) => {
            let Some((fee, context)) = fetch_pack_failure_charge(error) else {
                return;
            };
            peer.charge(fee, context.to_owned());
            return;
        }
    };
    if objects.is_empty() {
        return;
    }

    let object_count = objects.len();
    let response_objects = objects
        .into_iter()
        .map(|object| overlay::message::wire::TmIndexedObject {
            hash: Some(object.hash.data().to_vec()),
            node_id: None,
            index: None,
            data: Some(object.data),
            ledger_seq: Some(object.ledger_seq),
        })
        .collect();
    tracing::info!(target: "consensus", peer_id, objects = object_count,
        "Serving ledger-master fetch pack to peer");

    peer.send(overlay::Message::new(
        overlay::ProtocolMessage::new(overlay::ProtocolPayload::GetObjects(
            overlay::TmGetObjectByHash {
                r#type: overlay::message::wire::tm_get_object_by_hash::ObjectType::OtFetchPack
                    as i32,
                query: false,
                ledger_hash: Some(have_hash.data().to_vec()),
                fat: None,
                objects: response_objects,
            },
        )),
        None,
    ));
}

// --- GetObjectByHash rate limiting constants (matching rippled Tuning.h) ---

/// Hard ceiling: reject requests asking for more than this many objects.
const HARD_MAX_REPLY_NODES: usize = 12_288;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GenericGetObjectAdmission {
    MalformedLedgerHash,
    Oversized,
    Accepted,
}

/// All PeerImp TMGetObjectByHash query types share this overload gate before
/// their FetchPack, transaction-reduction, or generic serving branch.
fn get_object_query_send_queue_is_admissible(send_queue_depth: usize) -> bool {
    send_queue_depth < overlay::DROP_SEND_QUEUE
}

/// `PeerImp::doTransactions` rejects an oversized batch or a malformed/missing
/// hash as a complete request failure, rather than returning a partial batch.
fn transaction_object_request_is_admissible(
    objects: &[overlay::message::wire::TmIndexedObject],
) -> bool {
    objects.len() <= overlay::slot::MAX_TX_QUEUE_SIZE
        && objects.iter().all(|object| {
            object
                .hash
                .as_deref()
                .and_then(Uint256::from_slice)
                .is_some()
        })
}

/// Match the cheap PeerImp admission checks before queueing any NodeStore work.
/// Object hashes are intentionally validated by the worker and count as
/// misses; only the optional ledger hash is a request-level structural field.
fn classify_generic_get_object_request(
    ledger_hash: Option<&[u8]>,
    requested: usize,
) -> GenericGetObjectAdmission {
    if ledger_hash.is_some_and(|hash| Uint256::from_slice(hash).is_none()) {
        GenericGetObjectAdmission::MalformedLedgerHash
    } else if requested > HARD_MAX_REPLY_NODES {
        GenericGetObjectAdmission::Oversized
    } else {
        GenericGetObjectAdmission::Accepted
    }
}

/// First N objects per request are free (no cost charged).
const FREE_OBJECTS_PER_REQUEST: u32 = 16;

/// Cost per billable lookup that hits the cache/node store.
const COST_PER_LOOKUP_HIT: u32 = 1;

/// Cost per billable lookup that misses (not found in node store).
const COST_PER_LOOKUP_MISS: u32 = 8;

/// Size band boundary: requests with ≤64 objects are "small".
const BAND_SMALL_MAX: usize = 64;

/// Size band boundary: requests with ≤1024 objects are "medium".
const BAND_MEDIUM_MAX: usize = 1024;

/// Surcharge for small requests (none).
const COST_BAND_SMALL: u32 = 0;

/// Surcharge for medium-sized requests.
const COST_BAND_MEDIUM: u32 = 100;

/// Surcharge for large requests (>1024 objects).
const COST_BAND_LARGE: u32 = 1000;

fn requested_transaction_envelope(
    transaction: &crate::Transaction,
    timestamp: u64,
) -> overlay::TmTransaction {
    overlay::TmTransaction {
        raw_transaction: transaction
            .get_s_transaction()
            .get_serializer()
            .data()
            .to_vec(),
        // PeerImp sends tsCURRENT only for included transactions; every
        // other cached state is tsNEW in a requested transaction batch.
        status: if transaction.get_status() == crate::TransStatus::INCLUDED {
            2
        } else {
            1
        },
        receive_timestamp: Some(timestamp),
        deferred: Some(transaction.get_submit_result().queued),
    }
}

/// Serve a transaction-reduction object query through TMTransactions, matching
/// PeerImp::doTransactions. Any cache miss invalidates the whole request and
/// emits no partial reply.
fn serve_requested_transactions(
    root: &crate::ApplicationRoot,
    overlay_rt: &Arc<crate::runtime::overlay_runtime::AppOverlayRuntime>,
    req: &overlay::PeerMessage<overlay::TmGetObjectByHash>,
) {
    use overlay::Overlay;

    let Some(peer) = overlay_rt.overlay().find_peer_by_short_id(req.peer_id) else {
        return;
    };
    if !peer.tx_reduce_relay_enabled()
        || !transaction_object_request_is_admissible(&req.message.objects)
    {
        peer.charge(
            (*resource::FEE_MALFORMED_REQUEST).clone(),
            "TMGetObjectByHash transactions malformed".to_owned(),
        );
        return;
    }

    let timestamp = u64::from(root.current_network_time_seconds());
    let mut transactions = Vec::with_capacity(req.message.objects.len());
    for object in &req.message.objects {
        let hash = Uint256::from_slice(
            object
                .hash
                .as_deref()
                .expect("transaction request was prevalidated"),
        )
        .expect("transaction request hash was prevalidated");
        let Some(transaction) = root.fetch_cached_transaction(&hash) else {
            peer.charge(
                (*resource::FEE_MALFORMED_REQUEST).clone(),
                "TMGetObjectByHash transaction not found".to_owned(),
            );
            return;
        };
        let transaction = transaction
            .lock()
            .expect("canonical transaction mutex must not be poisoned");
        transactions.push(requested_transaction_envelope(&transaction, timestamp));
    }

    if !transactions.is_empty() {
        peer.send(overlay::Message::new(
            overlay::ProtocolMessage::new(overlay::ProtocolPayload::Transactions(
                overlay::TmTransactions { transactions },
            )),
            None,
        ));
    }
}

/// Serve a generic GetObjectByHash query from a peer (matching rippled processGetObjectByHash).
///
/// Looks up each requested hash in the node store, tracks hits/misses, applies
/// differential pricing, and sends a reply. Oversized requests are rejected
/// immediately. Excessively costly requests charge the peer.
fn serve_get_object_by_hash_request(
    root: &crate::ApplicationRoot,
    overlay_rt: &Arc<crate::runtime::overlay_runtime::AppOverlayRuntime>,
    req: &overlay::PeerMessage<overlay::TmGetObjectByHash>,
) {
    use overlay::Overlay;

    let msg = &req.message;
    let requested = msg.objects.len();

    // The router performs request-level admission before queueing. Preserve
    // this defensive worker gate for direct callers without reclassifying it.
    if !matches!(
        classify_generic_get_object_request(msg.ledger_hash.as_deref(), requested),
        GenericGetObjectAdmission::Accepted
    ) {
        return;
    }

    let node_store = root.node_store().clone();

    let mut reply_objects: Vec<overlay::message::wire::TmIndexedObject> = Vec::new();
    let mut hits: u32 = 0;
    let mut misses: u32 = 0;

    let iter_limit = requested.min(HARD_MAX_REPLY_NODES);
    for obj in msg.objects.iter().take(iter_limit) {
        let Some(hash_bytes) = obj.hash.as_deref() else {
            misses += 1;
            continue;
        };
        let Some(hash) = Uint256::from_slice(hash_bytes) else {
            misses += 1;
            continue;
        };

        let ledger_seq = obj.ledger_seq.unwrap_or(0);
        let fetched = node_store.as_ref().and_then(|node_store| match node_store {
            crate::SHAMapStoreNodeStore::Single(database) => {
                database.fetch_node_object(&hash, ledger_seq, FetchType::Synchronous, false)
            }
            crate::SHAMapStoreNodeStore::Rotating(database) => {
                database.fetch_node_object(&hash, ledger_seq, FetchType::Synchronous, false)
            }
        });

        if let Some(node_object) = fetched {
            hits += 1;
            reply_objects.push(overlay::message::wire::TmIndexedObject {
                hash: Some(hash.data().to_vec()),
                node_id: None,
                index: obj.node_id.clone(),
                data: Some(node_object.data().clone()),
                ledger_seq: obj.ledger_seq,
            });
        } else {
            misses += 1;
        }
    }

    // Compute differential cost (matching rippled computeGetObjectByHashFee).
    let billable = (requested as u32).saturating_sub(FREE_OBJECTS_PER_REQUEST);
    let billable_misses = misses.min(billable);
    let billable_hits = billable.saturating_sub(billable_misses);

    let size_band = if requested > BAND_MEDIUM_MAX {
        COST_BAND_LARGE
    } else if requested > BAND_SMALL_MAX {
        COST_BAND_MEDIUM
    } else {
        COST_BAND_SMALL
    };

    let cost =
        billable_hits * COST_PER_LOOKUP_HIT + billable_misses * COST_PER_LOOKUP_MISS + size_band;

    if cost > resource::DROP_THRESHOLD as u32 {
        tracing::warn!(target: "overlay",
            peer_id = req.peer_id,
            requested,
            hits,
            misses,
            cost,
            threshold = resource::DROP_THRESHOLD,
            "GetObjectByHash: cost exceeds drop threshold, charging peer"
        );
        if let Some(peer) = overlay_rt.overlay().find_peer_by_short_id(req.peer_id) {
            peer.charge(
                resource::Charge::new(cost as i32, "GetObjectByHash excessive cost"),
                "GetObjectByHash cost exceeded drop threshold".to_owned(),
            );
        }
    } else if cost > 0 {
        // Charge the peer with the dynamic lookup cost. The admission-time
        // moderate burden was already applied after successful job queueing.
        if let Some(peer) = overlay_rt.overlay().find_peer_by_short_id(req.peer_id) {
            peer.charge(
                resource::Charge::new(cost as i32, "GetObjectByHash differential"),
                "processed get object by hash request".to_owned(),
            );
        }
    }

    // PeerImp always sends the query-shaped reply, including an empty object
    // list for an all-miss request. The empty reply terminates remote retry
    // state without making the requester infer a transport failure.

    tracing::trace!(target: "overlay",
        peer_id = req.peer_id,
        found = reply_objects.len(),
        requested,
        cost,
        "GetObjectByHash: serving reply"
    );

    let reply = overlay::TmGetObjectByHash {
        r#type: msg.r#type,
        query: false,
        ledger_hash: msg.ledger_hash.clone(),
        fat: msg.fat,
        objects: reply_objects,
    };

    let response = overlay::ProtocolMessage::new(overlay::ProtocolPayload::GetObjects(reply));
    let message = overlay::Message::new(response, None);
    if let Some(peer) = overlay_rt.overlay().find_peer_by_short_id(req.peer_id) {
        peer.send(message);
    }
}

fn ensure_descriptor_budget(required: usize) -> Result<(), String> {
    let required = required.max(1024) as u64;
    let provider = SystemDescriptorLimitProvider;
    if adjust_descriptor_limit(required, &provider) {
        Ok(())
    } else {
        Err(format!(
            "Insufficient number of file descriptors: {required} are needed"
        ))
    }
}

fn spawn_shutdown_watcher(
    runtime: Arc<MainRuntime>,
    stop_requested: Arc<AtomicBool>,
) -> std::thread::JoinHandle<()> {
    std::thread::spawn(move || {
        // Docker's `stop` sends SIGTERM before it escalates to SIGKILL. Keep
        // this aligned with rippled's ApplicationImp::setup, which observes
        // both SIGINT and SIGTERM and routes either through signalStop.
        #[cfg(unix)]
        let mut terminate = runtime.root().basic_app().block_on(async {
            tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())
                .expect("SIGTERM handler must install")
        });

        loop {
            if stop_requested.load(Ordering::Acquire) {
                return;
            }

            let shutdown_signal_seen = runtime.root().basic_app().block_on(async {
                #[cfg(unix)]
                {
                    tokio::select! {
                        result = tokio::signal::ctrl_c() => result.is_ok(),
                        _ = terminate.recv() => true,
                        _ = tokio::time::sleep(Duration::from_millis(100)) => false,
                    }
                }

                #[cfg(not(unix))]
                {
                    tokio::select! {
                        result = tokio::signal::ctrl_c() => result.is_ok(),
                        _ = tokio::time::sleep(Duration::from_millis(100)) => false,
                    }
                }
            });

            if stop_requested.load(Ordering::Acquire) {
                return;
            }

            if shutdown_signal_seen {
                let _ = runtime.signal_stop("received shutdown signal");
                return;
            }
        }
    })
}

fn bootstrap_shamap_store_if_configured(
    root: &mut ApplicationRoot,
    config: &BasicConfig,
    standalone: bool,
    ledger_history: u32,
    io_threads: usize,
) -> Result<Option<PendingProductionSHAMapStore>, String> {
    if !config.exists("node_db") {
        return Ok(None);
    }

    let manager: Arc<dyn nodestore::Manager> = Arc::new(ManagerImp::new());
    let scheduler: Arc<dyn nodestore::Scheduler> = Arc::new(root.node_store_scheduler().clone());
    let journal: Arc<dyn nodestore::NodeStoreJournal> = root.get_journal("NodeStore");
    let bootstrap = bootstrap_shamap_store(
        config,
        standalone,
        ledger_history,
        io_threads.max(1) as i32,
        40_000,
        64,
        2,
        manager.as_ref(),
        Arc::clone(&scheduler),
        Arc::clone(&journal),
    )?;
    let _ = bootstrap.attach_node_store(root);
    let backend_factory = Arc::new(crate::ConfiguredSHAMapStoreBackendFactory::new(
        manager,
        bootstrap.effective_node_db_config.clone(),
        40_000,
        scheduler,
        journal,
    ));
    Ok(Some(PendingProductionSHAMapStore {
        bootstrap,
        backend_factory,
    }))
}

fn attach_production_shamap_store_runtime(
    root: &mut ApplicationRoot,
    pending: Option<PendingProductionSHAMapStore>,
) -> Result<(), String> {
    let Some(pending) = pending else {
        return Ok(());
    };
    let PendingProductionSHAMapStore {
        bootstrap,
        backend_factory,
    } = pending;

    // A single-backend store has no online-delete worker. Retain the small
    // inert runtime for that configuration rather than inventing rotation
    // capabilities which the backend cannot provide.
    if bootstrap.store.delete_interval() == 0 {
        let component = Arc::new(SHAMapStoreComponent::new(
            bootstrap.store,
            Box::new(BootstrapSHAMapStoreRuntime::default()),
            bootstrap.state_db,
        ));
        let _ = root.attach_shamap_store_component(component);
        return Ok(());
    }

    let crate::SHAMapStoreNodeStore::Rotating(database) = bootstrap.node_store else {
        return Err("online_delete requires a rotating NodeStore backend".to_owned());
    };
    let ledger_master_runtime = root
        .ledger_master_runtime()
        .ok_or_else(|| "online_delete requires LedgerMaster runtime".to_owned())?;
    let ledger_master = ledger_master_runtime.ledger_master();
    let node_family = root
        .node_family()
        .ok_or_else(|| "online_delete requires the application NodeFamily".to_owned())?;
    let tree_cache = root
        .shared_tree_cache_arc()
        .map(Arc::clone)
        .ok_or_else(|| "online_delete requires the shared TreeNode cache".to_owned())?;
    let full_below = root
        .node_family_full_below_cache()
        .ok_or_else(|| "online_delete requires the NodeFamily FullBelow cache".to_owned())?;
    let node_family_runtime = Arc::new(BootstrapNodeFamilyCacheRuntime {
        node_family,
        tree_cache,
        full_below,
    });
    let node_store_runtime = Arc::new(BootstrapRotatingNodeStoreRuntime {
        database,
        ledger_master_runtime,
        owner_wake: root.consensus_wake_callback(),
    });
    let relational = root
        .relational_database()
        .as_ref()
        .map(|database| Arc::clone(database) as Arc<dyn crate::SHAMapStoreRelationalRuntime>);
    let health = Arc::new(crate::SharedSHAMapStoreHealthState::new_with_app_state(
        root.shared_time_keeper(),
        root.network_ops_state(),
        root.ledger_master_state(),
    ));
    let runtime = crate::SHAMapStoreAppRuntime::new_with_health_state(
        ledger_master,
        node_family_runtime,
        root.transaction_master(),
        node_store_runtime,
        backend_factory,
        relational,
        Arc::new(crate::ValidatedLedgerCopyRuntime),
        Arc::clone(&health),
    );
    let component = Arc::new(SHAMapStoreComponent::new(
        bootstrap.store,
        Box::new(runtime),
        bootstrap.state_db,
    ));
    let service = Arc::new(crate::SHAMapStoreService::new(component, health));
    let _ = root.attach_shamap_store_service(service);
    Ok(())
}

fn attach_relational_database_if_configured(
    root: &mut ApplicationRoot,
    config: &BasicConfig,
    options: &AppBootstrapOptions,
    ledger_history: u32,
) -> Result<bool, String> {
    if !config.exists("database_path") {
        return Ok(false);
    }

    let setup = build_database_con_setup(
        config,
        to_core_startup_type(options.start_type),
        options.standalone,
        ledger_history,
    )?;
    if !setup.data_dir.as_os_str().is_empty() {
        if let Err(error) = fs::create_dir_all(&setup.data_dir) {
            let is_existing_dir = setup.data_dir.is_dir();
            if !is_existing_dir {
                return Err(format!(
                    "failed to create bootstrap database directory {}: {error}",
                    setup.data_dir.display()
                ));
            }
        }
    }
    let ledger_db = Arc::new(DatabaseCon::new_from_setup(
        &setup,
        LEDGER_DB_NAME,
        &setup.lgr_pragma,
        LEDGER_DB_INIT,
    )?);
    let transaction_db = Arc::new(DatabaseCon::new_from_setup(
        &setup,
        TRANSACTION_DB_NAME,
        &setup.tx_pragma,
        TRANSACTION_DB_INIT,
    )?);
    let relational = Arc::new(crate::SqliteSHAMapStoreRelational::new(
        ledger_db,
        Some(transaction_db),
        true,
        100,
        Duration::from_millis(0),
    ));
    let _ = root.attach_relational_database(Some(relational));

    // Open rdb::LedgerDb for header persistence (compatibility: the reference source Ledgers table).
    // Used on restart to load the last validated ledger without peer re-acquisition.
    let rdb_path = setup.data_dir.join("ledger_headers.db");
    tracing::info!(target: "ledger",
        "[bootstrap] opening ledger_headers.db at {}",
        rdb_path.display()
    );
    match rdb::LedgerDb::open(&rdb_path) {
        Ok(db) => {
            root.attach_ledger_db(Some(std::sync::Arc::new(db)));
        }
        Err(e) => {
            tracing::info!(target: "ledger", "[bootstrap] failed to open ledger_headers.db: {e}");
        }
    }

    Ok(true)
}

fn default_job_queue_threads(config: &BasicConfig, standalone: bool) -> usize {
    // Matches rippled Application.cpp JobQueue construction: standalone uses
    // one worker; otherwise medium/default nodes use 2 + min(cores, 4), with
    // larger nodes receiving the same documented escalation.
    if standalone {
        return 1;
    }
    let cores = std::thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1);
    let configured_node_size = configured_node_size_from_config(config);
    let node_size = configured_node_size.as_deref();
    match node_size {
        Some("huge") if cores >= 16 => 6 + cores.min(8),
        Some("large") if cores >= 8 => 4 + cores.min(6),
        _ => 2 + cores.min(4),
    }
}

fn node_db_fast_load(config: &BasicConfig) -> bool {
    let section = config.section("node_db");
    section
        .get::<bool>("fast_load")
        .ok()
        .flatten()
        .or_else(|| {
            section
                .get::<i32>("fast_load")
                .ok()
                .flatten()
                .map(|value| value != 0)
        })
        .unwrap_or(false)
}

fn configured_node_size_from_config(config: &BasicConfig) -> Option<String> {
    if !config.exists("node_size") {
        return None;
    }

    let section = config.section("node_size");
    match section.values() {
        [node_size] => {
            let node_size = node_size.trim().to_ascii_lowercase();
            match node_size.as_str() {
                "tiny" | "small" | "medium" | "large" | "huge" => Some(node_size),
                _ => None,
            }
        }
        values => {
            tracing::warn!(
                "Section 'node_size': requires 1 line not {} lines.",
                values.len()
            );
            None
        }
    }
}

fn attach_bootstrap_node_family(root: &mut ApplicationRoot, node_size: Option<&str>) {
    if let Some(node_store) = root.node_store().clone() {
        let profile = crate::NodeSizeResourceProfile::for_node_size(node_size);
        // rippled has ONE TreeNodeCache shared between NodeFamily and all
        // InboundLedger acquisitions (Application.cpp:236, InboundLedger.cpp:236,
        // SHAMap.cpp:1156,1168). Create it here and publish as shared_tree_cache
        // so acquisitions reuse the same instance.
        let tree_cache = Arc::new(TreeNodeCache::new(
            "tree-node-cache",
            profile.tree_cache_size,
            time::Duration::seconds(profile.tree_cache_age_seconds),
            MonotonicClock::default(),
        ));
        root.attach_shared_tree_cache(Arc::clone(&tree_cache));
        let family = crate::NodeFamily::new_with_owned_full_below_cache(
            tree_cache,
            1,
            profile.full_below_target_size,
            time::Duration::seconds(profile.full_below_expiration_seconds),
            BootstrapNodeStoreFetcher::new(node_store),
            NullMissingNodeReporter,
        );
        let _ = root.attach_node_family(Arc::new(family));
        let _ = root.wire_node_family_reset();
        return;
    }

    let _ = root.attach_default_node_family();
}

fn initialize_startup_ledger_state(
    root: &ApplicationRoot,
    options: &AppBootstrapOptions,
    config: &BasicConfig,
) -> Result<(), String> {
    match options.start_type {
        StartUpType::Load => match load_startup_ledger_from_storage(root, options) {
            Ok(()) => Ok(()),
            Err(error) if node_db_fast_load(config) => {
                tracing::warn!(target: "bootstrap", %error,
                    "fast_load durable ledger unavailable; falling back to genesis startup");
                // `fast_load` changes the effective startup type to `Load`, but
                // rippled's failure branch calls startGenesisLedger(), not the
                // synthetic Load placeholder. Select Normal only for the seed
                // operation so genesis receives its master AccountRoot and
                // setup entries while the application retains Load's original
                // need-network-ledger semantics.
                let mut genesis_options = options.clone();
                genesis_options.start_type = StartUpType::Normal;
                seed_startup_ledger_state(root, &genesis_options, config)
            }
            Err(error) => Err(error),
        },
        StartUpType::Replay => match replay_startup_ledger_from_storage(
            root,
            options.start_ledger.as_deref(),
            options.trap_tx_hash,
        )? {
            ReplayStartupResult::Complete => Ok(()),
            ReplayStartupResult::ParentIncomplete(pending) if root.standalone() => Err(format!(
                "Replay parent ledger {} is incomplete in local NodeStore; standalone mode cannot acquire {}",
                pending.parent_seq, pending.parent_hash
            )),
            ReplayStartupResult::ParentIncomplete(pending) => {
                tracing::warn!(target: "bootstrap",
                    parent_seq = pending.parent_seq,
                    parent_hash = %pending.parent_hash,
                    "replay parent is incomplete; deferring replay until inbound history acquisition persists it"
                );
                root.defer_replay_startup(pending);
                Ok(())
            }
        },
        StartUpType::LoadFile => load_startup_ledger_from_file(root, options),
        StartUpType::Network => {
            if !root.config().standalone {
                // Match rippled's independent network-startup latch. Operating
                // mode changes do not set it; a real LCL switch/publication
                // clears it later.
                root.set_need_network_ledger(true);
            }
            seed_startup_ledger_state(root, options, config)
        }
        StartUpType::Normal => {
            // Matches rippled Application.cpp normal startup branch: Normal
            // falls through to startGenesisLedger(). Durable getLastFullLedger
            // recovery is reserved for explicit Load/LoadFile/Replay modes.
            // NuDB remains attached and available for later node/history
            // acquisition; this changes startup selection, not retention.
            seed_startup_ledger_state(root, options, config)
        }
        StartUpType::Fresh | StartUpType::Snapshot => {
            // Rippled parity: --start (Fresh) does NOT set need_network_ledger.
            // Only explicit Network mode requires network-ledger acquisition
            // at startup; Normal begins from genesis like rippled.
            seed_startup_ledger_state(root, options, config)
        }
    }
}

// Unwired startup history-rehydration helper, retained for the M6-E
// `need_network_ledger` / history audit; removed in the M7 compatibility sweep
// if still unused.
#[allow(dead_code)]
fn rehydrate_configured_history(root: &ApplicationRoot, history_depth: u32) -> Result<(), String> {
    if history_depth == 0 {
        return Ok(());
    }

    let Some(latest) = root.closed_ledger().or_else(|| root.validated_ledger()) else {
        return Ok(());
    };
    let latest_seq = latest.header().seq;
    if latest_seq <= 1 {
        return Ok(());
    }
    let Some(relational) = root.relational_database().as_ref().map(Arc::clone) else {
        return Ok(());
    };
    let Some(node_store) = root.node_store().clone() else {
        return Ok(());
    };
    let Some(ledger_master_runtime) = root.ledger_master_runtime() else {
        return Ok(());
    };

    let provider = BootstrapLedgerDbProvider::new(relational);
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "app-bootstrap-history-loader",
            256,
            time::Duration::seconds(30),
            MonotonicClock::default(),
        )),
        NullFullBelowCache::new(0),
        BootstrapNodeStoreFetcher::new(node_store),
        NullMissingNodeReporter,
    );
    let journal = BootstrapLedgerJournal;
    let config = LedgerConfig::default();
    let earliest = if history_depth == u32::MAX {
        1
    } else {
        latest_seq.saturating_sub(history_depth).max(1)
    };

    let master = ledger_master_runtime.ledger_master();
    let mut child = latest;
    for seq in (earliest..latest_seq).rev() {
        let Some(mut ledger) = load_by_index(seq, false, &journal, &config, &family, &provider)
            .map_err(|error| format!("history ledger {seq} load failed: {error:?}"))?
        else {
            break;
        };
        ledger
            .finish_load_by_index_or_hash(&journal)
            .map_err(|error| format!("history ledger {seq} setup failed: {error:?}"))?;
        if ledger.header().hash != child.header().parent_hash {
            tracing::warn!(target: "bootstrap", seq,
                expected = %child.header().parent_hash,
                actual = %ledger.header().hash,
                "stopping history rehydration at a non-contiguous persisted ledger");
            break;
        }

        let ledger = root.ledger_with_node_fetcher(Arc::new(ledger));
        master.ledger_history().insert(Arc::clone(&ledger), true);
        master.mark_ledger_complete(seq);
        child = ledger;
    }

    let range = master.complete_ledgers();
    if !range.empty() {
        root.set_status_rpc_complete_ledgers(Some(range.to_string()));
    }
    Ok(())
}

fn load_startup_ledger_from_storage(
    root: &ApplicationRoot,
    options: &AppBootstrapOptions,
) -> Result<(), String> {
    let Some(ledger_master_runtime) = root.ledger_master_runtime() else {
        return Err("Load startup requires an attached LedgerMaster runtime".to_owned());
    };
    let loaded = load_complete_ledger_from_storage(
        root,
        options.start_ledger.as_deref(),
        "app-bootstrap-ledger-loader",
    )?
    .ok_or_else(|| "Requested startup ledger was not found in local storage".to_owned())?;

    hydrate_loaded_ledger(
        root,
        Arc::new(loaded),
        ledger_master_runtime.ledger_master(),
    )?;
    Ok(())
}

fn load_complete_ledger_from_storage(
    root: &ApplicationRoot,
    requested: Option<&str>,
    cache_name: &'static str,
) -> Result<Option<Ledger>, String> {
    let Some(relational) = root.relational_database().as_ref().map(Arc::clone) else {
        return Err(
            "Storage ledger load requires an attached relational ledger database".to_owned(),
        );
    };
    let Some(node_store) = root.node_store().clone() else {
        return Err("Storage ledger load requires an attached NodeStore".to_owned());
    };

    let provider = BootstrapLedgerDbProvider::new(relational);
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            cache_name,
            8,
            time::Duration::seconds(1),
            MonotonicClock::default(),
        )),
        NullFullBelowCache::new(0),
        BootstrapNodeStoreFetcher::new(node_store),
        NullMissingNodeReporter,
    );
    let journal = BootstrapLedgerJournal;
    let config = LedgerConfig::default();

    let mut loaded = load_bootstrap_ledger(requested, &journal, &config, &family, &provider)?;
    let Some(mut loaded) = loaded.take() else {
        return Ok(None);
    };

    // Explicit Load/LoadFile in rippled loadOldLedger requires a complete
    // walkLedger(..., true) before switchLCL/setFullLedger. Unlike normal
    // getLastFullLedger recovery, this mode must reject a partial local ledger.
    if !loaded.walk_ledger_with_family(&journal, true, &family) {
        tracing::warn!(target: "bootstrap", seq = loaded.header().seq,
            "Explicit startup ledger is missing SHAMap nodes");
        return Ok(None);
    }

    // Finish fee/rule setup after the complete walk. Normal startup no longer
    // reaches this path; it follows rippled startGenesisLedger instead.
    match loaded.finish_load_by_index_or_hash(&journal) {
        Ok(()) => {}
        Err(error) => {
            tracing::warn!(target: "bootstrap",
                seq = loaded.header().seq,
                error = ?error,
                "Startup ledger FeeSettings/setup not resolvable from local NodeStore; falling back to network"
            );
            return Ok(None);
        }
    }
    loaded.assert_sensible();
    Ok(Some(loaded))
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ReplayStartupResult {
    Complete,
    ParentIncomplete(PendingReplayStartup),
}

fn replay_startup_ledger_from_storage(
    root: &ApplicationRoot,
    start_ledger: Option<&str>,
    trap_tx_hash: Option<Uint256>,
) -> Result<ReplayStartupResult, String> {
    let Some(relational) = root.relational_database().as_ref().map(Arc::clone) else {
        return Err("Replay startup requires an attached relational ledger database".to_owned());
    };
    let Some(node_store) = root.node_store().clone() else {
        return Err("Replay startup requires an attached NodeStore".to_owned());
    };
    let Some(ledger_master_runtime) = root.ledger_master_runtime() else {
        return Err("Replay startup requires an attached LedgerMaster runtime".to_owned());
    };

    let provider = BootstrapLedgerDbProvider::new(relational);
    let family = SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "app-bootstrap-ledger-replay-loader",
            8,
            time::Duration::seconds(1),
            MonotonicClock::default(),
        )),
        NullFullBelowCache::new(0),
        BootstrapNodeStoreFetcher::new(node_store),
        NullMissingNodeReporter,
    );
    let journal = BootstrapLedgerJournal;
    let config = LedgerConfig::default();

    let mut replay_ledger =
        load_bootstrap_ledger(start_ledger, &journal, &config, &family, &provider)?
            .ok_or_else(|| "Requested replay ledger was not found in local storage".to_owned())?;

    if !replay_ledger.walk_ledger_with_family(&journal, false, &family) {
        return Err(format!(
            "Replay ledger {} is incomplete in local NodeStore",
            replay_ledger.header().seq
        ));
    }
    replay_ledger
        .finish_load_by_index_or_hash(&journal)
        .map_err(|error| format!("replay ledger setup failed: {error:?}"))?;
    replay_ledger.assert_sensible();

    let mut parent_ledger = load_by_hash(
        replay_ledger.header().parent_hash,
        false,
        &journal,
        &config,
        &family,
        &provider,
    )
    .map_err(|error| format!("replay parent ledger load failed: {error:?}"))?
    .ok_or_else(|| "Replay parent ledger was not found in local storage".to_owned())?;

    if !parent_ledger.walk_ledger_with_family(&journal, false, &family) {
        return Ok(ReplayStartupResult::ParentIncomplete(
            PendingReplayStartup {
                // Acquire by the replay header's parent hash, not by a locally
                // reconstructed header. This keeps the request pinned to the
                // exact immutable parent that replay is about to consume.
                parent_hash: *replay_ledger.header().parent_hash.as_uint256(),
                parent_seq: parent_ledger.header().seq,
                start_ledger: start_ledger.map(str::to_owned),
                trap_tx_hash,
            },
        ));
    }
    parent_ledger
        .finish_load_by_index_or_hash(&journal)
        .map_err(|error| format!("replay parent setup failed: {error:?}"))?;
    parent_ledger.assert_sensible();

    let parent = root.ledger_with_node_fetcher(Arc::new(parent_ledger));
    hydrate_loaded_ledger(
        root,
        Arc::clone(&parent),
        ledger_master_runtime.ledger_master(),
    )?;
    inject_replay_transactions(root, parent, Arc::new(replay_ledger), &family, trap_tx_hash)?;
    Ok(ReplayStartupResult::Complete)
}

fn load_startup_ledger_from_file(
    root: &ApplicationRoot,
    options: &AppBootstrapOptions,
) -> Result<(), String> {
    let Some(path) = options.start_ledger.as_deref() else {
        return Err("Ledger-file startup requires a file path".to_owned());
    };
    let Some(ledger_master_runtime) = root.ledger_master_runtime() else {
        return Err("Ledger-file startup requires an attached LedgerMaster runtime".to_owned());
    };

    let ledger = load_bootstrap_ledger_from_file(path)?;
    hydrate_loaded_ledger(
        root,
        Arc::new(ledger),
        ledger_master_runtime.ledger_master(),
    )?;
    Ok(())
}

fn load_bootstrap_ledger<P, CLOCK, S, FB, F, MR, NS, J>(
    requested: Option<&str>,
    journal: &J,
    config: &LedgerConfig,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
    provider: &P,
) -> Result<Option<Ledger>, String>
where
    P: LedgerInfoProvider,
    CLOCK: basics::tagged_cache::CacheClock,
    S: std::hash::BuildHasher + Clone,
    FB: shamap::family::FullBelowCache,
    F: SHAMapNodeFetcher,
    MR: shamap::family::MissingNodeReporter,
    J: LedgerJournal,
{
    let requested = requested.map(str::trim).filter(|value| !value.is_empty());
    if requested.is_none() || requested == Some("latest") {
        return ledger::get_latest_ledger(journal, config, family, provider)
            .map(|(ledger, _, _)| ledger)
            .map_err(|error| format!("latest local ledger load failed: {error:?}"));
    }

    let requested = requested.expect("requested startup ledger should be present");
    if requested.len() == 64 {
        let hash = Uint256::from_hex(requested)
            .map_err(|_| format!("invalid startup ledger hash: {requested}"))?;
        return load_by_hash(
            basics::sha_map_hash::SHAMapHash::new(hash),
            false,
            journal,
            config,
            family,
            provider,
        )
        .map_err(|error| format!("hash ledger load failed: {error:?}"));
    }

    let ledger_index = requested
        .parse::<u32>()
        .map_err(|_| format!("invalid startup ledger selector: {requested}"))?;
    load_by_index(ledger_index, false, journal, config, family, provider)
        .map_err(|error| format!("indexed ledger load failed: {error:?}"))
}

fn hydrate_loaded_ledger(
    root: &ApplicationRoot,
    ledger: Arc<Ledger>,
    ledger_master: Arc<crate::AppLedgerMaster>,
) -> Result<(), String> {
    let persistence = ledger::LedgerPersistence::new(root.build_ledger_persistence_runtime());
    let ledger = root.ledger_with_node_fetcher(ledger);

    // Matches rippled loadOldLedger(): switchLCL(loadLedger), mark the ledger
    // validated, then setFullLedger(loadLedger, true, false). Avoid direct
    // wrapped-master closed/pub/valid writes: ApplicationRoot owns the
    // canonical closed slot and app-visible bridges.
    root.on_closed_ledger(Arc::clone(&ledger));
    ledger_master
        .set_full_ledger(&persistence, Arc::clone(&ledger), true, false, None, None)
        .map_err(|error| format!("ledger master bootstrap failed: {error:?}"))?;
    let _ = root.on_validated_ledger(Arc::clone(&ledger));
    if let Some(published) = ledger_master.published_ledger() {
        // setFullLedger selects the publication ledger in the wrapped
        // LedgerMaster. Mirror that authoritative selection into the app-owned
        // publication tracker rather than independently selecting `ledger`.
        root.on_published_ledger(published);
    }

    let next_index = ledger.header().seq.saturating_add(1);
    let base_fee = ledger.fees().base.max(10);
    let _ = root.open_ledger().modify(|view| {
        *view = crate::AppOpenLedgerView::with_parent_timing(
            next_index,
            base_fee,
            *ledger.header().hash.as_uint256(),
            ledger.header().close_time,
            ledger.header().close_time_resolution,
        );
        true
    });

    let _ = root.order_book_db().setup(
        Arc::clone(&ledger),
        Arc::new(NullOrderBookDBRuntime),
        Arc::new(NullOrderBookDBJournal),
    );

    Ok(())
}

/// Preserve the replay ledger's metadata ordering for startup injection. Unlike
/// normal admission, replay startup does not independently preflight or apply
/// historical transactions: it restores the transaction set that the later
/// replay build will process cumulatively.
fn ordered_replay_open_ledger_transactions(replay_data: &LedgerReplay) -> Vec<Arc<STTx>> {
    replay_data
        .ordered_txs()
        .values()
        .map(|entry| Arc::clone(entry.transaction()))
        .collect()
}

fn inject_replay_transactions<CLOCK, S, FB, F, MR, NS>(
    root: &ApplicationRoot,
    parent: Arc<Ledger>,
    replay: Arc<Ledger>,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
    trap_tx_hash: Option<Uint256>,
) -> Result<(), String>
where
    CLOCK: basics::tagged_cache::CacheClock,
    S: std::hash::BuildHasher + Clone,
    FB: shamap::family::FullBelowCache,
    F: SHAMapNodeFetcher,
    MR: shamap::family::MissingNodeReporter,
{
    let replay_data = build_replay_data_with_family(parent, replay, family)?;

    // Parity: ../rippled/src/xrpld/app/main/Application.cpp::
    // ApplicationImp::loadOldLedger iterates LedgerReplay::orderedTxns and
    // calls OpenView::rawTxInsert. Startup must keep that raw, ordered set
    // intact: dependent sequence transactions are applied by the later
    // cumulative replay build, not preclaimed independently against parent.
    let admitted = ordered_replay_open_ledger_transactions(&replay_data);
    let found_trap = trap_tx_hash.is_none()
        || admitted
            .iter()
            .any(|tx| trap_tx_hash == Some(tx.get_transaction_id()));
    if !found_trap {
        return Err("Replay ledger does not contain the requested trap transaction".to_owned());
    }

    let _ = root.open_ledger().modify(|view| {
        for tx in admitted {
            view.push_transaction(tx);
        }
        true
    });

    Ok(())
}

fn build_replay_data_with_family<CLOCK, S, FB, F, MR, NS>(
    parent: Arc<Ledger>,
    replay: Arc<Ledger>,
    family: &SHAMapFamily<CLOCK, S, FB, F, MR, NS>,
) -> Result<LedgerReplay, String>
where
    CLOCK: basics::tagged_cache::CacheClock,
    S: std::hash::BuildHasher + Clone,
    FB: shamap::family::FullBelowCache,
    F: SHAMapNodeFetcher,
    MR: shamap::family::MissingNodeReporter,
{
    let mut ordered_txs = std::collections::BTreeMap::new();
    let mut stack: Vec<NodePathEntry> = Vec::new();
    let mut current = replay
        .tx_map()
        .peek_first_item_with_family(&mut stack, family)
        .map_err(|error| format!("replay tx traversal failed: {error:?}"))?;

    while let Some(node) = current {
        if !node.is_leaf() {
            break;
        }
        let item = node
            .peek_item()
            .ok_or_else(|| "replay tx leaf did not contain an item".to_owned())?;
        let (entry, meta_index) = decode_replay_tx_item(replay.header().seq, &item)?;
        ordered_txs.entry(meta_index).or_insert(entry);
        current = replay
            .tx_map()
            .peek_next_item_with_family(item.key(), &mut stack, family)
            .map_err(|error| format!("replay tx traversal failed: {error:?}"))?;
    }

    Ok(LedgerReplay::new_with_metadata(parent, replay, ordered_txs))
}

fn decode_replay_tx_item(
    ledger_seq: u32,
    item: &SHAMapItem,
) -> Result<(ledger::ReplayTransaction, u32), String> {
    let (tx_bytes, meta_bytes) = catch_unwind(AssertUnwindSafe(|| {
        let mut serial = SerialIter::new(item.data());
        (serial.get_vl(), serial.get_vl())
    }))
    .map_err(|_| "failed to split replay transaction-with-meta payload".to_owned())?;

    let tx = catch_unwind(AssertUnwindSafe(|| {
        let mut serial = SerialIter::new(&tx_bytes);
        Arc::new(STTx::from_serial_iter(&mut serial))
    }))
    .map_err(|_| "failed to parse replay STTx".to_owned())?;

    let meta = catch_unwind(AssertUnwindSafe(|| {
        TxMeta::from_raw(item.key(), ledger_seq, &meta_bytes)
    }))
    .map_err(|_| "failed to parse replay TxMeta".to_owned())?;

    Ok((
        ledger::ReplayTransaction::new(tx, Arc::new(Serializer::from_bytes(meta_bytes))),
        meta.get_index(),
    ))
}

fn load_bootstrap_ledger_from_file(path: &str) -> Result<Ledger, String> {
    let contents = fs::read_to_string(path)
        .map_err(|error| format!("failed to read ledger file {path}: {error}"))?;
    let parsed: serde_json::Value = serde_json::from_str(&contents)
        .map_err(|error| format!("failed to parse ledger JSON {path}: {error}"))?;
    let mut ledger = JsonValue::from(parsed);

    if let Some(result) = ledger.get("result").cloned() {
        ledger = result;
    }
    if let Some(inner) = ledger.get("ledger").cloned() {
        ledger = inner;
    }

    let mut seq = 1u32;
    let mut close_time = 0u32;
    let mut close_time_resolution = 30u8;
    let mut close_time_estimated = false;
    let mut total_drops = 0u64;
    let state_entries = if let Some(account_state) = ledger.get("accountState").cloned() {
        if let Some(index) = ledger.get("ledger_index").and_then(JsonValue::as_u64) {
            seq = index as u32;
        }
        if let Some(file_close_time) = ledger.get("close_time").and_then(JsonValue::as_u64) {
            close_time = file_close_time as u32;
        }
        if let Some(resolution) = ledger
            .get("close_time_resolution")
            .and_then(JsonValue::as_u64)
        {
            close_time_resolution = resolution as u8;
        }
        if let Some(estimated) = ledger.get("close_time_estimated") {
            close_time_estimated = matches!(estimated, JsonValue::Bool(true));
        }
        if let Some(total_coins) = ledger.get("total_coins") {
            total_drops = match total_coins {
                JsonValue::String(value) => value
                    .parse::<u64>()
                    .map_err(|_| "invalid total_coins in ledger file".to_owned())?,
                JsonValue::Unsigned(value) => *value,
                JsonValue::Signed(value) if *value >= 0 => *value as u64,
                _ => return Err("invalid total_coins in ledger file".to_owned()),
            };
        }
        account_state
    } else {
        ledger
    };

    let JsonValue::Array(entries) = state_entries else {
        return Err("ledger file accountState must be an array".to_owned());
    };

    let mut state_tree = MutableTree::new(seq.max(1));
    for entry in entries {
        let JsonValue::Object(mut object) = entry else {
            return Err("invalid entry in ledger file".to_owned());
        };
        let Some(index_text) = object
            .remove("index")
            .and_then(|value| value.as_str().map(ToOwned::to_owned))
        else {
            return Err("ledger file entry missing index".to_owned());
        };
        let index = Uint256::from_hex(&index_text)
            .map_err(|_| format!("invalid ledger entry index in {path}"))?;
        let sle = if let Some(blob_text) = object
            .remove("blob")
            .and_then(|value| value.as_str().map(ToOwned::to_owned))
        {
            let bytes = str_unhex(&blob_text)
                .ok_or_else(|| format!("invalid ledger entry blob in {path}"))?;
            let mut iter = SerialIter::new(&bytes);
            let entry = STLedgerEntry::try_from_serial_iter(&mut iter, index)
                .map_err(|error| format!("invalid ledger entry blob in {path}: {error}"))?;
            if !iter.empty() {
                return Err(format!(
                    "invalid trailing bytes in ledger entry blob {path}"
                ));
            }
            entry
        } else {
            let parsed = STParsedJSONObject::new("sle", &JsonValue::Object(object));
            let st_object = parsed
                .object
                .ok_or_else(|| format!("invalid ledger file entry in {path}"))?;
            STLedgerEntry::try_from_stobject(st_object, index)
                .map_err(|error| format!("invalid ledger file entry in {path}: {error}"))?
        };
        state_tree
            .add_item(
                SHAMapNodeType::AccountState,
                SHAMapItem::new(index, sle.get_serializer().data().to_vec()),
            )
            .map_err(|error| format!("failed to add ledger file entry: {error:?}"))?;
    }

    let mut ledger = Ledger::from_maps(
        LedgerHeader {
            seq,
            close_time,
            close_time_resolution,
            ..LedgerHeader::default()
        },
        SyncTree::from_root_with_type(
            state_tree.root(),
            SHAMapType::State,
            false,
            seq,
            SyncState::Modifying,
        ),
        SyncTree::new_with_type(SHAMapType::Transaction, false, seq),
    );
    ledger.set_total_drops(total_drops);
    let _ = ledger
        .set_accepted_and_setup_from_config(
            close_time,
            close_time_resolution,
            !close_time_estimated,
            &LedgerConfig::default(),
        )
        .map_err(|error| format!("failed to finalize ledger file state: {error:?}"))?;
    Ok(ledger)
}

fn parse_sql_hash(value: String) -> rusqlite::Result<basics::sha_map_hash::SHAMapHash> {
    Uint256::from_hex(&value)
        .map(basics::sha_map_hash::SHAMapHash::new)
        .map_err(|_| {
            rusqlite::Error::FromSqlConversionFailure(
                value.len(),
                rusqlite::types::Type::Text,
                Box::new(std::io::Error::other("invalid ledger hash")),
            )
        })
}

fn to_core_startup_type(start_type: StartUpType) -> quaxar_core::StartUpType {
    match start_type {
        StartUpType::Fresh => quaxar_core::StartUpType::Fresh,
        StartUpType::Normal => quaxar_core::StartUpType::Normal,
        StartUpType::Load => quaxar_core::StartUpType::Load,
        StartUpType::LoadFile => quaxar_core::StartUpType::LoadFile,
        StartUpType::Replay => quaxar_core::StartUpType::Replay,
        StartUpType::Network => quaxar_core::StartUpType::Network,
        StartUpType::Snapshot => quaxar_core::StartUpType::Snapshot,
    }
}

fn seed_startup_ledger_state(
    root: &ApplicationRoot,
    options: &AppBootstrapOptions,
    config: &BasicConfig,
) -> Result<(), String> {
    let seed_seq = options
        .start_ledger
        .as_deref()
        .and_then(|value| value.parse::<u32>().ok())
        .filter(|seq| *seq > 0)
        .unwrap_or(1);
    let backed = root.node_store().is_some();

    let closed = match options.start_type {
        StartUpType::Fresh | StartUpType::Normal | StartUpType::Network | StartUpType::Snapshot => {
            // All these modes call startGenesisLedger() in rippled.
            // Normal with no local DB, Fresh, Network, and Snapshot all
            // create a proper genesis ledger with state tree and computed hash.
            let preset_features = configured_feature_ids(config);
            let genesis_amendments = amendments_from_config(config, options.start_type);
            let genesis_config = LedgerConfig {
                fees: ledger::CURRENT_DEFAULT_FEES,
                features: protocol::FeatureSet::new(preset_features),
            };
            Ledger::create_genesis(backed, &genesis_config, genesis_amendments)
                .unwrap_or_else(|_| Ledger::from_ledger_seq_and_close_time(1, 0, backed))
        }
        StartUpType::Replay => {
            Ledger::from_ledger_seq_and_close_time(seed_seq.max(2) - 1, 0, backed)
        }
        StartUpType::Load | StartUpType::LoadFile => {
            Ledger::from_ledger_seq_and_close_time(seed_seq, 0, backed)
        }
    };
    let closed = Arc::new(closed);
    tracing::info!(target: "bootstrap", ledger_seq = closed.header().seq, "Genesis ledger loaded");
    let hydrate_seed_as_loaded = !matches!(
        options.start_type,
        StartUpType::Fresh | StartUpType::Normal | StartUpType::Network
    );
    if hydrate_seed_as_loaded
        && closed.is_immutable()
        && let Some(ledger_master_runtime) = root.ledger_master_runtime()
    {
        hydrate_loaded_ledger(
            root,
            Arc::clone(&closed),
            ledger_master_runtime.ledger_master(),
        )?;
        return Ok(());
    }

    // =========================================================================
    // GENESIS PERSISTENCE — MUST happen BEFORE on_closed_ledger.
    //
    // rippled parity: `Ledger::Ledger(kCreateGenesis, ...)` calls
    //   stateMap_.flushDirty(AccountNode)   ← persists ALL nodes to NuDB + tree cache
    //   setImmutable()
    // BEFORE `switchLCL` / `storeLedger` ever touches the ledger.
    //
    // Persist the full tree before the first closed-LCL installation, matching
    // rippled's genesis construction. The active LCL remains resident after
    // installation; it must not be forcibly evicted from the consensus path.
    // =========================================================================
    if root.node_store().is_some() {
        let writer = root.node_writer_result_from_store();
        let tree_cache = root.shared_tree_cache();
        if writer.is_some() || tree_cache.is_some() {
            let mut genesis_for_persist = closed.as_ref().clone();
            let writer = writer.ok_or_else(|| {
                "missing fallible node writer while persisting genesis ledger".to_owned()
            })?;
            genesis_for_persist.set_node_writer_result(writer);
            let batch_writer = root.node_batch_writer_result_from_store().ok_or_else(|| {
                "missing fallible node batch writer while persisting genesis ledger".to_owned()
            })?;
            genesis_for_persist.set_node_batch_writer_result(batch_writer);
            genesis_for_persist.state_map_mut().set_backed();
            genesis_for_persist.tx_map_mut().set_backed();
            // Persist dirty nodes to NuDB + tree cache. Propagate failure:
            // rippled flushDirty/writeNode does not silently continue after a
            // backend write failure, and startup must not release an
            // unpersisted genesis tree.
            genesis_for_persist
                .persist_dirty_nodes_to_store_result(tree_cache)
                .map_err(|error| format!("genesis NuDB persistence failed: {error}"))?;
            tracing::info!(
                target: "bootstrap",
                seq = closed.header().seq,
                has_fallible_writer = genesis_for_persist.has_node_writer_result(),
                has_tree_cache = tree_cache.is_some(),
                "Genesis state nodes persisted to NuDB (before on_closed_ledger)"
            );
        }
    }

    // Construct the immutable next ledger before releasing the genesis tree.
    // This is rippled ApplicationImp::startGenesisLedger(): store genesis,
    // create next from genesis, update its skip list, set immutable, emplace
    // open ledger from next, store next, then switchLCL(next).
    let mut next = Ledger::from_previous(closed.as_ref(), root.current_close_time_seconds());
    if root.node_store().is_some() {
        let writer = root.node_writer_result_from_store().ok_or_else(|| {
            "missing fallible node writer while constructing initial next ledger".to_owned()
        })?;
        next.set_node_writer_result(writer);
        let batch_writer = root.node_batch_writer_result_from_store().ok_or_else(|| {
            "missing fallible node batch writer while constructing initial next ledger".to_owned()
        })?;
        next.set_node_batch_writer_result(batch_writer);
        if let Some(fetcher) = root.node_fetcher_from_store() {
            next.set_node_fetcher(fetcher);
        }
        next.state_map_mut().set_backed();
        next.tx_map_mut().set_backed();
    }
    next.update_skip_list()
        .map_err(|error| format!("initial next-ledger skip list failed: {error:?}"))?;
    if root.node_store().is_some() {
        next.persist_dirty_nodes_to_store_result(root.shared_tree_cache())
            .map_err(|error| format!("initial next-ledger NuDB persistence failed: {error}"))?;
        // A start-valid forge is immediately copied and reopened by Pulsar.
        // Persisting dirty SHAMap nodes schedules backend writes; force the
        // NodeStore durability barrier before the validated header can be
        // written, otherwise `--load` finds metadata without its full tree.
        match root.node_store().as_ref() {
            Some(crate::SHAMapStoreNodeStore::Single(database)) => database.sync(),
            Some(crate::SHAMapStoreNodeStore::Rotating(database)) => database.sync(),
            None => unreachable!("node store presence was checked above"),
        }
    }
    next.set_immutable(true);
    let next = Arc::new(next);

    // Rippld stores genesis but does not switch LCL to it. Store by hash, then
    // switch directly to the immutable next ledger below.
    if let Some(runtime) = root.ledger_master_runtime() {
        runtime
            .ledger_master()
            .ledger_history()
            .insert(Arc::clone(&closed), false);
    }

    let next_open_index = next.header().seq.saturating_add(1);
    let _ = root.open_ledger().modify(|view| {
        *view = crate::AppOpenLedgerView::with_parent_timing(
            next_open_index,
            next.fees().base.max(10),
            *next.header().hash.as_uint256(),
            next.header().close_time,
            next.header().close_time_resolution,
        );
        true
    });
    // `--valid` is an explicit operator assertion that the initial LCL is a
    // valid network ledger. Hydrate it through the same `setFullLedger` /
    // application bridge as a durable load before installing the acquisition
    // coordinator; otherwise the coordinator sees a closed-but-unpublished
    // Fresh LCL and overwrites the requested Full startup mode with Connected.
    // Ordinary Fresh startup deliberately remains closed-only.
    if options.start_valid && !options.standalone {
        let ledger_master = root
            .ledger_master_runtime()
            .ok_or_else(|| "missing ledger master while honoring --valid startup".to_owned())?
            .ledger_master();
        hydrate_loaded_ledger(root, Arc::clone(&next), ledger_master)?;
        return Ok(());
    }

    // switchLCL(next) occurs after the open ledger is based on next.
    root.on_closed_ledger(Arc::clone(&next));

    // Only standalone startup promotes the initial next LCL through the same
    // switchLCL branch used by accepted children, including setFullLedger,
    // tryAdvance, and the app publication bridge.
    if options.standalone {
        root.install_consensus_child(Arc::clone(&next));
    }

    Ok(())
}

fn configured_feature_ids(config: &BasicConfig) -> Vec<Uint256> {
    config
        .section("features")
        .values()
        .iter()
        .filter_map(|line| {
            let name = line.split_whitespace().next()?;
            REGISTERED_FEATURES
                .iter()
                .find(|feature| {
                    protocol::registered_feature_supported(feature) && feature.name == name
                })
                .map(|feature| feature_id(feature.name))
        })
        .collect()
}

fn amendments_from_config(config: &BasicConfig, start_type: StartUpType) -> Vec<Uint256> {
    if start_type != StartUpType::Fresh {
        return Vec::new();
    }

    let section = config.section("amendments");
    let values = section.values();
    if !values.is_empty() {
        return values
            .iter()
            .filter_map(|line| {
                let hex = line.split_whitespace().next()?;
                if hex.len() != 64 {
                    return None;
                }
                let bytes = str_unhex(hex)?;
                Uint256::from_slice(&bytes)
            })
            .collect();
    }

    // Pulsar's generated private-network configs use named features rather
    // than a hexadecimal [amendments] section. Preserve that explicit desired
    // set at Fresh genesis; falling through to every supported feature changes
    // the harness contract and left the full nodes with a no-amendment ledger.
    let configured = configured_feature_ids(config);
    if !configured.is_empty() {
        return configured;
    }

    REGISTERED_FEATURES
        .iter()
        .filter(|feature| protocol::registered_feature_supported(feature))
        .map(|f| feature_id(f.name))
        .collect()
}

fn config_legacy_u32(config: &BasicConfig, section: &str) -> Option<u32> {
    let value = config.legacy(section).ok()?;
    let trimmed = value.trim();
    match trimmed.to_ascii_lowercase().as_str() {
        "full" => Some(u32::MAX),
        "none" => Some(0),
        _ => trimmed.parse::<u32>().ok(),
    }
}

fn config_legacy_usize(config: &BasicConfig, section: &str) -> Option<usize> {
    config.legacy(section).ok()?.trim().parse::<usize>().ok()
}

/// Strict legacy-section parser for Config values where malformed, signed, or
/// multiple entries must fail bootstrap rather than silently choosing a default.
fn config_single_unsigned(config: &BasicConfig, section: &str) -> Result<Option<usize>, String> {
    let values = config.section(section).values();
    match values {
        [] => Ok(None),
        [value] => value.trim().parse::<usize>().map(Some).map_err(|_| {
            format!("invalid [{section}] configuration: expected one unsigned integer")
        }),
        _ => Err(format!(
            "invalid [{section}] configuration: expected one value"
        )),
    }
}

/// Match rippled Config's `[sweep_interval]`: administrators may override the
/// node-size SweepInterval, but only with a value in the reference's 10–600
/// second range.
fn configured_sweep_interval(config: &BasicConfig, default: u64) -> Result<u64, String> {
    if !config.exists("sweep_interval") {
        return Ok(default);
    }
    let raw = config
        .legacy("sweep_interval")
        .map_err(|error| format!("invalid [sweep_interval] configuration: {error}"))?;
    let seconds = raw
        .trim()
        .parse::<u64>()
        .map_err(|_| "invalid [sweep_interval]: must be an integer from 10 to 600".to_owned())?;
    if !(10..=600).contains(&seconds) {
        return Err("invalid [sweep_interval]: must be between 10 and 600 inclusive".to_owned());
    }
    Ok(seconds)
}

/// Parse the `[transaction_queue]` config section.
/// All fields are optional — unset fields use TxQSetup::default().
fn parse_txq_setup(config: &BasicConfig) -> tx::TxQSetup {
    use tx::TxQSetup;
    let mut setup = TxQSetup::default();

    if !config.exists("transaction_queue") {
        return setup;
    }

    let section_values: Vec<(String, String)> = config
        .section("transaction_queue")
        .values()
        .iter()
        .filter_map(|line| {
            let parts: Vec<&str> = line.splitn(2, '=').collect();
            if parts.len() == 2 {
                Some((parts[0].trim().to_string(), parts[1].trim().to_string()))
            } else {
                None
            }
        })
        .collect();

    for (key, value) in &section_values {
        match key.as_str() {
            "ledgers_in_queue" => {
                if let Ok(v) = value.parse::<usize>() {
                    setup.ledgers_in_queue = v;
                }
            }
            "minimum_queue_size" => {
                if let Ok(v) = value.parse::<usize>() {
                    setup.queue_size_min = v;
                }
            }
            "retry_sequence_percent" => {
                if let Ok(v) = value.parse::<u32>() {
                    setup.retry_sequence_percent = v;
                }
            }
            "minimum_txn_in_ledger" => {
                if let Ok(v) = value.parse::<usize>() {
                    setup.minimum_txn_in_ledger = v;
                }
            }
            "minimum_txn_in_ledger_standalone" => {
                if let Ok(v) = value.parse::<usize>() {
                    setup.minimum_txn_in_ledger_standalone = v;
                }
            }
            "target_txn_in_ledger" => {
                if let Ok(v) = value.parse::<usize>() {
                    setup.target_txn_in_ledger = v;
                }
            }
            "maximum_txn_in_ledger" => {
                if let Ok(v) = value.parse::<usize>() {
                    setup.maximum_txn_in_ledger = Some(v);
                }
            }
            "normal_consensus_increase_percent" => {
                if let Ok(v) = value.parse::<u32>() {
                    setup.normal_consensus_increase_percent = v.clamp(0, 1000);
                }
            }
            "slow_consensus_decrease_percent" => {
                if let Ok(v) = value.parse::<u32>() {
                    setup.slow_consensus_decrease_percent = v.clamp(0, 100);
                }
            }
            "maximum_txn_per_account" => {
                if let Ok(v) = value.parse::<u32>() {
                    setup.maximum_txn_per_account = v;
                }
            }
            "minimum_last_ledger_buffer" => {
                if let Ok(v) = value.parse::<u32>() {
                    setup.minimum_last_ledger_buffer = v;
                }
            }
            _ => {
                tracing::warn!(target: "bootstrap", key, "Unknown [transaction_queue] config key");
            }
        }
    }

    // Validation: maximum must not be less than minimum
    if let Some(max) = setup.maximum_txn_in_ledger {
        if max < setup.minimum_txn_in_ledger {
            panic!(
                "The minimum number of low-fee transactions allowed per ledger \
                 (minimum_txn_in_ledger={}) exceeds the maximum (maximum_txn_in_ledger={})",
                setup.minimum_txn_in_ledger, max
            );
        }
    }

    tracing::info!(target: "bootstrap",
        ledgers_in_queue = setup.ledgers_in_queue,
        queue_size_min = setup.queue_size_min,
        minimum_txn_in_ledger = setup.minimum_txn_in_ledger,
        target_txn_in_ledger = setup.target_txn_in_ledger,
        maximum_txn_per_account = setup.maximum_txn_per_account,
        "Loaded [transaction_queue] config"
    );

    setup
}

fn config_path_search_max(config: &BasicConfig) -> u32 {
    if let Some(explicit) = config_legacy_u32(config, "path_search_max") {
        return explicit;
    }

    if config.exists("validation_seed") || config.exists("validator_token") {
        0
    } else {
        3
    }
}

fn parse_basic_config_text(text: &str) -> Result<BasicConfig, String> {
    let mut sections = IniFileSections::new();
    let mut current_section = String::new();

    for raw_line in text.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        if line.starts_with('[') && line.ends_with(']') {
            current_section = line[1..line.len() - 1].trim().to_owned();
            let _ = sections.entry(current_section.clone()).or_default();
            continue;
        }

        sections
            .entry(current_section.clone())
            .or_default()
            .push(raw_line.to_owned());
    }

    let mut config = BasicConfig::new();
    config.build(&sections);
    Ok(config)
}

fn usage() -> String {
    [
        "usage: quaxar [options] <command> <params>",
        "General Options:",
        "  --conf PATH         Specify the configuration file.",
        "  --debug             Enable normally suppressed debug logging",
        "  --definitions       Output server definitions as JSON and exit.",
        "  --help, -h          Display this message.",
        "  --newnodeid         Generate a new node identity for this server.",
        "  --nodeid ID         Specify the node identity for this server.",
        "  --quorum N          Override the minimum validation quorum.",
        "  --silent            No output to the console after startup.",
        "  --standalone, -a    Run with no peers.",
        "  --verbose, -v       Verbose logging.",
        "  --version           Display the build version.",
        "",
        "Ledger/Data Options:",
        "  --force_ledger_present_range MIN,MAX",
        "                      Specify the range of present ledgers for testing.",
        "  --import            Import an existing node database.",
        "  --ledger ID         Load the specified ledger and start from the value given.",
        "  --ledgerfile PATH   Load the specified ledger file.",
        "  --load              Load the current ledger from the local DB.",
        "  --net               Get the initial ledger from the network.",
        "  --replay            Replay a ledger close.",
        "  --trap_tx_hash HASH Trap a specific transaction during replay.",
        "  --start             Start from a fresh Ledger.",
        "  --vacuum            VACUUM the transaction db.",
        "  --valid             Consider the initial ledger a valid network ledger.",
        "",
        "RPC Client Options:",
        "  --rpc               Perform rpc command. Assumed if any positional parameters provided.",
        "  --rpc_ip IP[:PORT]  Specify the IP address for RPC command.",
        "  --rpc_port PORT     Specify the port number for RPC command.",
        "",
        "Unit Test Options:",
        "  --quiet, -q         Suppress test suite messages.",
        "  --unittest [SEL]    Perform unit tests.",
        "  --unittest-arg ARG  Supplies an argument string to unit tests.",
        "  --unittest-ipv6     Use IPv6 localhost when running unittests.",
        "  --unittest-log      Force unit test log message output.",
        "  --unittest-jobs N   Number of unittest jobs to run in parallel.",
    ]
    .join("\n")
}

struct SystemDescriptorLimitProvider;

impl DescriptorLimitProvider for SystemDescriptorLimitProvider {
    fn current_descriptor_limit(&self) -> Option<u64> {
        #[cfg(unix)]
        {
            use libc::{RLIM_INFINITY, RLIMIT_NOFILE, getrlimit, rlimit};
            let mut limits = rlimit {
                rlim_cur: 0,
                rlim_max: 0,
            };
            let status = unsafe { getrlimit(RLIMIT_NOFILE, &mut limits) };
            if status != 0 || limits.rlim_cur == RLIM_INFINITY {
                return None;
            }
            Some(limits.rlim_cur)
        }

        #[cfg(not(unix))]
        {
            None
        }
    }

    fn set_descriptor_limit(&self, requested: u64) -> Option<u64> {
        #[cfg(unix)]
        {
            use libc::{RLIMIT_NOFILE, getrlimit, rlimit, setrlimit};
            let mut limits = rlimit {
                rlim_cur: 0,
                rlim_max: 0,
            };
            if unsafe { getrlimit(RLIMIT_NOFILE, &mut limits) } != 0 {
                return None;
            }
            limits.rlim_cur = requested;
            if unsafe { setrlimit(RLIMIT_NOFILE, &limits) } != 0 {
                return None;
            }
            Some(requested)
        }

        #[cfg(not(unix))]
        {
            let _ = requested;
            None
        }
    }
}

fn should_schedule_relayed_transaction(
    hash_router: &HashRouter,
    transaction_id: Uint256,
    peer_id: overlay::PeerId,
) -> bool {
    // rippled PeerImp::handleTransaction uses a ten-second per-transaction
    // process interval before queuing the RcvCheckTx job.
    const TX_PROCESS_INTERVAL: Duration = Duration::from_secs(10);
    hash_router
        .should_process(transaction_id, peer_id, TX_PROCESS_INTERVAL)
        .0
}

/// Generic `TMGetObjectByHash` replies are cache updates for coordinator
/// sessions, but unlike `otFETCH_PACK` replies they do not enter LedgerMaster's
/// gotFetchPack single-flight. Schedule one coordinator wake only after at
/// least one valid object was cached and only once coordinator ownership is
/// active; legacy acquisition retains its established timeout/worker path.
const fn should_schedule_coordinator_fetch_pack_wake(
    stored: usize,
    coordinator_installed: bool,
) -> bool {
    stored > 0 && coordinator_installed
}

#[cfg(test)]
mod tests {
    use super::{
        APPLICATION_SWEEP_MALLOC_TRIM_TAG, BootstrapLedgerDataRouting, ENDPOINT_HANDOUT_LIMIT,
        FetchPackAdmission, GenericGetObjectAdmission, LedgerDataIngressDisposition, MainRuntime,
        StartUpType, amendments_from_config, build_endpoint_handout,
        build_validator_list_collection_messages, candidate_ledger_data_charge,
        classify_fetch_pack_request, classify_generic_get_object_request, configured_feature_ids,
        configured_sweep_interval, fetch_pack_failure_charge, get_ledger_send_queue_is_admissible,
        get_object_query_send_queue_is_admissible, ledger_data_nodes_are_admissible,
        ledger_data_sequence_is_admissible, load_bootstrap_ledger_from_file,
        manifest_rate_limit_policy, parse_basic_config_text, relay_accepted_manifest,
        requested_transaction_envelope, route_bootstrap_ledger_data,
        sequence_is_fetchable_at_floor, should_schedule_coordinator_fetch_pack_wake,
        should_schedule_relayed_transaction, spawn_shutdown_watcher,
        transaction_object_request_is_admissible, trim_after_application_sweep_with,
        trusted_first_manifest_payloads, validator_list_collection_blobs,
        validator_list_threshold_from_config,
    };
    use super::{ApplicationSweepActions, run_application_sweep};
    use crate::state::manifest::{
        MAX_UNTRUSTED_MANIFESTS, ManifestDisposition, ManifestLimits, ManifestRateLimitCapPolicy,
    };
    use crate::{ApplicationRoot, ValidatorListBroadcastBlob, ValidatorListCollectionForBroadcast};
    use basics::base_uint::Uint256;
    use basics::basic_config::BasicConfig;
    use basics::blob::Blob;
    use basics::hardened_hash::HardenedHashBuilder;
    use basics::memory::malloc_trim::MallocTrimReport;
    use basics::tagged_cache::{ManualClock, MonotonicClock, TaggedCache};
    use ledger::FetchPackCache;
    use nodestore::{DummyScheduler, ManagerImp, NullJournal, Scheduler};
    use shamap::family::FullBelowCacheImpl;
    use shamap::tree_node_cache::TreeNodeCache;
    use std::cell::RefCell;
    use std::collections::BTreeSet;
    use std::fs;
    use std::sync::atomic::AtomicBool;
    use std::sync::{Arc, mpsc};
    use std::time::Duration;
    use tempfile::TempDir;
    use xrpl_core::HashRouter;

    #[test]
    fn allocator_trim_runs_at_the_application_sweep_boundary() {
        let mut tags = Vec::new();
        let report = trim_after_application_sweep_with(|tag| {
            tags.push(tag.to_owned());
            MallocTrimReport {
                supported: true,
                trim_result: 1,
                rss_before_kb: 100,
                rss_after_kb: 90,
                duration_us: 7,
                minflt_delta: 2,
                majflt_delta: 0,
            }
        });
        assert_eq!(tags, vec![APPLICATION_SWEEP_MALLOC_TRIM_TAG]);
        assert!(report.supported);
        assert_eq!(report.delta_kb(), -10);
    }

    struct DeterministicApplicationSweep {
        actions: RefCell<Vec<&'static str>>,
    }

    impl ApplicationSweepActions for DeterministicApplicationSweep {
        fn sweep_inbound_ledgers(&self) {
            self.actions.borrow_mut().push("inbound_ledgers");
        }

        fn sweep_node_family(&self) {
            self.actions.borrow_mut().push("node_family");
        }

        fn sweep_ledger_master(&self) {
            self.actions.borrow_mut().push("ledger_master");
        }

        fn sweep_transaction_master(&self) {
            self.actions.borrow_mut().push("transaction_master");
        }

        fn expire_validations(&self) {
            self.actions.borrow_mut().push("validations");
        }

        fn trim_allocator(&self) {
            self.actions.borrow_mut().push("allocator_trim");
        }
    }

    #[test]
    fn configured_application_sweep_expires_temp_node_cache_before_allocator_trim() {
        let clock = Arc::new(ManualClock::new(0));
        let cache = TaggedCache::<Uint256, Blob, _>::new(
            "NodeCache",
            1,
            time::Duration::seconds(1),
            Arc::clone(&clock),
        );
        let hash = Uint256::from_u64(1);
        let sweep = DeterministicApplicationSweep {
            actions: RefCell::new(Vec::new()),
        };

        assert!(!cache.insert(hash, vec![0xCA, 0xFE]));
        assert_eq!(cache.get_cache_size(), 1);

        clock.advance_seconds(1);
        run_application_sweep(&cache, &sweep);

        assert_eq!(cache.get_cache_size(), 0);
        assert_eq!(cache.get_track_size(), 0);
        assert_eq!(cache.retrieve(&hash), None);
        assert_eq!(
            *sweep.actions.borrow(),
            [
                "inbound_ledgers",
                "node_family",
                "ledger_master",
                "transaction_master",
                "validations",
                "allocator_trim",
            ]
        );
    }

    #[test]
    fn bootstrap_ledger_file_rejects_unknown_sle_type_without_unwinding() {
        let dir = TempDir::new().expect("tempdir");
        let path = dir.path().join("invalid-ledger.json");
        fs::write(
            &path,
            r#"{
                "ledger_index": 1,
                "accountState": [{
                    "index": "0000000000000000000000000000000000000000000000000000000000000000",
                    "blob": "11FFFF"
                }]
            }"#,
        )
        .expect("invalid ledger fixture");

        let loaded = std::panic::catch_unwind(|| {
            load_bootstrap_ledger_from_file(path.to_str().expect("UTF-8 temporary path"))
        });

        assert!(
            loaded.is_ok(),
            "invalid ledger input must not unwind bootstrap"
        );
        assert!(
            loaded
                .expect("caught bootstrap loader")
                .expect_err("unknown LedgerEntryType must be rejected")
                .contains("invalid ledger entry blob"),
            "the bootstrap error must identify the rejected blob"
        );
    }

    #[test]
    fn generic_object_reply_wakes_only_an_installed_coordinator_after_cache_progress() {
        assert!(should_schedule_coordinator_fetch_pack_wake(1, true));
        assert!(should_schedule_coordinator_fetch_pack_wake(8, true));
        assert!(
            !should_schedule_coordinator_fetch_pack_wake(0, true),
            "an empty reply must not manufacture a coordinator plan advance"
        );
        assert!(
            !should_schedule_coordinator_fetch_pack_wake(1, false),
            "legacy acquisition retains its existing fetch-pack wake path"
        );
    }

    #[test]
    fn relayed_transaction_ingress_suppresses_duplicates_and_skips_source_peer() {
        let hash_router = HashRouter::default();
        let tx_id = Uint256::from_u64(0xC0FFEE);
        let source_peer = 41;

        assert!(should_schedule_relayed_transaction(
            &hash_router,
            tx_id,
            source_peer,
        ));
        assert!(
            !should_schedule_relayed_transaction(&hash_router, tx_id, 42),
            "the ten-second HashRouter interval suppresses duplicate relay work"
        );
        assert_eq!(
            hash_router.should_relay(tx_id),
            Some(BTreeSet::from([source_peer, 42])),
            "all inbound sources, including suppressed duplicates, are withheld from re-relay"
        );
    }

    #[test]
    fn fresh_genesis_honors_pulsar_named_features() {
        let config = parse_basic_config_text("[features]\nDID\nCredentials\nunknown_feature\n")
            .expect("Pulsar-style feature config parses");
        let amendments = amendments_from_config(&config, StartUpType::Fresh);

        assert_eq!(amendments.len(), 2);
        assert!(amendments.contains(&protocol::feature_id("DID")));
        assert!(amendments.contains(&protocol::feature_id("Credentials")));
        let genesis = ledger::Ledger::create_genesis(
            false,
            &ledger::LedgerConfig {
                features: protocol::FeatureSet::new(amendments.clone()),
                ..ledger::LedgerConfig::default()
            },
            amendments,
        )
        .expect("Fresh genesis should build");
        assert!(genesis.rules().enabled(&protocol::feature_id("DID")));
        assert!(
            genesis
                .rules()
                .enabled(&protocol::feature_id("Credentials"))
        );
        assert!(
            amendments_from_config(&config, StartUpType::Normal).is_empty(),
            "only Fresh genesis applies configured amendment desires"
        );
    }

    #[test]
    fn network_bootstrap_uses_named_presets_without_genesis_amendments() {
        let config = parse_basic_config_text("[features]\nPriceOracle\n")
            .expect("rippled-style named feature preset parses");
        let presets = configured_feature_ids(&config);
        let amendments = amendments_from_config(&config, StartUpType::Network);

        assert_eq!(presets, vec![protocol::feature_id("PriceOracle")]);
        assert!(
            amendments.is_empty(),
            "Network genesis must not synthesize an Amendments SLE from presets"
        );

        let genesis = ledger::Ledger::create_genesis(
            false,
            &ledger::LedgerConfig {
                features: protocol::FeatureSet::new(presets),
                ..ledger::LedgerConfig::default()
            },
            amendments,
        )
        .expect("Network genesis should build");
        assert!(
            genesis
                .rules()
                .enabled(&protocol::feature_id("PriceOracle"))
        );
        assert!(
            genesis
                .read(protocol::amendments_keylet())
                .expect("genesis amendments read should succeed")
                .is_none(),
            "rippled Network startup leaves the genesis Amendments SLE absent"
        );
        assert!(amendments_from_config(&config, StartUpType::Normal).is_empty());
    }

    #[test]
    fn sweep_interval_matches_rippled_default_and_explicit_override_rules() {
        let unset = parse_basic_config_text("[node_size]\nmedium\n").expect("config parses");
        assert_eq!(configured_sweep_interval(&unset, 60), Ok(60));

        let configured = parse_basic_config_text("[sweep_interval]\n120\n").expect("config parses");
        assert_eq!(configured_sweep_interval(&configured, 60), Ok(120));

        let too_small = parse_basic_config_text("[sweep_interval]\n9\n").expect("config parses");
        assert!(
            configured_sweep_interval(&too_small, 60)
                .expect_err("rippled rejects intervals below 10 seconds")
                .contains("between 10 and 600")
        );

        let malformed = parse_basic_config_text("[sweep_interval]\nnope\n").expect("config parses");
        assert!(
            configured_sweep_interval(&malformed, 60)
                .expect_err("non-numeric sweep interval is invalid")
                .contains("integer")
        );
    }

    #[test]
    fn validator_list_threshold_matches_config_source_validation() {
        let configured = parse_basic_config_text(
            "[validator_list_threshold]\n2\n[validator_list_keys]\na\nb\nc\n",
        )
        .expect("config parses");
        assert_eq!(
            validator_list_threshold_from_config(&configured, 3),
            Ok(Some(2))
        );

        let computed =
            parse_basic_config_text("[validator_list_threshold]\n0\n").expect("config parses");
        assert_eq!(validator_list_threshold_from_config(&computed, 0), Ok(None));

        let multiple =
            parse_basic_config_text("[validator_list_threshold]\n1\n2\n").expect("config parses");
        assert!(
            validator_list_threshold_from_config(&multiple, 2)
                .expect_err("multiple threshold values are invalid")
                .contains("single value")
        );

        let exceeds =
            parse_basic_config_text("[validator_list_threshold]\n3\n").expect("config parses");
        assert!(
            validator_list_threshold_from_config(&exceeds, 2)
                .expect_err("threshold may not exceed publisher keys")
                .contains("exceeds")
        );
    }

    #[test]
    fn manifest_limits_parse_defaults_independently_and_enforce_bounds() {
        let defaults = parse_basic_config_text("[overlay]\n").expect("config parses");
        assert_eq!(
            ManifestLimits::from_config(&defaults),
            Ok(ManifestLimits::default())
        );

        let configured = parse_basic_config_text(
            "[overlay]\nmax_untrusted_count = 50\nmax_trusted_count = 1000\n",
        )
        .expect("config parses");
        assert_eq!(
            ManifestLimits::from_config(&configured),
            Ok(ManifestLimits {
                max_untrusted_count: 50,
                max_trusted_count: 1000,
            })
        );

        for config in [
            "[overlay]\nmax_untrusted_count = 49\n",
            "[overlay]\nmax_trusted_count = 1001\n",
            "[overlay]\nmax_untrusted_count = invalid\n",
        ] {
            let config = parse_basic_config_text(config).expect("config parses");
            assert!(ManifestLimits::from_config(&config).is_err());
        }
    }

    #[test]
    fn startup_manifest_gossip_is_trusted_first_with_independent_bounded_suffix() {
        let entries = std::iter::once((true, vec![1]))
            .chain(std::iter::once((true, vec![2])))
            .chain(std::iter::once((true, vec![3])))
            .chain(
                (0..MAX_UNTRUSTED_MANIFESTS + 1)
                    .map(|n| (false, vec![u8::try_from(n % 255).expect("bounded byte")])),
            );
        let selected = trusted_first_manifest_payloads(entries, ManifestLimits::default());
        assert_eq!(selected.len(), MAX_UNTRUSTED_MANIFESTS + 3);
        assert_eq!(&selected[..3], &[vec![1], vec![2], vec![3]]);

        let entries = [(true, vec![1]), (true, vec![2]), (true, vec![3])]
            .into_iter()
            .chain([(false, vec![4]), (false, vec![5]), (false, vec![6])]);
        let selected = trusted_first_manifest_payloads(
            entries,
            ManifestLimits {
                max_untrusted_count: 2,
                max_trusted_count: 2,
            },
        );
        assert_eq!(selected, vec![vec![1], vec![2], vec![4], vec![5]]);
    }

    #[test]
    fn validator_list_v2_messages_are_recipient_filtered_size_bounded_and_chunk_hashed() {
        let blob = |sequence, fill| ValidatorListBroadcastBlob {
            sequence,
            blob: crate::ValidatorBlobInfo {
                blob: basics::base64::base64_encode(&vec![fill; 128]),
                signature: basics::str_hex::str_hex(&vec![fill; 72]),
                manifest: None,
            },
        };
        let collection = ValidatorListCollectionForBroadcast {
            publisher_key: protocol::PublicKey::from_bytes([2; 33]),
            max_sequence: 3,
            version: 2,
            manifest: basics::base64::base64_encode(&[0xAB; 16]),
            blobs: vec![blob(1, 1), blob(2, 2), blob(3, 3)],
        };
        let one_blob = ValidatorListCollectionForBroadcast {
            blobs: vec![collection.blobs[0].clone()],
            ..collection.clone()
        };
        let max_size = build_validator_list_collection_messages(&one_blob, 0, usize::MAX)
            .pop()
            .expect("single blob collection")
            .message
            .get_buffer_size();
        let messages = build_validator_list_collection_messages(&collection, 0, max_size);
        assert_eq!(messages.len(), 3);
        assert!(
            messages
                .iter()
                .all(|message| message.message.get_buffer_size() <= max_size)
        );
        assert_eq!(
            messages
                .iter()
                .map(|message| message.hash)
                .collect::<std::collections::HashSet<_>>()
                .len(),
            3
        );

        let later_peer = build_validator_list_collection_messages(&collection, 1, max_size);
        assert_eq!(later_peer.len(), 2);
        let fills = later_peer
            .iter()
            .map(|message| match &message.message.protocol().payload {
                overlay::ProtocolPayload::ValidatorListCollection(collection) => {
                    collection.blobs[0].blob[0]
                }
                _ => panic!("expected validator list collection"),
            })
            .collect::<Vec<_>>();
        assert_eq!(fills, vec![2, 3]);
    }

    #[test]
    fn validator_list_collection_conversion_enforces_manifest_bounds() {
        let collection = overlay::TmValidatorListCollection {
            version: 2,
            manifest: vec![7; crate::validator::validator_list::MAX_MANIFEST_BYTES],
            blobs: vec![overlay::message::wire::ValidatorBlobInfo {
                manifest: Some(vec![
                    8;
                    crate::validator::validator_list::MAX_MANIFEST_BYTES
                ]),
                blob: vec![9],
                signature: vec![10],
            }],
        };
        let (manifest, version, blobs) =
            validator_list_collection_blobs(&collection).expect("bounded collection is accepted");
        assert_eq!(version, 2);
        assert_eq!(
            basics::base64::base64_decode(&manifest),
            collection.manifest
        );
        assert_eq!(blobs.len(), 1);
        assert_eq!(
            blobs[0]
                .manifest
                .as_ref()
                .map(|m| basics::base64::base64_decode(m)),
            collection.blobs[0].manifest
        );

        let oversized = overlay::TmValidatorListCollection {
            manifest: vec![0; crate::validator::validator_list::MAX_MANIFEST_BYTES + 1],
            ..collection
        };
        assert!(validator_list_collection_blobs(&oversized).is_none());
    }

    #[test]
    fn ledger_data_sequence_admission_matches_peerimp_rules() {
        assert!(ledger_data_sequence_is_admissible(
            3,
            0,
            Some(100),
            Duration::from_secs(1),
        ));
        assert!(!ledger_data_sequence_is_admissible(
            3,
            1,
            Some(100),
            Duration::from_secs(1),
        ));
        assert!(ledger_data_sequence_is_admissible(
            0,
            110,
            Some(100),
            Duration::from_secs(10),
        ));
        assert!(!ledger_data_sequence_is_admissible(
            0,
            111,
            Some(100),
            Duration::from_secs(10),
        ));
        assert!(ledger_data_sequence_is_admissible(
            0,
            50_000,
            Some(100),
            Duration::from_secs(11),
        ));
    }

    #[test]
    fn get_ledger_send_queue_gate_rejects_all_normal_requests_at_drop_limit() {
        assert!(get_ledger_send_queue_is_admissible(
            0,
            overlay::DROP_SEND_QUEUE - 1,
        ));
        assert!(!get_ledger_send_queue_is_admissible(
            0,
            overlay::DROP_SEND_QUEUE,
        ));
        assert!(!get_ledger_send_queue_is_admissible(
            2,
            overlay::DROP_SEND_QUEUE + 1,
        ));
        // Relayed normal requests use the same overload gate; only their
        // resource charge is cookie-exempt.
        assert!(!get_ledger_send_queue_is_admissible(
            0,
            overlay::DROP_SEND_QUEUE,
        ));
        assert!(get_ledger_send_queue_is_admissible(
            3,
            overlay::DROP_SEND_QUEUE + 1,
        ));
    }

    #[test]
    fn manifest_gossip_processes_trusted_after_untrusted_cap_and_relays_only_accepts() {
        let mut untrusted_processed = 0;
        for _ in 0..MAX_UNTRUSTED_MANIFESTS {
            assert_eq!(
                manifest_rate_limit_policy(
                    false,
                    &mut untrusted_processed,
                    MAX_UNTRUSTED_MANIFESTS
                ),
                Some(ManifestRateLimitCapPolicy::Capped)
            );
        }
        assert_eq!(
            manifest_rate_limit_policy(false, &mut untrusted_processed, MAX_UNTRUSTED_MANIFESTS),
            None,
            "the 301st untrusted manifest must not consume work"
        );
        assert_eq!(
            manifest_rate_limit_policy(true, &mut untrusted_processed, MAX_UNTRUSTED_MANIFESTS),
            Some(ManifestRateLimitCapPolicy::Uncapped),
            "trusted manifests remain processable beyond the untrusted cap"
        );
        assert_eq!(untrusted_processed, MAX_UNTRUSTED_MANIFESTS);
        assert!(relay_accepted_manifest(ManifestDisposition::Accepted));
        assert!(
            !relay_accepted_manifest(ManifestDisposition::Stale),
            "stale cache entries must not be relayed"
        );
        assert!(!relay_accepted_manifest(
            ManifestDisposition::UntrustedCapacity,
        ));
    }

    #[test]
    fn get_object_query_send_queue_gate_applies_to_every_query_type() {
        assert!(get_object_query_send_queue_is_admissible(
            overlay::DROP_SEND_QUEUE - 1,
        ));
        assert!(!get_object_query_send_queue_is_admissible(
            overlay::DROP_SEND_QUEUE,
        ));
    }

    #[test]
    fn transaction_object_requests_require_bounded_well_formed_hashes() {
        let valid = overlay::message::wire::TmIndexedObject {
            hash: Some(basics::base_uint::Uint256::from_u64(7).data().to_vec()),
            node_id: None,
            index: None,
            data: None,
            ledger_seq: None,
        };
        assert!(transaction_object_request_is_admissible(
            std::slice::from_ref(&valid)
        ));
        let malformed = overlay::message::wire::TmIndexedObject {
            hash: Some(vec![0; 31]),
            ..valid.clone()
        };
        assert!(!transaction_object_request_is_admissible(&[malformed]));
        let oversized = vec![valid; overlay::slot::MAX_TX_QUEUE_SIZE + 1];
        assert!(!transaction_object_request_is_admissible(&oversized));
    }

    #[test]
    fn requested_transaction_envelope_matches_peerimp_tmtransactions_fields() {
        let st_tx = Arc::new(protocol::STTx::new(protocol::TxType::PAYMENT, |_| {}));
        let mut transaction = crate::Transaction::new(Arc::clone(&st_tx));
        transaction.set_status(crate::TransStatus::INCLUDED);
        transaction.set_queued();

        let envelope = requested_transaction_envelope(&transaction, 123_456);
        assert_eq!(envelope.raw_transaction, st_tx.get_serializer().data());
        assert_eq!(envelope.status, 2, "included transactions use tsCURRENT");
        assert_eq!(envelope.receive_timestamp, Some(123_456));
        assert_eq!(envelope.deferred, Some(true));

        transaction.set_status(crate::TransStatus::HELD);
        assert_eq!(requested_transaction_envelope(&transaction, 1).status, 1);
    }

    #[test]
    fn endpoint_handout_is_per_peer_bounded_and_uses_unspecified_self_entry() {
        let recipient = "192.0.2.1:51235".parse().expect("socket address");
        let candidates = vec![
            recipient,
            "192.0.2.2:51235".parse().expect("socket address"),
            "192.0.2.2:51236".parse().expect("socket address"),
            "192.0.2.3:51235".parse().expect("socket address"),
        ];
        let handout = build_endpoint_handout(Some(51235), recipient, candidates, |_, _| true);
        assert_eq!(handout[0].endpoint, "[::]:51235");
        assert_eq!(handout[0].hops, 0);
        assert!(handout.iter().skip(1).all(|endpoint| endpoint.hops == 1));
        assert!(
            handout
                .iter()
                .all(|endpoint| endpoint.endpoint != "192.0.2.1:51235")
        );
        assert_eq!(handout.len(), 3, "the same endpoint IP is handed out once");
        assert!(handout.len() <= ENDPOINT_HANDOUT_LIMIT);
    }

    #[test]
    fn generic_get_object_admission_matches_peerimp_structural_gates() {
        assert_eq!(
            classify_generic_get_object_request(Some(&[7; 31]), 1),
            GenericGetObjectAdmission::MalformedLedgerHash,
        );
        assert_eq!(
            classify_generic_get_object_request(None, 12_289),
            GenericGetObjectAdmission::Oversized,
        );
        assert_eq!(
            classify_generic_get_object_request(
                Some(basics::base_uint::Uint256::from_u64(7).data()),
                1,
            ),
            GenericGetObjectAdmission::Accepted,
        );
    }

    #[test]
    fn candidate_ledger_data_node_count_matches_peerimp_invalid_data_gate() {
        assert!(!ledger_data_nodes_are_admissible(0));
        assert!(ledger_data_nodes_are_admissible(1));
        assert!(ledger_data_nodes_are_admissible(
            overlay::HARD_MAX_REPLY_NODES
        ));
        assert!(!ledger_data_nodes_are_admissible(
            overlay::HARD_MAX_REPLY_NODES + 1,
        ));
    }

    #[test]
    fn candidate_ledger_data_outcomes_use_reference_resource_fees() {
        let no_acquire =
            candidate_ledger_data_charge(&ledger::InboundTransactionsDataStatus::NoAcquire)
                .expect("unknown candidate set must be charged");
        assert_eq!(no_acquire.0.cost(), resource::FEE_USELESS_DATA.cost());
        assert_eq!(no_acquire.1, "ledger_data");

        let missing_id =
            candidate_ledger_data_charge(&ledger::InboundTransactionsDataStatus::MissingNodeId)
                .expect("missing candidate node id must be charged");
        assert_eq!(missing_id.0.cost(), resource::FEE_MALFORMED_REQUEST.cost());

        let invalid_id =
            candidate_ledger_data_charge(&ledger::InboundTransactionsDataStatus::InvalidNodeId)
                .expect("invalid candidate node id must be charged");
        assert_eq!(invalid_id.0.cost(), resource::FEE_INVALID_DATA.cost());

        let useful =
            ledger::InboundTransactionsDataStatus::Applied(shamap::sync::SHAMapAddNode::useful());
        assert!(candidate_ledger_data_charge(&useful).is_none());
    }

    #[test]
    fn earliest_fetch_floor_applies_independently_of_selector() {
        assert!(!sequence_is_fetchable_at_floor(99, 100));
        assert!(sequence_is_fetchable_at_floor(100, 100));
        assert!(sequence_is_fetchable_at_floor(101, 100));
    }

    #[test]
    fn fetch_pack_admission_matches_peerimp_load_age_queue_and_hash_gates() {
        let valid = basics::base_uint::Uint256::from_u64(0x42);
        assert_eq!(
            classify_fetch_pack_request(false, Duration::from_secs(40), 10, Some(valid.data())),
            FetchPackAdmission::Accepted(valid),
        );
        assert_eq!(
            classify_fetch_pack_request(true, Duration::default(), 0, Some(valid.data())),
            FetchPackAdmission::Busy,
        );
        assert_eq!(
            classify_fetch_pack_request(false, Duration::from_secs(41), 0, Some(valid.data())),
            FetchPackAdmission::Busy,
        );
        assert_eq!(
            classify_fetch_pack_request(false, Duration::default(), 11, Some(valid.data())),
            FetchPackAdmission::Busy,
        );
        assert_eq!(
            classify_fetch_pack_request(false, Duration::default(), 0, Some(&[7; 31])),
            FetchPackAdmission::Malformed,
        );
        assert_eq!(
            classify_fetch_pack_request(false, Duration::default(), 0, None),
            FetchPackAdmission::Malformed,
        );
    }

    #[test]
    fn fetch_pack_missing_initial_predecessor_charges_no_reply() {
        let (fee, context) = fetch_pack_failure_charge(
            ledger::FetchPackBuildError::RequestedLedgerPredecessorMissing,
        )
        .expect("missing initial predecessor must charge rather than silently return");
        assert_eq!(fee.cost(), resource::FEE_REQUEST_NO_REPLY.cost());
        assert_eq!(context, "get_object ledger");
        assert!(fetch_pack_failure_charge(ledger::FetchPackBuildError::Stale).is_none());
        let (traversal_fee, traversal_context) =
            fetch_pack_failure_charge(ledger::FetchPackBuildError::Traversal)
                .expect("unresolved historical SHAMap traversal must not emit a partial pack");
        assert_eq!(traversal_fee.cost(), resource::FEE_REQUEST_NO_REPLY.cost());
        assert_eq!(traversal_context, "get_object ledger");
    }

    #[test]
    fn shutdown_watcher_exits_when_stop_is_already_requested() {
        let runtime = Arc::new(MainRuntime::new(
            ApplicationRoot::new(0).expect("root should build"),
        ));
        let stop_requested = Arc::new(AtomicBool::new(true));

        let handle = spawn_shutdown_watcher(runtime, stop_requested);
        handle.join().expect("watcher should exit cleanly");
    }

    #[test]
    fn b1_resource_charge_vectors_use_reference_fee_schedule() {
        assert_eq!(resource::FEE_INVALID_DATA.cost(), 400);
        assert_eq!(resource::FEE_USELESS_DATA.cost(), 150);
        assert_eq!(resource::FEE_MALFORMED_REQUEST.cost(), 200);
        assert_eq!(resource::FEE_MODERATE_BURDEN_PEER.cost(), 250);
    }

    #[test]
    fn bootstrap_ledger_data_router_maps_all_admission_dispositions_without_deferred_actor_route() {
        use crate::ledger::inbound_ledgers::{AcquireReason, InboundLedgers};

        /// Build the same real in-memory node store used by the inbound-ledger
        /// fixtures. `acquire` rejects creation without an attached store, so
        /// an admitted response can only reach actor routing through a real
        /// registry entry.
        fn test_node_store() -> (TempDir, crate::SHAMapStoreNodeStore) {
            let dir = TempDir::new().expect("tempdir");
            let mut config = BasicConfig::new();
            config.set_legacy("database_path", dir.path().join("sql").to_string_lossy());
            let node_db = config.section_mut("node_db");
            node_db.set("type", "Memory");
            node_db.set("path", dir.path().join("node").to_string_lossy());

            let bootstrap = crate::bootstrap_shamap_store(
                &config,
                false,
                128,
                1,
                8,
                64,
                2,
                &ManagerImp::new(),
                Arc::new(DummyScheduler) as Arc<dyn Scheduler>,
                Arc::new(NullJournal),
            )
            .expect("bootstrap");
            (dir, bootstrap.node_store)
        }

        fn registry() -> (TempDir, Arc<InboundLedgers>) {
            let (dir, node_store) = test_node_store();
            let (completed_tx, _completed_rx) = mpsc::sync_channel(1);
            let registry = Arc::new(InboundLedgers::new(
                Arc::new(TreeNodeCache::new(
                    "bootstrap-ledger-data-router-test",
                    8,
                    time::Duration::seconds(60),
                    MonotonicClock::default(),
                )),
                Arc::new(FullBelowCacheImpl::new(
                    1,
                    MonotonicClock::default(),
                    HardenedHashBuilder::default(),
                    8,
                )),
                Arc::new(FetchPackCache::new(
                    8,
                    time::Duration::seconds(60),
                    MonotonicClock::default(),
                )),
                completed_tx,
                Arc::new(AtomicBool::new(false)),
            ));
            registry.set_node_store(node_store);
            (dir, registry)
        }

        fn base_reply(hash: Uint256) -> overlay::TmLedgerData {
            overlay::TmLedgerData {
                ledger_hash: hash.data().to_vec(),
                ledger_seq: 1,
                r#type: 0,
                nodes: vec![overlay::message::wire::TmLedgerNode {
                    nodeid: None,
                    nodedata: vec![0],
                    reference: None,
                }],
                request_cookie: None,
                error: None,
            }
        }

        let (_admitted_dir, admitted) = registry();
        let admitted_hash = Uint256::from_array([0xA1; 32]);
        assert!(
            admitted
                .acquire(admitted_hash, 1, AcquireReason::Generic)
                .is_none()
        );
        let first_routing =
            route_bootstrap_ledger_data(&admitted, admitted_hash, 7, &base_reply(admitted_hash));
        assert_eq!(
            first_routing,
            BootstrapLedgerDataRouting {
                disposition: LedgerDataIngressDisposition::Delivered,
                charge_unsolicited: false,
            },
            "LedgerDataAdmission::Admitted consumes exactly one lease into actor routing"
        );
        let admitted_lifecycle = admitted.lifecycle_snapshot();
        assert_eq!(admitted_lifecycle.route_attempts, 1);
        assert_eq!(admitted_lifecycle.route_accepted, 1);
        admitted.stop();

        let (_deferred_dir, deferred) = registry();
        let deferred_hash = Uint256::from_array([0xD2; 32]);
        assert!(
            deferred
                .acquire(deferred_hash, 1, AcquireReason::Generic)
                .is_none()
        );
        let reservation_packet =
            ledger::InboundLedgerPacket::new(ledger::InboundLedgerDataType::Base, Vec::new());
        let mut leases =
            Vec::with_capacity(crate::ledger::inbound_ledgers::ACQ_MAILBOX_PACKET_CAPACITY);
        for _ in 0..crate::ledger::inbound_ledgers::ACQ_MAILBOX_PACKET_CAPACITY {
            let crate::ledger::inbound_ledgers::LedgerDataAdmission::Admitted(lease) =
                deferred.reserve_response_admission(&deferred_hash, &reservation_packet)
            else {
                panic!("every mailbox reservation through the exact capacity must admit");
            };
            leases.push(lease);
        }
        assert_eq!(
            route_bootstrap_ledger_data(&deferred, deferred_hash, 8, &base_reply(deferred_hash)),
            BootstrapLedgerDataRouting {
                disposition: LedgerDataIngressDisposition::Deferred,
                charge_unsolicited: false,
            },
            "LedgerDataAdmission::Deferred retains the frame in transport and does not charge or route it"
        );
        let deferred_lifecycle = deferred.lifecycle_snapshot();
        assert_eq!(deferred_lifecycle.route_attempts, 0);
        assert_eq!(deferred_lifecycle.route_accepted, 0);
        drop(leases);
        deferred.stop();

        let (_unmatched_dir, unmatched) = registry();
        let unmatched_hash = Uint256::from_array([0xC3; 32]);
        assert_eq!(
            route_bootstrap_ledger_data(&unmatched, unmatched_hash, 9, &base_reply(unmatched_hash)),
            BootstrapLedgerDataRouting {
                disposition: LedgerDataIngressDisposition::Delivered,
                charge_unsolicited: true,
            },
            "LedgerDataAdmission::Unmatched is terminally delivered as unsolicited Base data"
        );
        assert_eq!(unmatched.lifecycle_snapshot().route_attempts, 0);
        unmatched.stop();

        let (_terminal_dir, terminal) = registry();
        let terminal_hash = Uint256::from_array([0xE4; 32]);
        assert!(
            terminal
                .acquire(terminal_hash, 1, AcquireReason::Generic)
                .is_none()
        );
        terminal.on_failed(terminal_hash);
        assert_eq!(
            route_bootstrap_ledger_data(&terminal, terminal_hash, 10, &base_reply(terminal_hash)),
            BootstrapLedgerDataRouting {
                disposition: LedgerDataIngressDisposition::Delivered,
                charge_unsolicited: true,
            },
            "LedgerDataAdmission::Terminal does not defer or enqueue a failed acquisition reply"
        );
        let terminal_lifecycle = terminal.lifecycle_snapshot();
        assert_eq!(terminal_lifecycle.route_attempts, 0);
        assert_eq!(terminal_lifecycle.route_accepted, 0);
        terminal.stop();
    }
}
