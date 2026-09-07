//! Honest application-root owner for the migrated runtime shell.

use crate::amendments::amendment_status::{AmendmentStatus, UnsupportedMajorityWarningDetails};
use crate::consensus::rcl_consensus::RclConsensusOpenLedgerSource;
use crate::consensus::rcl_validations::SharedAppValidations;
use crate::job::job_queue::JobQueue;
use crate::ledger::ledger_master_runtime::AppLedgerMasterRuntime;
use crate::ledger::ledger_master_state::SharedLedgerMasterState;
use crate::load::fee_vote::FeeSetup;
use crate::load::load_fee_track::SharedLoadFeeTrack;
use crate::load::load_manager::{LoadManager, LoadManagerTiming};
use crate::network::network_ops::networkops_apply_flags;
use crate::network::network_ops::{
    AppNetworkOpsModeOwner, NetworkOpsOperatingMode, SharedNetworkOpsState,
    normalize_operating_mode_for_validated_age,
};
use crate::network::network_ops_runtime::{
    AppNetworkOpsApplyHeldOutcome, AppNetworkOpsApplyReport, AppNetworkOpsRuntime,
    AppNetworkOpsSubmitReport,
};
use crate::network::network_ops_validation_runtime::{
    AppNetworkOpsValidationReceiveReport, AppNetworkOpsValidationRuntime,
};
use crate::node_family::node_family::{NodeFamily, NodeFamilyRuntime};
use crate::runtime::component_runtime::{
    AppConsensusRuntime, AppLedgerRuntime, AppNodeStoreRuntime, AppPerfLogRuntime,
    AppValidatorSiteRuntime,
};
use crate::runtime::main_runtime::{GrpcRuntime, ManagedComponent, ManagedHandle, RuntimeBindings};
use crate::runtime::overlay_runtime::{AppOverlayRuntime, build_overlay_runtime};
use crate::runtime::resolver_runtime::AppResolverRuntime;
use crate::server::server_okay::server_okay;
use crate::server::server_ports::{
    PublishedServerPortsSource, ServerPortsSetup, build_server_ports_setup,
};
use crate::shamap::shamap_store_component::SHAMapStoreComponent;
use crate::shamap::shamap_store_health::SHAMapStoreOperatingMode;
use crate::shamap::shamap_store_service::SHAMapStoreService;
use crate::state::accept_ledger_pending_apply::AcceptLedgerPendingApplyRuntime;
use crate::state::app_registry::{
    AppAcceptedLedgerCache, AppConfig, AppInboundLedgers, AppInboundTransactions, AppLogs,
    AppOpenLedgerTxRecord, AppOpenLedgerView, AppPlaceholder, AppQueueApplyTxSource,
    AppRequiredFeeView, AppServerHandler, AppTxQAccount, AppTxQJournalTag, AppTxQLock,
    AppTxQParentBatchId, AppTxQTransaction, ApplicationRegistryOwners, RelayUntrustedPolicy,
    SharedAppOpenLedger, SharedAppTxQ,
};
use crate::state::basic_app::BasicApp;
use crate::state::candidate_diagnostics::{
    CandidateAdmissionDiagnostic, CandidateDiagnosticDecision, emit_candidate_admission_diagnostic,
};
use crate::state::collector_manager::{CollectorManager, CollectorParams};
use crate::state::manifest::{ManifestCache, ManifestLimits};
use crate::state::node_store_scheduler::NodeStoreScheduler;
use crate::state::overlay_status::OverlayStatusSource;
use crate::state::snapshot_export_state::{SnapshotExportState, SnapshotExportStatus};
use crate::state::status_metrics::StatusMetricsSource;
use crate::state::status_rpc_state::{StatusRpcGitInfo, StatusRpcLastClose, StatusRpcState};
use crate::state::stop_tree::{StopTree, StopTreeNode};
use crate::state::time_keeper::{SystemTimeKeeperClock, TimeKeeper};
use crate::state::transactor_dispatcher::handle_real_dispatch;
use crate::tx_queue::transaction::{Transaction, TransactionCloseTimeSource};
use crate::tx_queue::transaction_master::{SharedTransaction, TransactionMaster};
use crate::validator::validator_list::{
    ListDisposition, PublisherListStats, SystemValidatorListClock, ValidatorBlobInfo,
    ValidatorList, ValidatorListStatusSnapshot,
};
use crate::validator::validator_site::ValidatorSite;
use basics::base_uint::{Uint160, Uint256};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::MonotonicClock;
use ledger::OrderBookDB;
use ledger::{
    ApplyView, CanonicalTXSet, Ledger, LedgerMasterCaughtUp, LedgerNodeObjectType,
    NullOrderBookDBJournal, NullOrderBookDBRuntime, OpenView, ReadView, Sandbox, TxsRawView,
};
use overlay::Cluster;
use overlay::{OverlayHandoff, OverlayImpl, PeerReservationSource};
use perflog::PerfLogImp;
use protocol::{
    AccountID, BatchTransactionFlags, JsonOptions, JsonValue, NodeID, NotTec, PublicKey,
    REFERENCE_FEE_UNITS_DEPRECATED, Rules, STAmount, STLedgerEntry, STObject, STTx, SecretKey,
    SeqProxy, Serializer, StBase, Ter, TxType, XRPAmount, account_keylet, calc_account_id,
    calc_node_id, feature_xrp_fees, get_field_by_symbol, is_tec_claim, is_tef_failure,
    is_tem_malformed, is_tes_success, lsfDisableMaster, tfInnerBatchTxn,
};
use quaxar_core::DatabaseCon;
use shamap::family::{NullMissingNodeReporter, NullNodeFetcher};
use shamap::tree_node_cache::TreeNodeCache;
use std::{
    collections::BTreeSet,
    sync::{Arc, Mutex},
};
use time::{Duration, OffsetDateTime};
use tx::{
    ApplyFlags, ApplyResult, HasTxnType, PreclaimResult, PreflightResult,
    QueueAcceptLedgerViewSource, QueueAcceptLiveApplyRuntime, QueueApplyExecutionRuntime,
    QueueFeeLevelPaidInputs, QueueTxQClosedLedgerAppSource, QueueTxQClosedLedgerView,
    QueueTxQMetrics, QueueTxQRpcReport, TxConsequences, TxDetails, evaluate_fee_level_paid,
    likely_to_claim_fee, snapshot_queue_apply_app_view_with_metrics,
};

use xrpl_core::{
    FixedNetworkIdService, HashRouter, LoadMonitorJournalFactory, NetworkIDService,
    PeerReservationTable, ServiceRegistry, StartUpType,
};

#[path = "application_root/replay_callback_impl.rs"]
mod replay_callback_impl;

fn to_nodestore_type(object_type: LedgerNodeObjectType) -> nodestore::NodeObjectType {
    match object_type {
        LedgerNodeObjectType::AccountNode => nodestore::NodeObjectType::AccountNode,
        LedgerNodeObjectType::TransactionNode => nodestore::NodeObjectType::TransactionNode,
    }
}

fn consensus_status_event(event: i32, have_correct_lcl: bool) -> i32 {
    if have_correct_lcl { event } else { 4 } // neLOST_SYNC
}

fn advertised_ledger_range(
    full_range: (u32, u32),
    minimum_online: Option<u32>,
    earliest_fetch: u32,
) -> (u32, u32) {
    let (first, last) = full_range;
    (
        first
            .max(minimum_online.unwrap_or_default())
            .max(earliest_fetch),
        last,
    )
}

/// Reference `LedgerMaster::setValidLedger` uses the median signing time of
/// trusted validations. For an even sample, average the two middle elements
/// without overflow; if quorum has not been reached, retain the ledger close
/// time as the only trustworthy fallback.
fn median_validation_sign_time(mut sign_times: Vec<u32>, quorum: usize, fallback: u32) -> u32 {
    if quorum == 0 || sign_times.len() < quorum {
        return fallback;
    }
    sign_times.sort_unstable();
    let low = sign_times[(sign_times.len() - 1) / 2];
    let high = sign_times[sign_times.len() / 2];
    low.saturating_add((high - low) / 2)
}

/// Mirrors `LedgerMaster::getNeededValidations`: standalone accepts without
/// network validation while every non-standalone path uses the configured UNL
/// quorum.
fn needed_validations(standalone: bool, quorum: usize) -> usize {
    if standalone { 0 } else { quorum }
}

/// Mirrors the resolver-miss branch of `LedgerMaster::checkAccept(hash, seq)`:
/// only a quorum-backed nonzero validation with no valid ledger can update peer
/// convergence before generic acquisition is requested.
fn should_check_tracking_on_validation_resolver_miss(
    seq: u32,
    valid_ledger_seq: u32,
    validation_count: usize,
    quorum: usize,
) -> bool {
    seq != 0 && valid_ledger_seq == 0 && validation_count >= quorum
}

/// `LedgerMaster::consensusBuilt` intentionally uses a strict threshold when
/// scanning alternate current-validation candidates, unlike `checkAccept`.
fn consensus_built_alternate_threshold_met(validation_count: usize, needed: usize) -> bool {
    validation_count > needed
}

/// Group the already filtered *current* trusted validations exactly as
/// `LedgerMaster::consensusBuilt`'s local `ValSeq` map does. Historical
/// validation sets are deliberately not consulted here; they belong only to
/// the subsequent `checkAccept(hash, seq)` call.
fn consensus_built_current_validation_counts(
    validations: impl IntoIterator<Item = (Uint256, u32)>,
) -> std::collections::HashMap<Uint256, (usize, u32)> {
    let mut counts = std::collections::HashMap::new();
    for (hash, seq) in validations {
        let entry = counts.entry(hash).or_insert((0, 0));
        entry.0 += 1;
        // Match rippled ValSeq::mergeValidation: retain the first known
        // nonzero sequence for a ledger hash even if an earlier validation
        // omitted sfLedgerSequence.
        if entry.1 == 0 {
            entry.1 = seq;
        }
    }
    counts
}

/// A preferred LCL equal to the local closed ledger or its immediate parent
/// cannot justify an abnormal jump. This test-only predicate keeps the mode
/// promotion regression assertion explicit without introducing another
/// production LCL policy owner.
#[cfg(test)]
fn preferred_lcl_matches_local_or_parent(
    local_hash: Uint256,
    parent_hash: Uint256,
    preferred_hash: Uint256,
) -> bool {
    preferred_hash == local_hash || preferred_hash == parent_hash
}

fn full_sync_debug_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("QUAXAR_FULL_SYNC_DEBUG")
            .map(|value| value == "1" || value.eq_ignore_ascii_case("true"))
            .unwrap_or(false)
    })
}

macro_rules! full_sync_debug {
    ($($arg:tt)*) => {
        if crate::state::application_root::full_sync_debug_enabled() {
            tracing::debug!(target: "full_sync", $($arg)*);
        }
    };
}

#[derive(Clone)]
struct AppLoadManagerEvents {
    collector_manager: CollectorManager,
    fee_change_reporter: Arc<FeeChangeReporter>,
}

impl crate::load::load_manager::LoadManagerEvents for AppLoadManagerEvents {
    fn report_fee_change(&self) {
        self.collector_manager
            .group("load_manager")
            .record_event("fee_change");
        // LoadManager outlives no ApplicationRoot state: it holds this
        // standalone reporter, not a root callback. A stopped JobQueue rejects
        // the work cleanly, and normal reports retain the server-stream
        // deduplication shared with all other fee-change paths.
        let _ = self.fee_change_reporter.report_fee_change();
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ApplicationRootOptions {
    pub io_threads: usize,
    pub job_queue_threads: usize,
    /// Node network ID used by transaction preflight before an overlay runtime
    /// is attached. Production startup replaces it from the configured
    /// overlay; deterministic ledger builders and parity fixtures set it here.
    pub network_id: u32,
    pub start_valid: bool,
    pub elb_support: bool,
    pub standalone: bool,
    pub start_type: StartUpType,
    pub start_ledger: Option<String>,
    pub import: bool,
    pub quorum: Option<usize>,
    /// rippled Config::networkQuorum, passed to NetworkOPs at construction.
    pub network_quorum: usize,
    /// Maximum ledger depth this node advertises and serves to peers.
    pub ledger_fetch_depth: u32,
    /// Target fee schedule advertised by this validator on voting ledgers.
    /// The reference reads this from the configured `[voting]` section.
    pub fee_setup: FeeSetup,
    pub collector_params: CollectorParams,
    pub load_manager_timing: LoadManagerTiming,
}

impl Default for ApplicationRootOptions {
    fn default() -> Self {
        Self {
            io_threads: 1,
            job_queue_threads: 1,
            network_id: 0,
            start_valid: false,
            elb_support: false,
            standalone: false,
            start_type: StartUpType::Fresh,
            start_ledger: None,
            import: false,
            quorum: None,
            network_quorum: 1,
            ledger_fetch_depth: u32::MAX,
            fee_setup: FeeSetup::default(),
            collector_params: CollectorParams::default(),
            load_manager_timing: LoadManagerTiming::default(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ClosedLedgerHistoryAction {
    Store,
    AlreadyStored,
}

/// The fee fields emitted on the `server` stream. This mirrors rippled's
/// `NetworkOPsImp::ServerFeeSummary`: notification is driven by the fee
/// values themselves, not by every OpenLedger acceptance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ServerFeeSummary {
    load_factor_server: u32,
    load_base_server: u32,
    base_fee: u64,
    min_processing_fee_level: u64,
    open_ledger_fee_level: u64,
    reference_fee_level: u64,
}

impl ServerFeeSummary {
    fn load_factor(self) -> u64 {
        let fee_escalation = basics::mul_div::mul_div(
            self.open_ledger_fee_level,
            u64::from(self.load_base_server),
            self.reference_fee_level,
        )
        .unwrap_or(u64::MAX);
        u64::from(self.load_factor_server).max(fee_escalation)
    }
}

type SubscriptionPublisher = Arc<dyn Fn(&str, protocol::JsonValue) + Send + Sync + 'static>;
type SharedSubscriptionPublisher = Arc<std::sync::RwLock<Option<SubscriptionPublisher>>>;

/// The lifecycle-independent portion of `NetworkOPs::reportFeeChange`.
///
/// It deliberately owns only the shared application services it needs, not an
/// `ApplicationRoot`. `LoadManager` can therefore report fee changes without a
/// root-reference cycle, while a stopped job queue makes late shutdown reports
/// harmless.
#[derive(Clone)]
struct FeeChangeReporter {
    job_queue: Arc<JobQueue>,
    load_fee_track: Arc<SharedLoadFeeTrack>,
    open_ledger: SharedAppOpenLedger,
    tx_q: SharedAppTxQ,
    network_ops_state: Arc<SharedNetworkOpsState>,
    subscription_manager: SharedSubscriptionPublisher,
    last_summary: Arc<Mutex<Option<ServerFeeSummary>>>,
}

impl FeeChangeReporter {
    fn server_fee_summary(&self) -> ServerFeeSummary {
        let current = self.open_ledger.current();
        let mut lock = AppTxQLock;
        let metrics = self.tx_q.get_metrics(&mut lock, current.as_ref());
        ServerFeeSummary {
            load_factor_server: self.load_fee_track.load_factor(),
            load_base_server: self.load_fee_track.load_base(),
            base_fee: current.base_fee_drops,
            min_processing_fee_level: metrics.min_processing_fee_level,
            open_ledger_fee_level: metrics.open_ledger_fee_level,
            reference_fee_level: metrics.reference_fee_level,
        }
    }

    fn fee_change_payload(&self, summary: ServerFeeSummary) -> JsonValue {
        JsonValue::Object(std::collections::BTreeMap::from([
            (
                "type".to_owned(),
                JsonValue::String("serverStatus".to_owned()),
            ),
            (
                "server_status".to_owned(),
                JsonValue::String(self.network_ops_state.operating_mode().as_str().to_owned()),
            ),
            (
                "load_base".to_owned(),
                JsonValue::Unsigned(u64::from(summary.load_base_server)),
            ),
            (
                "load_factor_server".to_owned(),
                JsonValue::Unsigned(u64::from(summary.load_factor_server)),
            ),
            (
                "load_factor".to_owned(),
                JsonValue::Unsigned(summary.load_factor()),
            ),
            (
                "load_factor_fee_escalation".to_owned(),
                JsonValue::Unsigned(summary.open_ledger_fee_level),
            ),
            (
                "load_factor_fee_queue".to_owned(),
                JsonValue::Unsigned(summary.min_processing_fee_level),
            ),
            (
                "load_factor_fee_reference".to_owned(),
                JsonValue::Unsigned(summary.reference_fee_level),
            ),
            ("base_fee".to_owned(), JsonValue::Unsigned(summary.base_fee)),
        ]))
    }

    fn report_fee_change(&self) -> bool {
        let publisher = self
            .subscription_manager
            .read()
            .ok()
            .and_then(|guard| guard.as_ref().cloned());
        let Some(publisher) = publisher else {
            return false;
        };

        let summary = self.server_fee_summary();
        let payload = self.fee_change_payload(summary);
        let mut last_summary = self
            .last_summary
            .lock()
            .expect("last fee summary mutex must not be poisoned");
        if *last_summary == Some(summary) {
            return false;
        }

        let scheduled = self.job_queue.add_job(
            crate::job::job_types::JobType::JtClientFeeChange,
            "feeChange",
            move || publisher("server", payload),
        );
        if scheduled {
            *last_summary = Some(summary);
        }
        scheduled
    }
}

fn queue_relay_envelope(
    raw_transaction: Vec<u8>,
    local_timestamp: u64,
    locally_queued: bool,
) -> overlay::TmTransaction {
    overlay::TmTransaction {
        raw_transaction,
        status: 2, // tsCURRENT
        receive_timestamp: Some(local_timestamp),
        deferred: Some(locally_queued),
    }
}

/// Replay startup is parked here only when the locally persisted parent
/// header exists but `walk_ledger` proves its SHAMap is incomplete. The
/// runtime uses this immutable request to acquire that exact parent through
/// `InboundLedgers`; it must not synthesize a full ledger from the header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PendingReplayStartup {
    pub parent_hash: Uint256,
    pub parent_seq: u32,
    pub start_ledger: Option<String>,
    pub trap_tx_hash: Option<Uint256>,
}

/// The minimal owner-visible state that defines a publication plan. The epoch
/// records lifecycle changes that a hash/sequence snapshot cannot express
/// (for example, a failed or swept Generic acquisition).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PublicationPlanIdentity {
    validated: Option<(Uint256, u32)>,
    published: Option<(Uint256, u32)>,
    missing: Option<(Uint256, u32)>,
}

impl PublicationPlanIdentity {
    fn heads(lm: &crate::AppLedgerMaster) -> (Option<(Uint256, u32)>, Option<(Uint256, u32)>) {
        let validated = lm
            .validated_ledger()
            .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq));
        let published = lm
            .published_ledger()
            .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq));
        (validated, published)
    }

    fn from_report(
        lm: &crate::AppLedgerMaster,
        report: &crate::ledger::ledger_master_runtime::AppLedgerMasterAdvanceReport,
    ) -> Self {
        let (validated, published) = Self::heads(lm);
        Self {
            validated,
            published,
            missing: report.missing.map(|missing| (missing.hash, missing.seq)),
        }
    }

    fn matches_heads(&self, heads: (Option<(Uint256, u32)>, Option<(Uint256, u32)>)) -> bool {
        self.validated == heads.0 && self.published == heads.1
    }
}

/// Rust's equivalent of LedgerMaster's `advanceWork_`/`advanceThread_` gate.
/// The NetworkOps strand remains the only execution owner; outside lifecycle
/// callbacks only advance this coalesced event epoch and wake that strand.
#[derive(Debug)]
struct PublicationAdvanceState {
    requested_epoch: u64,
    planned_epoch: u64,
    last_plan: Option<PublicationPlanIdentity>,
    /// One exact Worker-2 lifecycle may block its own publication. This does
    /// not suppress unrelated validated or publication planning work.
    provisional_deferral: Option<PublicationDeferral>,
}

#[derive(Clone, Copy, Debug)]
struct PublicationDeferral {
    identity: crate::ledger::inbound_ledgers::ProvisionalLedgerIdentity,
    suppression_logged: bool,
}

impl Default for PublicationAdvanceState {
    fn default() -> Self {
        // The initial validated/published state requires one planning pass
        // after the LedgerMaster runtime is attached.
        Self {
            requested_epoch: 1,
            planned_epoch: 0,
            last_plan: None,
            provisional_deferral: None,
        }
    }
}

#[derive(Clone)]
pub struct ApplicationRoot {
    registry: ApplicationRegistryOwners,
    manifest_limits: ManifestLimits,
    basic_app: Arc<BasicApp>,
    job_queue: Arc<JobQueue>,
    /// Shared, persistent ledger persistence runtime -- constructed once so
    /// its hash-router-style dedup (`saved_hashes`) and pending-save gating
    /// (`pending`) are real bookkeeping across calls, matching the
    /// reference's long-lived `HashRouter`/`PendingSaves` members on
    /// `Application`. Rebuilt (state reset) only when storage targets
    /// change, which happens once at startup, not on the hot path.
    ledger_persistence_runtime: Arc<std::sync::RwLock<Arc<crate::AppLedgerPersistenceRuntime>>>,
    time_keeper: Arc<TimeKeeper<SystemTimeKeeperClock>>,
    /// Built-in SNTP client for environments where host NTP cannot be
    /// configured (LXC, Docker, managed VPS).  `None` when not initialised.
    sntp_client: Option<crate::state::sntp::SntpClient>,
    stop_tree: Arc<StopTree>,
    collector_manager: Arc<CollectorManager>,
    load_manager: Arc<LoadManager>,
    load_fee_track: Arc<SharedLoadFeeTrack>,
    /// Configured `[voting]` fee targets supplied to the consensus adaptor.
    fee_vote_setup: FeeSetup,
    ledger_fetch_depth: u32,
    /// Lifecycle-safe server fee reporter shared with LoadManager and the
    /// normal NetworkOps/consensus paths.
    fee_change_reporter: Arc<FeeChangeReporter>,
    node_store_scheduler: Arc<NodeStoreScheduler>,
    node_family: Option<Arc<dyn NodeFamilyRuntime>>,
    resolver_runtime: Option<Arc<AppResolverRuntime>>,
    overlay_runtime: Option<Arc<AppOverlayRuntime>>,
    overlay_status: Option<Arc<dyn OverlayStatusSource>>,
    server_ports_setup: Option<Arc<ServerPortsSetup>>,
    published_server_ports: Option<Arc<dyn PublishedServerPortsSource>>,
    status_metrics: Option<Arc<dyn StatusMetricsSource>>,
    ledger_delta_publisher: Option<Arc<dyn Fn(protocol::JsonValue) + Send + Sync + 'static>>,
    /// Callback to notify WebSocket subscribers when a ledger closes.
    /// Wired to SubscriptionManager::publish_json(StreamKind::Ledger, ...).
    ledger_close_publisher: Option<Arc<dyn Fn(protocol::JsonValue) + Send + Sync + 'static>>,
    /// Callback to notify WebSocket subscribers when a transaction is applied.
    transaction_publisher: Option<Arc<dyn Fn(protocol::JsonValue) + Send + Sync + 'static>>,
    /// Shared subscription manager from the RPC server. Populated when the
    /// server starts, used by accept_standalone_ledger to push notifications.
    shared_subscription_manager: Arc<
        std::sync::RwLock<Option<Arc<dyn Fn(&str, protocol::JsonValue) + Send + Sync + 'static>>>,
    >,
    network_ops_state: Arc<SharedNetworkOpsState>,
    network_ops_runtime: Option<Arc<AppNetworkOpsRuntime>>,
    network_ops_validation_runtime: Option<Arc<AppNetworkOpsValidationRuntime>>,
    ledger_master_runtime: Option<Arc<AppLedgerMasterRuntime>>,
    consensus_runtime: Option<Arc<AppConsensusRuntime>>,
    ledger_master_state: Arc<SharedLedgerMasterState>,
    transaction_master: Arc<TransactionMaster>,
    /// Strong lifecycle owner for the weak ConsensusTransSetSF -> NetworkOPs
    /// submission handoff. Temporarily removed before cloning the submit root
    /// so the callback cannot form an ApplicationRoot reference cycle.
    consensus_tx_set_submit_adapter:
        Option<Arc<crate::consensus::consensus_trans_set_sf::ConsensusFetchedTxSubmitAdapter>>,
    validations: SharedAppValidations<SystemTimeKeeperClock>,
    validators: Arc<ValidatorList>,
    status_rpc_state: Arc<StatusRpcState>,
    snapshot_export_state: Arc<SnapshotExportState>,
    amendment_status: Arc<AmendmentStatus>,
    elb_support: bool,
    node_identity: Option<(PublicKey, SecretKey)>,
    validation_public_key: Option<PublicKey>,
    runtime_bindings: RuntimeBindings,
    shamap_store_service: Option<Arc<SHAMapStoreService>>,
    /// Shared node store for ConsensusLedgerAcceptor. Populated by attach_node_store.
    shared_consensus_node_store:
        Arc<std::sync::RwLock<Option<crate::shamap::shamap_store_backend::SHAMapStoreNodeStore>>>,
    /// Shared consensus runtime reference. Populated by attach_default_consensus_runtime.
    /// Used by the JtAccept job to call start_next_round (matching rippled's
    /// doAccept → endConsensus → beginConsensus atomic pattern). Arc<RwLock>
    /// ensures all ApplicationRoot clones see the attachment.
    shared_consensus_rt: Arc<std::sync::RwLock<Option<Arc<AppConsensusRuntime>>>>,
    /// Shared network ops runtime reference. Populated by bind_default_component_runtimes.
    shared_network_ops_rt: Arc<std::sync::RwLock<Option<Arc<AppNetworkOpsRuntime>>>>,
    /// Signal from bootstrap/consensus loop to InboundLedger workers that
    /// the shared fetch-pack cache was populated. Workers should re-check
    /// local storage immediately (matching rippled gotFetchPack).
    fetch_pack_ready: Arc<std::sync::atomic::AtomicBool>,
    /// A replay request whose historical parent is known locally by header
    /// but lacks reachable SHAMap nodes. It is consumed only after inbound
    /// history acquisition has durably completed.
    pending_replay_startup: Arc<Mutex<Option<PendingReplayStartup>>>,
    /// Tracks the next expected sequence for each account with pending open ledger txs.
    /// Cleared on ledger_accept. Matches rippled's persistent OpenView behavior where
    /// account sequences are updated during submit and visible to subsequent submits.
    open_ledger_account_seqs:
        Arc<std::sync::Mutex<std::collections::HashMap<protocol::AccountID, u32>>>,
    /// Persistent submit sandbox matching rippled's OpenView. Accumulates state changes
    /// across submit calls within the same open ledger period. Reset on ledger_accept.
    open_ledger_sandbox: Arc<std::sync::Mutex<Option<Sandbox<ledger::OpenView<Ledger>>>>>,
    /// Close gate: serializes on_close's apply+capture with NetworkOPs batch
    /// application. rippled protects this work with its application and ledger
    /// locks; the Rust runtime uses this narrow gate around the same mutable
    /// open-ledger transition.
    close_gate: Arc<std::sync::Mutex<()>>,
    /// Serializes each LCL promotion with the complete consensus accept and
    /// next-round handoff. It is re-entrant because consensus-built checking
    /// can synchronously promote a preferred LCL on the same strand.
    lcl_transition_gate: Arc<parking_lot::ReentrantMutex<()>>,
    /// Serializes validation acceptance with publication planning and commit.
    /// Rippled holds LedgerMaster::mutex_ across this equivalent checkAccept →
    /// tryAdvance path; keep it separate from the re-entrant LCL transition
    /// gate because it never recursively switches the closed ledger.
    validation_advance_gate: Arc<parking_lot::Mutex<()>>,
    /// Coalesced owner event and last plan identity for validated-to-published
    /// advancement. Lifecycle callbacks may request work, but only the
    /// validation/NetworkOps serialized paths execute it.
    publication_advance: Arc<Mutex<PublicationAdvanceState>>,
    /// Condvar to wake the consensus strand loop immediately when proposals
    /// arrive from the overlay, removing the 50ms poll latency. Matches
    /// rippled's strand-based immediate dispatch of proposals.
    consensus_notify: Arc<(std::sync::Mutex<bool>, std::sync::Condvar)>,
    /// Shared tree-node cache — the single `TreeNodeCache` instance shared
    /// across all SHAMaps via `SHAMapFamily`. Attached by bootstrap after
    /// creation. Used by `persist_dirty_nodes_to_store` to canonicalize
    /// flushed nodes into the cache (matching rippled's `SHAMap::writeNode`
    /// which calls `canonicalize` + `db().store()`).
    shared_tree_cache: std::sync::OnceLock<
        Arc<TreeNodeCache<MonotonicClock, basics::hardened_hash::HardenedHashBuilder>>,
    >,
    /// Maximum disallowed ledger sequence — set from the relational database's
    /// highest stored ledger for validator nodes. Matches rippled's
    /// `setMaxDisallowedLedger` in Application::setup().
    max_disallowed_ledger: Arc<std::sync::atomic::AtomicU32>,
}

impl std::fmt::Debug for ApplicationRoot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ApplicationRoot")
            .field("basic_app", &self.basic_app)
            .field("job_queue", &self.job_queue)
            .field("collector_manager", &self.collector_manager)
            .field("load_manager", &self.load_manager)
            .field("local_load_fee", &self.load_fee_track.local_fee())
            .field("node_store_scheduler", &self.node_store_scheduler)
            .field("time_keeper", &"TimeKeeper")
            .field("stop_tree", &self.stop_tree)
            .field("has_node_family", &self.node_family.is_some())
            .field("has_resolver_runtime", &self.resolver_runtime.is_some())
            .field("has_overlay_runtime", &self.overlay_runtime.is_some())
            .field("has_overlay_status", &self.overlay_status.is_some())
            .field("has_server_ports_setup", &self.server_ports_setup.is_some())
            .field(
                "has_published_server_ports",
                &self.published_server_ports.is_some(),
            )
            .field("has_status_metrics", &self.status_metrics().is_some())
            .field("wallet_db_path", &self.registry.config.wallet_db_path)
            .field("path_search_old", &self.registry.config.path_search_old)
            .field("path_search", &self.registry.config.path_search)
            .field("path_search_fast", &self.registry.config.path_search_fast)
            .field("path_search_max", &self.registry.config.path_search_max)
            .field(
                "peer_reservation_count",
                &self.registry.peer_reservations.list().len(),
            )
            .field("has_perf_log", &self.registry.perf_log.is_some())
            .field(
                "network_ops_operating_mode",
                &self.network_ops_operating_mode(),
            )
            .field(
                "has_network_ops_runtime",
                &self.network_ops_runtime.is_some(),
            )
            .field(
                "has_network_ops_validation_runtime",
                &self.network_ops_validation_runtime.is_some(),
            )
            .field(
                "network_ops_pending_transactions",
                &self.network_ops_pending_transaction_count().unwrap_or(0),
            )
            .field(
                "network_ops_pending_validations",
                &self.network_ops_pending_validation_count().unwrap_or(0),
            )
            .field(
                "transaction_cache_size",
                &self.transaction_master.get_cache().size(),
            )
            .field("validated_ledger_seq", &self.validated_ledger_seq())
            .field("published_ledger_seq", &self.published_ledger_seq())
            .field(
                "has_ledger_master_runtime",
                &self.ledger_master_runtime.is_some(),
            )
            .field("has_consensus_runtime", &self.consensus_runtime.is_some())
            .field("local_tx_count", &self.local_tx_count().unwrap_or(0))
            .field("validations", &self.validations)
            .field("validator_quorum", &self.validators.quorum())
            .field("validator_list_count", &self.validators.count())
            .field(
                "status_rpc_current_ledger_index",
                &self.status_rpc_current_ledger_index(),
            )
            .field(
                "has_status_rpc_queue_report",
                &self.status_rpc_queue_report().is_some(),
            )
            .field("status_rpc_peer_count", &self.status_rpc_peer_count())
            .field("status_rpc_network_id", &self.status_rpc_network_id())
            .field(
                "has_status_rpc_last_close",
                &self.status_rpc_last_close().is_some(),
            )
            .field("status_rpc_hostid", &self.status_rpc_hostid())
            .field("status_rpc_server_domain", &self.status_rpc_server_domain())
            .field("status_rpc_node_size", &self.status_rpc_node_size())
            .field("status_rpc_io_latency_ms", &self.status_rpc_io_latency_ms())
            .field(
                "has_status_rpc_git_info",
                &self.status_rpc_git_info().is_some(),
            )
            .field(
                "unsupported_majority_warned",
                &self.unsupported_majority_warned(),
            )
            .field(
                "has_unsupported_majority_warning_details",
                &self.unsupported_majority_warning_details().is_some(),
            )
            .field("elb_support", &self.elb_support)
            .field("has_node_identity", &self.node_identity.is_some())
            .field(
                "has_validation_public_key",
                &self.validation_public_key.is_some(),
            )
            .field("runtime_bindings", &self.runtime_bindings())
            .field(
                "has_shamap_store_service",
                &self.shamap_store_service.is_some(),
            )
            .field(
                "has_shared_tree_cache",
                &self.shared_tree_cache.get().is_some(),
            )
            .finish()
    }
}

/// Everything needed to sign a validation for a just-accepted ledger,
/// carried alongside `accept_ledger`'s other parameters so signing can
/// happen synchronously with the real ledger build inside the SAME
/// JobQueue job -- not in a separate step racing against
/// `ConsensusLedgerAcceptor::accept_ledger`'s async, fire-and-forget
/// wrapper (which enqueues the real build and returns immediately,
/// without waiting for it). Reading `closed_ledger()` right after that
/// wrapper returns can observe the PREVIOUS ledger (a stale read racing
/// the not-yet-run inner job), producing a validation whose `sfLedgerHash`
/// doesn't match its claimed `sfLedgerSequence` -- corrupting the trust
/// trie with an internally inconsistent `(seq, id)` pair and causing
/// `Validations::getPreferred` to return nonsense, which in turn makes
/// `Consensus::checkLedger` think the network is on a different ledger
/// and reset back to it via `handleWrongLedger`. This struct exists so the
/// real, synchronous ledger hash is available at the exact point signing
/// happens.
#[derive(Clone)]
pub struct PendingValidation {
    pub public_key: protocol::PublicKey,
    pub secret_key: protocol::SecretKey,
    pub node_id: protocol::NodeId,
    pub consensus_hash: Uint256,
    pub proposing: bool,
}

pub trait LedgerAcceptor: Send + Sync + 'static {
    /// `txns` is the exact transaction set consensus agreed on this round
    /// (the reference's `result.txns`, captured by `onClose` from the open
    /// ledger's contents at that earlier point in time and passed down
    /// through `doAccept` unchanged). This must NOT be re-derived by
    /// re-reading the open ledger's current contents at accept time: new
    /// local transactions may have arrived since `onClose` captured the
    /// consensus set.
    fn accept_ledger(
        &self,
        closed_seq: u32,
        close_time: u32,
        close_resolution: u8,
        correct_close_time: bool,
        _base_fee_drops: u64,
        txns: Vec<Arc<protocol::STTx>>,
        validation: Option<PendingValidation>,
    ) -> Result<u32, String>;

    /// Accept a ledger built by the consensus engine.
    fn consensus_built(&self, ledger: Arc<Ledger>) -> Result<(), String>;

    /// Publish a locally-signed validation for a just-accepted ledger:
    /// feed it into this node's own trust trie (matching the reference's
    /// `handleNewValidation(app_, v, "local")`) and broadcast it to every
    /// connected peer (matching `app_.getOverlay().broadcast(TMValidation)`).
    /// Matches `RCLConsensus::Adaptor::validate`'s tail. Default is a no-op
    /// so callers without a full runtime (e.g. tests) still compile; the
    /// real implementation lives on `ConsensusLedgerAcceptor`, which has
    /// the `ApplicationRoot`/overlay access this needs.
    fn publish_validation(&self, _validation: Arc<protocol::STValidation>) {}

    /// The current closed ledger, used right after `accept_ledger`
    /// succeeds to learn the real built ledger's hash for the validation
    /// `publish_validation` sends. Default returns `None` for callers
    /// without a full runtime.
    fn closed_ledger(&self) -> Option<Arc<Ledger>> {
        None
    }

    /// Dispatch the heavy consensus-accept work (do_accept + end_consensus)
    /// to run off the consensus timer thread, matching rippled's
    /// `app_.getJobQueue().addJob(JtAccept, "AcceptLedger", ...)` in
    /// RCLConsensus::Adaptor::onAccept. Default runs synchronously so
    /// callers without a JobQueue (e.g. tests) still work correctly.
    fn spawn_consensus_accept_job(&self, job: Box<dyn FnOnce() + Send + 'static>) {
        job();
    }

    /// Return the owner-tracked closed ledger for consensus handoff.
    fn consensus_closed_ledger(&self) -> Option<Arc<Ledger>> {
        None
    }

    /// Return the owner-selected previous ledger for the next round.
    fn consensus_previous_ledger(&self) -> Option<Arc<Ledger>> {
        None
    }

    /// Get a node fetcher closure for backed state map reads from NuDB.
    fn node_fetcher(
        &self,
    ) -> Option<
        Arc<
            dyn Fn(
                    basics::sha_map_hash::SHAMapHash,
                ) -> Option<
                    basics::memory::intrusive_pointer::SharedIntrusive<
                        shamap::nodes::tree_node::SHAMapTreeNode,
                    >,
                > + Send
                + Sync,
        >,
    > {
        None
    }
}

impl LedgerAcceptor for ApplicationRoot {
    fn accept_ledger(
        &self,
        closed_seq: u32,
        close_time: u32,
        close_resolution: u8,
        correct_close_time: bool,
        base_fee_drops: u64,
        txns: Vec<Arc<protocol::STTx>>,
        _validation: Option<PendingValidation>,
    ) -> Result<u32, String> {
        self.accept_ledger_with_txns(
            closed_seq,
            close_time,
            close_resolution,
            correct_close_time,
            base_fee_drops,
            txns,
        )
    }

    fn consensus_built(&self, ledger: Arc<ledger::Ledger>) -> Result<(), String> {
        tracing::info!(target: "consensus",
            "[consensus] consensus_built seq={} hash={:02x}{:02x}{:02x}{:02x}",
            ledger.header().seq,
            ledger.header().hash.as_uint256().data()[0],
            ledger.header().hash.as_uint256().data()[1],
            ledger.header().hash.as_uint256().data()[2],
            ledger.header().hash.as_uint256().data()[3],
        );
        self.on_consensus_built_ledger(ledger);
        Ok(())
    }

    fn consensus_closed_ledger(&self) -> Option<Arc<Ledger>> {
        self.closed_ledger().or_else(|| self.validated_ledger())
    }

    fn consensus_previous_ledger(&self) -> Option<Arc<Ledger>> {
        let parent_hash = self.open_ledger().current().parent_hash;
        if parent_hash.is_zero() {
            return self.consensus_closed_ledger();
        }

        if let Some(closed) = self.consensus_closed_ledger()
            && *closed.header().hash.as_uint256() == parent_hash
        {
            return Some(closed);
        }

        self.ledger_master_runtime()
            .and_then(|runtime| {
                runtime
                    .ledger_master()
                    .get_ledger_by_hash(SHAMapHash::new(parent_hash))
            })
            .or_else(|| {
                self.validated_ledger()
                    .filter(|ledger| *ledger.header().hash.as_uint256() == parent_hash)
            })
    }

    fn node_fetcher(
        &self,
    ) -> Option<
        Arc<
            dyn Fn(
                    basics::sha_map_hash::SHAMapHash,
                ) -> Option<
                    basics::memory::intrusive_pointer::SharedIntrusive<
                        shamap::nodes::tree_node::SHAMapTreeNode,
                    >,
                > + Send
                + Sync,
        >,
    > {
        let ns = self.node_store().as_ref()?.clone();
        Some(Arc::new(move |hash| {
            let data = match &ns {
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Single(db) => db
                    .fetch_node_object(
                        hash.as_uint256(),
                        0,
                        nodestore::FetchType::Synchronous,
                        false,
                    ),
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Rotating(db) => db
                    .fetch_node_object(
                        hash.as_uint256(),
                        0,
                        nodestore::FetchType::Synchronous,
                        false,
                    ),
            }?;
            shamap::nodes::tree_node::SHAMapTreeNode::make_from_prefix(data.data(), hash).ok()
        }))
    }
}

#[allow(dead_code)]
pub struct ConsensusLedgerAcceptor {
    root: ApplicationRoot,
    job_queue: Arc<JobQueue>,
    basic_app: Arc<BasicApp>,
    /// Shared node store reference. Set via OnceLock after node store is attached.
    shared_node_store:
        Arc<std::sync::RwLock<Option<crate::shamap::shamap_store_backend::SHAMapStoreNodeStore>>>,
}

#[derive(Clone)]
#[cfg_attr(not(test), allow(dead_code))] // dormant legacy accept machinery; exercised by state tests
struct AcceptLedgerPendingTransaction {
    transaction: SharedTransaction,
}

impl HasTxnType for AcceptLedgerPendingTransaction {
    fn txn_type(&self) -> TxType {
        self.transaction
            .lock()
            .expect("transaction mutex must not be poisoned")
            .get_s_transaction()
            .get_txn_type()
    }
}

#[cfg_attr(not(test), allow(dead_code))] // dormant legacy accept machinery; exercised by state tests
struct AcceptLedgerPendingRuntime;

/// Concrete ledger-state adapters for the shared Batch signer authorization
/// helpers. Keeping the authorization algorithm in `tx` makes Batch follow
/// the same regular-key, disabled-master, and signer-list rules as ordinary
/// transactions.
#[derive(Clone)]
struct BatchPreclaimAccountState {
    regular_key: Option<AccountID>,
    master_disabled: bool,
}

impl tx::TransactorSingleSignAccountState<AccountID> for BatchPreclaimAccountState {
    fn regular_key(&self) -> Option<&AccountID> {
        self.regular_key.as_ref()
    }

    fn is_master_disabled(&self) -> bool {
        self.master_disabled
    }
}

#[derive(Clone)]
struct BatchPreclaimAccountSigner {
    account: AccountID,
    weight: u32,
}

impl tx::TransactorMultiSignAccountSigner<AccountID> for BatchPreclaimAccountSigner {
    fn account_id(&self) -> &AccountID {
        &self.account
    }

    fn weight(&self) -> u32 {
        self.weight
    }
}

#[derive(Clone)]
struct BatchPreclaimSignerList {
    signer_list_id_present: bool,
    signer_list_id: u32,
    quorum: u32,
    entries: Vec<BatchPreclaimAccountSigner>,
}

impl tx::TransactorMultiSignSignerList<BatchPreclaimAccountSigner> for BatchPreclaimSignerList {
    type Entries = Vec<BatchPreclaimAccountSigner>;

    fn signer_list_id_present(&self) -> bool {
        self.signer_list_id_present
    }

    fn signer_list_id(&self) -> u32 {
        self.signer_list_id
    }

    fn signer_quorum(&self) -> u32 {
        self.quorum
    }

    fn signer_entries(self) -> Result<Self::Entries, NotTec> {
        Ok(self.entries)
    }
}

#[derive(Clone)]
struct BatchPreclaimTxSigner {
    object: STObject,
}

impl tx::TransactorMultiSignTxSigner<AccountID> for BatchPreclaimTxSigner {
    fn account_id(&self) -> AccountID {
        self.object.get_account_id(get_field_by_symbol("sfAccount"))
    }

    fn signing_pub_key_is_empty(&self) -> bool {
        self.object
            .get_field_vl(get_field_by_symbol("sfSigningPubKey"))
            .is_empty()
    }
}

#[derive(Clone)]
struct BatchPreclaimSigner {
    object: STObject,
}

impl tx::TransactorBatchSigner for BatchPreclaimSigner {
    type AccountId = AccountID;

    fn account_id(&self) -> Self::AccountId {
        self.object.get_account_id(get_field_by_symbol("sfAccount"))
    }

    fn signing_pub_key_is_empty(&self) -> bool {
        self.object
            .get_field_vl(get_field_by_symbol("sfSigningPubKey"))
            .is_empty()
    }
}

impl tx::TransactorBatchMultiSigner<AccountID> for BatchPreclaimSigner {
    type TxSigner = BatchPreclaimTxSigner;
    type TxSigners = Vec<BatchPreclaimTxSigner>;

    fn tx_signers(&self) -> Self::TxSigners {
        self.object
            .get_field_array(get_field_by_symbol("sfSigners"))
            .iter()
            .cloned()
            .map(|object| BatchPreclaimTxSigner { object })
            .collect()
    }
}

struct BatchPreclaimTx<'a> {
    tx: &'a STTx,
}

impl tx::TransactorBatchSignTx for BatchPreclaimTx<'_> {
    type AccountId = AccountID;
    type Signer = BatchPreclaimSigner;
    type Signers = Vec<BatchPreclaimSigner>;

    fn batch_signers(&self) -> Self::Signers {
        self.tx
            .get_field_array(get_field_by_symbol("sfBatchSigners"))
            .iter()
            .cloned()
            .map(|object| BatchPreclaimSigner { object })
            .collect()
    }
}

#[derive(Clone, Copy)]
struct BatchFeeInnerTransaction<'a>(&'a STTx);

impl tx::BatchBaseFeeInnerTransaction for BatchFeeInnerTransaction<'_> {
    fn txn_type(&self) -> TxType {
        self.0.get_txn_type()
    }
}

#[derive(Clone)]
struct BatchFeeSignerEntry(STObject);

impl tx::BatchBaseFeeSignerEntry for BatchFeeSignerEntry {
    fn has_txn_signature(&self) -> bool {
        self.0
            .is_field_present(get_field_by_symbol("sfTxnSignature"))
    }

    fn multisigner_count(&self) -> usize {
        self.0
            .get_field_array(get_field_by_symbol("sfSigners"))
            .len()
    }
}

const INVALID_BATCH_BASE_FEE: u64 = u64::MAX;

fn batch_base_fee(view: &impl ReadView, tx: &STTx) -> Result<u64, Ter> {
    let raw_transactions_field = get_field_by_symbol("sfRawTransactions");
    if !tx.is_field_present(raw_transactions_field) {
        return Ok(INVALID_BATCH_BASE_FEE);
    }
    let inner_transactions = match tx::canonical_batch_inner_transactions(tx) {
        Ok(inner_transactions) => inner_transactions,
        Err(_) => return Ok(INVALID_BATCH_BASE_FEE),
    };
    let batch_signers_field = get_field_by_symbol("sfBatchSigners");
    let batch_signers = tx.is_field_present(batch_signers_field).then(|| {
        tx.get_field_array(batch_signers_field)
            .iter()
            .cloned()
            .map(BatchFeeSignerEntry)
            .collect::<Vec<_>>()
    });
    let ledger_base_fee = view.fees().base;
    // Batch::calculateBaseFeeImpl starts from
    // Transactor::calculateBaseFee, including both the outer transaction's
    // multisigners and any SponsorSignature multisigners.
    let transactor_base_fee = calculate_default_sttx_base_fee(view, tx);

    let fee_error = std::cell::Cell::new(None);
    let fee = tx::run_batch_calculate_base_fee(
        INVALID_BATCH_BASE_FEE,
        transactor_base_fee,
        ledger_base_fee,
        Some(
            inner_transactions
                .iter()
                .map(BatchFeeInnerTransaction)
                .collect::<Vec<_>>(),
        ),
        batch_signers,
        |inner| match calculate_sttx_base_fee(view, inner.0) {
            Ok(fee) => fee,
            Err(ter) => {
                fee_error.set(Some(ter));
                INVALID_BATCH_BASE_FEE
            }
        },
        u64::checked_add,
        |fee, count| fee.checked_mul(u64::try_from(count).ok()?),
    );
    fee_error.get().map_or(Ok(fee), Err)
}

/// `../rippled/src/libxrpl/tx/transactors/system/Batch.cpp::Batch::checkSign`
/// runs the ordinary outer-transaction signer check before this BatchSigners
/// tail. Keep this separate from the fee-specific preclaim tail so callers
/// can preserve `applySteps.cpp::invokePreclaim`'s pre-sign-before-fee order.
pub(crate) fn batch_check_sign_ter(view: &impl ReadView, tx: &STTx, flags: ApplyFlags) -> Ter {
    let batch_signers_field = get_field_by_symbol("sfBatchSigners");
    if !tx.is_field_present(batch_signers_field) {
        return Ter::TES_SUCCESS;
    }

    let read_failed = std::cell::Cell::new(false);
    let result = tx::run_transactor_preclaim_check_batch_sign(
        flags,
        &BatchPreclaimTx { tx },
        |account| match view.read(account_keylet(
            Uint160::from_slice(account.data()).expect("account width should match Uint160"),
        )) {
            Ok(account_root) => account_root.map(|account_root| {
                let regular_key_field = get_field_by_symbol("sfRegularKey");
                BatchPreclaimAccountState {
                    regular_key: account_root
                        .is_field_present(regular_key_field)
                        .then(|| account_root.get_account_id(regular_key_field)),
                    master_disabled: account_root.get_field_u32(get_field_by_symbol("sfFlags"))
                        & lsfDisableMaster
                        != 0,
                }
            }),
            Err(_) => {
                read_failed.set(true);
                None
            }
        },
        |account| {
            match view.read(protocol::signers_keylet(
                Uint160::from_slice(account.data()).expect("account width should match Uint160"),
            )) {
                Ok(signer_list) => signer_list,
                Err(_) => {
                    read_failed.set(true);
                    None
                }
            }
            .map(|signer_list| BatchPreclaimSignerList {
                signer_list_id_present: signer_list
                    .is_field_present(get_field_by_symbol("sfSignerListID")),
                signer_list_id: signer_list.get_field_u32(get_field_by_symbol("sfSignerListID")),
                quorum: signer_list.get_field_u32(get_field_by_symbol("sfSignerQuorum")),
                entries: signer_list
                    .get_field_array(get_field_by_symbol("sfSignerEntries"))
                    .iter()
                    .map(|entry| BatchPreclaimAccountSigner {
                        account: entry.get_account_id(get_field_by_symbol("sfAccount")),
                        weight: u32::from(
                            entry.get_field_u16(get_field_by_symbol("sfSignerWeight")),
                        ),
                    })
                    .collect(),
            })
        },
        |signer| {
            PublicKey::from_slice(
                &signer
                    .object
                    .get_field_vl(get_field_by_symbol("sfSigningPubKey")),
            )
            .is_ok()
        },
        |signer| {
            let key = PublicKey::from_slice(
                &signer
                    .object
                    .get_field_vl(get_field_by_symbol("sfSigningPubKey")),
            )
            .expect("public-key type was checked before deriving its account");
            calc_account_id(key.as_bytes())
        },
        |signer| {
            PublicKey::from_slice(
                &signer
                    .object
                    .get_field_vl(get_field_by_symbol("sfSigningPubKey")),
            )
            .is_ok()
        },
        |signer| {
            let key = PublicKey::from_slice(
                &signer
                    .object
                    .get_field_vl(get_field_by_symbol("sfSigningPubKey")),
            )
            .expect("public-key type was checked before deriving its account");
            calc_account_id(key.as_bytes())
        },
    );
    if read_failed.get() {
        Ter::TEF_BAD_LEDGER
    } else {
        result
    }
}

fn batch_preclaim_ter(view: &impl ReadView, tx: &STTx, _flags: ApplyFlags) -> Ter {
    if tx.get_txn_type() != TxType::BATCH {
        return Ter::TES_SUCCESS;
    }

    // `Batch::calculateBaseFee` returns a payable placeholder on failure, but
    // Batch's typed preclaim rejects that same invalid calculation after the
    // shared signature and fee gates have run.
    match batch_base_fee(view, tx) {
        Err(ter) => ter,
        Ok(INVALID_BATCH_BASE_FEE) => Ter::TEC_INSUFF_FEE,
        Ok(_) => Ter::TES_SUCCESS,
    }
}

#[derive(Debug)]
struct PersistentSubmitSandbox {
    holder: Arc<std::sync::Mutex<Option<Sandbox<ledger::OpenView<Ledger>>>>>,
    sandbox: Option<Sandbox<ledger::OpenView<Ledger>>>,
}

impl PersistentSubmitSandbox {
    fn take_or_new(
        holder: Arc<std::sync::Mutex<Option<Sandbox<ledger::OpenView<Ledger>>>>>,
        base: Arc<Ledger>,
    ) -> Self {
        let base_header = base.header();
        let sandbox = holder
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .take()
            // Reuse only the OpenView built over this exact LCL. In
            // particular, preclaim expiration compares parent_close_time, so
            // retaining an OpenView after the parent advances can evaluate a
            // transaction against an obsolete (including zero) close time.
            .filter(|sandbox| {
                let header = sandbox.header();
                header.parent_hash == base_header.hash
                    && header.parent_close_time == base_header.close_time
            })
            // TxQ::apply receives rippled's OpenView. A Sandbox<Ledger>
            // delegates `open()` to the closed parent and therefore skips
            // Transactor::checkFee's open-ledger minimum-fee rejection.
            .unwrap_or_else(|| {
                let rules = base.rules().clone();
                Sandbox::new(
                    Arc::new(ledger::OpenView::new_open(base, rules)),
                    ApplyFlags::NONE,
                )
            });
        Self {
            holder,
            sandbox: Some(sandbox),
        }
    }

    fn view_mut(&mut self) -> &mut Sandbox<ledger::OpenView<Ledger>> {
        self.sandbox
            .as_mut()
            .expect("persistent submit sandbox must be present while applying")
    }
}

impl Drop for PersistentSubmitSandbox {
    fn drop(&mut self) {
        let Some(sandbox) = self.sandbox.take() else {
            return;
        };
        let mut holder = self
            .holder
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        *holder = Some(sandbox);
        drop(holder);
        self.holder.clear_poison();
    }
}

#[cfg(test)]
mod persistent_submit_sandbox_tests {
    use super::PersistentSubmitSandbox;
    use ledger::{Ledger, OpenView, ReadView, Sandbox};
    use std::sync::{Arc, Mutex};

    #[test]
    fn rebases_parent_close_time_when_submit_lcl_advances() {
        let holder: Arc<Mutex<Option<Sandbox<OpenView<Ledger>>>>> = Arc::new(Mutex::new(None));
        let initial = Arc::new(Ledger::from_ledger_seq_and_close_time(1, 0, false));
        {
            let mut sandbox =
                PersistentSubmitSandbox::take_or_new(Arc::clone(&holder), Arc::clone(&initial));
            assert_eq!(sandbox.view_mut().header().parent_close_time, 0);
        }

        let lcl = Arc::new(Ledger::from_ledger_seq_and_close_time(2, 1_000, false));
        let mut sandbox = PersistentSubmitSandbox::take_or_new(holder, Arc::clone(&lcl));
        let header = sandbox.view_mut().header();
        assert_eq!(header.parent_hash, lcl.header().hash);
        assert_eq!(header.parent_close_time, lcl.header().close_time);
    }
}

#[derive(Debug, Clone)]
struct SubmitConsumedTicket {
    sle: Arc<STLedgerEntry>,
    owner_page: u64,
}

#[derive(Clone, Copy)]
struct AppClosedLedgerTxQView<'a> {
    ledger: &'a Ledger,
}

impl QueueTxQClosedLedgerView for AppClosedLedgerTxQView<'_> {
    fn ledger_seq(&self) -> u32 {
        self.ledger.header().seq
    }
}

#[derive(Clone, Copy)]
struct AppOpenLedgerTxQAcceptView {
    open_ledger_tx_count: usize,
    parent_hash: Uint256,
}

impl QueueAcceptLedgerViewSource for AppOpenLedgerTxQAcceptView {
    fn open_ledger_tx_count(&self) -> usize {
        self.open_ledger_tx_count
    }

    fn parent_hash(&self) -> Uint256 {
        self.parent_hash
    }
}

struct AppOpenLedgerTxQAcceptRuntime<'a, V> {
    root: &'a ApplicationRoot,
    view: &'a mut AppOpenLedgerView,
    rebase_view: &'a mut V,
    applied_ids: &'a mut std::collections::HashSet<Uint256>,
    #[cfg_attr(not(test), allow(dead_code))] // reserved for accept-pass flag handling in M7
    flags: ApplyFlags,
}

impl<V>
    QueueAcceptLiveApplyRuntime<
        AppTxQAccount,
        AppTxQTransaction,
        AppTxQJournalTag,
        AppTxQParentBatchId,
    > for AppOpenLedgerTxQAcceptRuntime<'_, V>
where
    V: ledger::ApplyView,
{
    fn apply_queued(
        &mut self,
        queued: &mut tx::MaybeTx<
            AppTxQTransaction,
            AppTxQAccount,
            AppTxQJournalTag,
            AppTxQParentBatchId,
        >,
    ) -> ApplyResult {
        self.root.reapply_open_ledger_record(
            self.view,
            self.rebase_view,
            self.applied_ids,
            &AppOpenLedgerTxRecord::new(Arc::clone(&queued.pf_result.tx)),
            // `TxQ::MaybeTx::apply` reuses its stored flags and re-preflights
            // if they differ from the retained preflight result. Do not
            // substitute the enclosing accept pass's flags here.
            queued.flags,
        )
    }
}

struct AppOpenLedgerTxQApplyRuntime<'a, V> {
    view: &'a mut AppOpenLedgerView,
    submit_view: &'a mut V,
    tx: Arc<STTx>,
    account_seqs: Arc<std::sync::Mutex<std::collections::HashMap<protocol::AccountID, u32>>>,
    preflight_result:
        PreflightResult<AppTxQTransaction, TxConsequences, AppTxQJournalTag, AppTxQParentBatchId>,
    preclaim_result: PreclaimResult<AppTxQTransaction, AppTxQJournalTag, AppTxQParentBatchId>,
    current_ledger_seq: u32,
    load_fee_track: &'a SharedLoadFeeTrack,
    clear_ahead_queue: Vec<TxDetails<AppTxQTransaction, AppTxQAccount>>,
    clear_ahead_metrics: tx::QueueFeeMetricsSnapshot,
    clear_ahead_attempts: Vec<(SeqProxy, ApplyResult)>,
    clear_ahead_removed: Vec<SeqProxy>,
    multi_txn_adjustment: Option<tx::QueueApplyViewAdjustment>,
    delivered_amount: Option<STAmount>,
    node_network_id: u32,
}

impl<'a, V> AppOpenLedgerTxQApplyRuntime<'a, V>
where
    V: ledger::ApplyView,
{
    #[cfg_attr(not(test), allow(dead_code))] // TxQ apply runtime built by state tests
    fn new(
        view: &'a mut AppOpenLedgerView,
        submit_view: &'a mut V,
        tx: Arc<STTx>,
        flags: ApplyFlags,
        current_ledger_seq: u32,
        load_fee_track: &'a SharedLoadFeeTrack,
        account_seqs: Arc<std::sync::Mutex<std::collections::HashMap<protocol::AccountID, u32>>>,
    ) -> Self {
        Self::new_with_clear_ahead(
            view,
            submit_view,
            tx,
            flags,
            current_ledger_seq,
            load_fee_track,
            account_seqs,
            0,
            Vec::new(),
            tx::QueueFeeMetricsSnapshot {
                txns_expected: 0,
                escalation_multiplier: tx::TXQ_BASE_LEVEL,
            },
        )
    }

    fn new_with_clear_ahead(
        view: &'a mut AppOpenLedgerView,
        submit_view: &'a mut V,
        tx: Arc<STTx>,
        flags: ApplyFlags,
        current_ledger_seq: u32,
        load_fee_track: &'a SharedLoadFeeTrack,
        account_seqs: Arc<std::sync::Mutex<std::collections::HashMap<protocol::AccountID, u32>>>,
        node_network_id: u32,
        clear_ahead_queue: Vec<TxDetails<AppTxQTransaction, AppTxQAccount>>,
        clear_ahead_metrics: tx::QueueFeeMetricsSnapshot,
    ) -> Self {
        let rules = submit_view.rules().clone();
        let result = transaction_preflight_ter_with_flags_and_network_id(
            &tx,
            &rules,
            flags,
            node_network_id,
        );
        let preclaim_ter = if is_tes_success(result) {
            queue_apply_preclaim_ter_with_load_fee(
                submit_view,
                tx.as_ref(),
                current_ledger_seq,
                flags,
                load_fee_track,
            )
        } else {
            result
        };
        let consequences = if is_tes_success(result) {
            // TxQ admission must use the transaction type's canonical
            // consequences factory. A generic fee/sequence consequence loses
            // blockers, custom potential spend, and ticket identity.
            canonical_sttx_consequences(tx.as_ref())
        } else {
            TxConsequences::from_preflight_result(result)
        };
        let journal = "app_txq_submit".to_owned();
        let preflight_result = PreflightResult::new(
            Arc::clone(&tx),
            None,
            rules,
            consequences,
            flags,
            journal.clone(),
            result,
        );
        let preclaim_result = PreclaimResult::new(
            current_ledger_seq,
            Arc::clone(&tx),
            None,
            flags,
            journal,
            preclaim_ter,
        );

        Self {
            view,
            submit_view,
            tx,
            account_seqs,
            preflight_result,
            preclaim_result,
            current_ledger_seq,
            load_fee_track,
            clear_ahead_queue,
            clear_ahead_metrics,
            clear_ahead_attempts: Vec::new(),
            clear_ahead_removed: Vec::new(),
            multi_txn_adjustment: None,
            delivered_amount: None,
            node_network_id,
        }
    }

    fn take_clear_ahead_effects(&mut self) -> (Vec<(SeqProxy, ApplyResult)>, Vec<SeqProxy>) {
        (
            std::mem::take(&mut self.clear_ahead_attempts),
            std::mem::take(&mut self.clear_ahead_removed),
        )
    }

    fn clear_ahead_required_fee_level(&self, series_size: usize) -> Option<u64> {
        // TxQ.cpp::FeeMetrics::escalatedSeriesFeeLevel (240-273):
        // multiplier / target² * Σ(current..last)n².
        let current = self.view.tx_ids().len() as u128;
        let target = self.clear_ahead_metrics.txns_expected as u128;
        if current <= target || target == 0 || series_size == 0 {
            return None;
        }
        let last = current.checked_add((series_size - 1) as u128)?;
        let sum_squares = |n: u128| {
            n.checked_mul(n)?
                .checked_mul(n.checked_mul(2)?.checked_add(1)?)?
                .checked_div(6)
        };
        let series = sum_squares(last)?.checked_sub(sum_squares(current - 1)?)?;
        let total = (self.clear_ahead_metrics.escalation_multiplier as u128)
            .checked_mul(series)?
            .checked_div(target.checked_mul(target)?)?;
        u64::try_from(total).ok()
    }

    fn clear_ahead_apply<W: ledger::ApplyView>(
        current_ledger_seq: u32,
        load_fee_track: &SharedLoadFeeTrack,
        view: &mut W,
        tx: &Arc<STTx>,
        flags: ApplyFlags,
        node_network_id: u32,
    ) -> (
        ApplyResult,
        Option<STAmount>,
        Vec<AppliedBatchInnerTransaction>,
    ) {
        let preflight = transaction_preflight_ter_with_flags_and_network_id(
            tx,
            &view.rules(),
            flags,
            node_network_id,
        );
        let preclaim = if is_tes_success(preflight) {
            queue_apply_preclaim_ter_with_load_fee(
                view,
                tx.as_ref(),
                current_ledger_seq,
                flags,
                load_fee_track,
            )
        } else {
            preflight
        };
        if !is_tes_success(preclaim) && !is_tec_claim(preclaim) {
            return (ApplyResult::new(preclaim, false, false), None, Vec::new());
        }
        let outcome =
            apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim_and_network_id(
                view,
                tx.as_ref(),
                tx.get_txn_type(),
                flags,
                preclaim,
                node_network_id,
            );
        let applied_batch_inner_transactions = outcome.applied_batch_inner_transactions;
        (
            ApplyResult::new(outcome.result, outcome.applied, false),
            outcome.delivered_amount,
            applied_batch_inner_transactions,
        )
    }

    fn record_clear_ahead_open_ledger_tx(&self, tx: &Arc<STTx>) {
        let account = tx.get_account_id(get_field_by_symbol("sfAccount"));
        let next = tx.get_seq_proxy().value().saturating_add(1);
        if let Ok(mut seqs) = self.account_seqs.lock() {
            let entry = seqs.entry(account).or_insert(next);
            *entry = (*entry).max(next);
        }
    }
}

impl<V> QueueApplyExecutionRuntime<AppTxQTransaction, AppTxQJournalTag, AppTxQParentBatchId>
    for AppOpenLedgerTxQApplyRuntime<'_, V>
where
    V: ledger::ApplyView,
{
    fn run_preflight(
        &mut self,
    ) -> PreflightResult<AppTxQTransaction, TxConsequences, AppTxQJournalTag, AppTxQParentBatchId>
    {
        self.preflight_result.clone()
    }

    fn trace(&mut self, _message: &str) {}

    fn direct_apply(&mut self) -> ApplyResult {
        let txn_type = self.tx.get_txn_type();
        let preclaim = self.preclaim_result.ter;
        // A claimable preclaim `tec` enters Transactor for the generic
        // fee/sequence lifecycle, but Transactor::operator() never invokes
        // the type-specific doApply unless preclaimResult is tesSUCCESS.
        let outcome = if is_tes_success(preclaim) || is_tec_claim(preclaim) {
            apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim_and_network_id(
                self.submit_view,
                self.tx.as_ref(),
                txn_type,
                self.preflight_result.flags,
                preclaim,
                self.node_network_id,
            )
        } else {
            SubmitApplyOutcome {
                result: preclaim,
                applied: false,
                delivered_amount: None,
                prebuilt_outer_metadata: None,
                applied_batch_inner_transactions: Vec::new(),
            }
        };
        self.delivered_amount = outcome.delivered_amount;
        if outcome.applied {
            record_applied_open_transactions(
                self.view,
                Arc::clone(&self.tx),
                &outcome.applied_batch_inner_transactions,
            );
            tracing::debug!(
                target: "rpc",
                ter = ?outcome.result,
                "direct_apply: pushed transaction into open ledger view"
            );
            // Track the account's next expected sequence
            let account = self.tx.get_account_id(get_field_by_symbol("sfAccount"));
            let tx_seq = self.tx.get_seq_proxy().value();
            if let Ok(mut seqs) = self.account_seqs.lock() {
                let next = tx_seq.saturating_add(1);
                let entry = seqs.entry(account).or_insert(next);
                if next > *entry {
                    *entry = next;
                }
            }
        }

        ApplyResult::new(outcome.result, outcome.applied, false)
    }

    fn prepare_multitxn(&mut self, adjustment: tx::QueueApplyViewAdjustment) -> bool {
        // Parity: ../rippled/src/xrpld/app/misc/detail/TxQ.cpp::TxQ::apply
        // materializes a temporary ApplyViewImpl/OpenView, reduces its
        // account balance by queued commitments, and adjusts its sequence
        // before running preclaim. Keep this child uncommitted: it is an
        // admission-only view, never a mutation of the live submit sandbox.
        self.multi_txn_adjustment = Some(adjustment);
        true
    }

    fn run_preclaim(
        &mut self,
        view_source: tx::QueueApplyPreclaimViewSource,
    ) -> PreclaimResult<AppTxQTransaction, AppTxQJournalTag, AppTxQParentBatchId> {
        if view_source == tx::QueueApplyPreclaimViewSource::CurrentView {
            return self.preclaim_result.clone();
        }

        let Some(adjustment) = self.multi_txn_adjustment else {
            return PreclaimResult::new(
                self.current_ledger_seq,
                Arc::clone(&self.tx),
                None,
                self.preflight_result.flags,
                self.preflight_result.journal.clone(),
                Ter::TEF_INTERNAL,
            );
        };

        let account = self.tx.get_account_id(get_field_by_symbol("sfAccount"));
        let account_key = account_keylet(Uint160::from_void(account.data()));
        let mut multi_txn = ledger::FlowSandbox::new(&mut *self.submit_view);
        let account_root = match multi_txn.peek(account_key) {
            Ok(Some(account_root)) => account_root,
            Ok(None) => {
                return PreclaimResult::new(
                    self.current_ledger_seq,
                    Arc::clone(&self.tx),
                    None,
                    self.preflight_result.flags,
                    self.preflight_result.journal.clone(),
                    Ter::TEF_INTERNAL,
                );
            }
            Err(_) => {
                return PreclaimResult::new(
                    self.current_ledger_seq,
                    Arc::clone(&self.tx),
                    None,
                    self.preflight_result.flags,
                    self.preflight_result.journal.clone(),
                    Ter::TEF_BAD_LEDGER,
                );
            }
        };
        let mut adjusted =
            STLedgerEntry::from_stobject(account_root.clone_as_object(), *account_root.key());
        adjusted.set_field_amount(
            get_field_by_symbol("sfBalance"),
            STAmount::from_xrp_amount(XRPAmount::from_drops(adjustment.adjusted_balance_drops)),
        );
        adjusted.set_field_u32(
            get_field_by_symbol("sfSequence"),
            adjustment.applied_sequence_value,
        );
        if multi_txn.update(Arc::new(adjusted)).is_err() {
            return PreclaimResult::new(
                self.current_ledger_seq,
                Arc::clone(&self.tx),
                None,
                self.preflight_result.flags,
                self.preflight_result.journal.clone(),
                Ter::TEF_INTERNAL,
            );
        }

        PreclaimResult::new(
            self.current_ledger_seq,
            Arc::clone(&self.tx),
            None,
            self.preflight_result.flags,
            self.preflight_result.journal.clone(),
            queue_apply_preclaim_ter_with_load_fee(
                &multi_txn,
                self.tx.as_ref(),
                self.current_ledger_seq,
                self.preflight_result.flags,
                self.load_fee_track,
            ),
        )
    }

    fn run_try_clear(&mut self) -> ApplyResult {
        // rippled TxQ.cpp:517-609 applies all queued predecessors into an OpenView
        // sandbox, then repreclaims the current transaction against that
        // changed view. Do not mutate the persistent submit view or queue
        // until both phases have succeeded.
        let target = self.tx.get_seq_proxy();
        let predecessors = self
            .clear_ahead_queue
            .iter()
            .filter(|queued| queued.seq_proxy < target)
            .cloned()
            .collect::<Vec<_>>();
        if predecessors.is_empty() {
            return ApplyResult::new(Ter::TER_QUEUED, false, false);
        }

        let fee_field = get_field_by_symbol("sfFee");
        let fee_paid_drops = self.tx.get_field_amount(fee_field).xrp().drops();
        let calculated_base_fee = match calculate_sttx_base_fee(self.submit_view, self.tx.as_ref())
        {
            Ok(fee) => fee,
            Err(ter) => return ApplyResult::new(ter, false, false),
        };
        let fee_level_paid = evaluate_fee_level_paid(QueueFeeLevelPaidInputs {
            calculated_base_fee_drops: fee_drops_as_i64(calculated_base_fee),
            fee_paid_drops,
            default_base_fee_drops: fee_drops_as_i64(calculate_default_sttx_base_fee(
                self.submit_view,
                self.tx.as_ref(),
            )),
        });
        let Some(total_paid) = predecessors
            .iter()
            .try_fold(fee_level_paid, |total, queued| {
                total.checked_add(queued.fee_level)
            })
        else {
            return ApplyResult::new(Ter::TEL_INSUF_FEE_P, false, false);
        };
        let Some(required) = self.clear_ahead_required_fee_level(predecessors.len() + 1) else {
            return ApplyResult::new(Ter::TEL_INSUF_FEE_P, false, false);
        };
        if total_paid < required {
            return ApplyResult::new(Ter::TEL_INSUF_FEE_P, false, false);
        }

        let current_ledger_seq = self.current_ledger_seq;
        let load_fee_track = self.load_fee_track;
        let mut sandbox = ledger::FlowSandbox::new(&mut *self.submit_view);
        let mut applied_predecessors = Vec::new();
        for queued in &predecessors {
            let (result, _, applied_batch_inner_transactions) = Self::clear_ahead_apply(
                current_ledger_seq,
                load_fee_track,
                &mut sandbox,
                &queued.tx,
                // A clear-ahead predecessor is a persisted MaybeTx. TxQ.cpp
                // invokes MaybeTx::apply, which retains that entry's flags.
                queued.flags,
                self.node_network_id,
            );
            self.clear_ahead_attempts
                .push((queued.seq_proxy, result.clone()));
            // TxQ.cpp:573-586 treats a queued ticket that was already used in
            // the ledger as a completed predecessor so the later success
            // cleanup can discard it.
            if result.ter == Ter::TEF_NO_TICKET {
                continue;
            }
            if !result.applied {
                return result;
            }
            applied_predecessors.push((Arc::clone(&queued.tx), applied_batch_inner_transactions));
        }

        let (current, delivered, current_batch_inner_transactions) = Self::clear_ahead_apply(
            current_ledger_seq,
            load_fee_track,
            &mut sandbox,
            &self.tx,
            self.preflight_result.flags,
            self.node_network_id,
        );
        if !current.applied {
            return current;
        }
        if sandbox.apply().is_err() {
            return ApplyResult::new(Ter::TEF_INTERNAL, false, false);
        }

        for (queued, inner_transactions) in &applied_predecessors {
            record_applied_open_transactions(self.view, Arc::clone(queued), inner_transactions);
            self.record_clear_ahead_open_ledger_tx(queued);
            for inner in inner_transactions {
                self.record_clear_ahead_open_ledger_tx(&Arc::new(inner.transaction.clone()));
            }
        }
        record_applied_open_transactions(
            self.view,
            Arc::clone(&self.tx),
            &current_batch_inner_transactions,
        );
        self.record_clear_ahead_open_ledger_tx(&self.tx);
        for inner in &current_batch_inner_transactions {
            self.record_clear_ahead_open_ledger_tx(&Arc::new(inner.transaction.clone()));
        }
        self.delivered_amount = delivered;
        self.clear_ahead_removed = predecessors.iter().map(|queued| queued.seq_proxy).collect();
        if self
            .clear_ahead_queue
            .iter()
            .any(|queued| queued.seq_proxy == target)
        {
            self.clear_ahead_removed.push(target);
        }
        current
    }

    fn apply_sandbox(&mut self) {
        // `run_try_clear` already committed its child only on complete success.
    }
}

#[derive(Clone)]
struct StandaloneAcceptedTx {
    transaction_id: Uint256,
    txn: Arc<Serializer>,
    metadata: Arc<Serializer>,
    delta_meta_nodes: protocol::JsonValue,
}

/// An inner transaction that reached the applied (`tes*` or `tec*`) state in
/// the isolated Batch view. It is staged until the entire Batch policy decides
/// whether that view can be committed.
pub(crate) struct AppliedBatchInnerTransaction {
    pub(crate) transaction: STTx,
    pub(crate) result: Ter,
    pub(crate) metadata: protocol::TxMeta,
}

fn record_applied_open_transactions(
    open_ledger: &mut AppOpenLedgerView,
    outer: Arc<STTx>,
    inner_transactions: &[AppliedBatchInnerTransaction],
) {
    open_ledger.push_transaction(outer);
    // `xrpl::apply` (the TxQ/OpenLedger boundary) never runs Batch's inner
    // phase. Inner transactions are inserted only by closed-ledger
    // `applyTransaction`, so this slice must be empty for every open-ledger
    // caller and can never enter the proposed transaction set independently.
    debug_assert!(inner_transactions.is_empty());
}

pub(crate) struct SubmitApplyOutcome {
    pub(crate) result: Ter,
    pub(crate) applied: bool,
    pub(crate) delivered_amount: Option<STAmount>,
    /// Batch is applied in two ordered phases, matching rippled: the outer
    /// transaction is metadata-built and threaded before any inner delta is
    /// opened. Closed-ledger callers must therefore reuse this metadata and
    /// commit the already-threaded aggregate sandbox without threading it as
    /// the outer transaction a second time.
    pub(crate) prebuilt_outer_metadata: Option<protocol::TxMeta>,
    pub(crate) applied_batch_inner_transactions: Vec<AppliedBatchInnerTransaction>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BatchApplyDestination {
    Open,
    Closed,
    DryRun,
}

impl BatchApplyDestination {
    fn for_view(view: &dyn ledger::ReadView, flags: ApplyFlags) -> Self {
        if protocol::any_apply_flags(flags & ApplyFlags::DRY_RUN) {
            Self::DryRun
        } else if view.open() {
            Self::Open
        } else {
            Self::Closed
        }
    }

    fn builds_metadata(self) -> bool {
        matches!(self, Self::Closed | Self::DryRun)
    }
}

/// Result of a TxQ-admitted dry run. The state delta is retained only as
/// metadata; the cloned TxQ and ApplyView never publish or mutate live state.
#[derive(Clone)]
pub struct SimulationOutcome {
    pub result: ApplyResult,
    pub ledger_seq: u32,
    pub close_time: u32,
    pub metadata: Option<protocol::TxMeta>,
}

struct BatchFollowupOutcome {
    result: Ter,
    applied_inner_transactions: Vec<AppliedBatchInnerTransaction>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AcceptedLedgerLclInstall {
    /// Legacy/non-consensus callers install the built child immediately.
    Unconditional,
    /// The active consensus path installs only after `consensusBuilt` and
    /// `OpenLedger::accept`, matching rippled `doAccept` ordering.
    Deferred,
}

#[derive(Clone)]
pub(crate) struct AcceptedLedgerOutcome {
    /// Exact locally built child that atomically replaced its captured parent.
    /// Consensus post-accept work must use this snapshot rather than re-read
    /// the moving global LCL.
    pub closed: Arc<Ledger>,
    pub next_open_index: u32,
    /// IDs that must be removed from the previous open ledger because they
    /// were already included, were terminal failures, or were duplicates in
    /// the parent ledger.
    #[cfg_attr(not(test), allow(dead_code))]
    // asserted by state tests; not yet consumed by consensus
    pub completed_transaction_ids: std::collections::HashSet<Uint256>,
    /// Retry-class transactions that BuildLedger leaves for the next open
    /// ledger, including entries received from a peer consensus set.
    pub retry_transactions: Vec<Arc<STTx>>,
}

struct StandaloneLedgerBuildView {
    inner: OpenView<Ledger>,
    state_table: Option<ledger::ApplyStateTable>,
}

impl StandaloneLedgerBuildView {
    fn from_base(
        base: Arc<Ledger>,
        entries: &[StandaloneAcceptedTx],
        state_table: Option<ledger::ApplyStateTable>,
    ) -> Self {
        let mut inner = OpenView::new_closed(base);
        for entry in entries {
            inner
                .raw_tx_insert(
                    entry.transaction_id,
                    Arc::clone(&entry.txn),
                    Some(Arc::clone(&entry.metadata)),
                )
                .expect("standalone accepted tx overlay should insert");
        }
        Self { inner, state_table }
    }
}

impl crate::BuildLedgerView for StandaloneLedgerBuildView {
    fn open(&self) -> bool {
        self.inner.open()
    }

    fn tx_count(&self) -> usize {
        self.inner.tx_count()
    }

    fn apply_to_ledger(mut self, ledger: &mut Ledger) -> Result<(), crate::BuildLedgerError> {
        if let Some(table) = self.state_table.take() {
            table.apply(&mut self.inner).map_err(|error| {
                crate::BuildLedgerError::View(format!("state view apply failed: {error:?}"))
            })?;
        }
        self.inner.apply(ledger).map_err(|error| {
            crate::BuildLedgerError::View(format!("accepted view apply failed: {error:?}"))
        })
    }
}

impl AcceptLedgerPendingRuntime {
    #[cfg_attr(not(test), allow(dead_code))] // reachable only from the dormant accept path
    fn is_system_transaction(txn_type: TxType) -> bool {
        tx::run_with_system_transactor_txn_type_key(txn_type, |_| ()).is_ok()
    }

    #[cfg_attr(not(test), allow(dead_code))] // reachable only from the dormant accept path
    fn read_sttx(tx: &AcceptLedgerPendingTransaction) -> Arc<STTx> {
        tx.transaction
            .lock()
            .expect("transaction mutex must not be poisoned")
            .get_s_transaction()
            .clone()
    }
}

fn is_change_pseudo_transaction(txn_type: TxType) -> bool {
    matches!(
        txn_type,
        TxType::AMENDMENT | TxType::FEE | TxType::UNL_MODIFY
    )
}

/// Runs Change's distinct pseudo-transaction preflight. Change does not
/// inherit the ordinary preflight1 account rule: it requires a zero account,
/// zero fee, empty signature fields, and zero sequence instead.
fn change_pseudo_transaction_preflight_ter(tx: &STTx, rules: &Rules, node_network_id: u32) -> Ter {
    let account = get_field_by_symbol("sfAccount");
    let fee = get_field_by_symbol("sfFee");
    let signing_pub_key = get_field_by_symbol("sfSigningPubKey");
    let txn_signature = get_field_by_symbol("sfTxnSignature");
    let signers = get_field_by_symbol("sfSigners");
    let sequence = get_field_by_symbol("sfSequence");
    let previous_txn_id = get_field_by_symbol("sfPreviousTxnID");
    let network_id = get_field_by_symbol("sfNetworkID");
    let lending_protocol_enabled = rules.enabled(&protocol::feature_lending_protocol());

    tx::run_change_invoke_preflight_for_txn_type(
        tx.get_txn_type(),
        lending_protocol_enabled,
        || tx::run_change_preflight_flag_mask(lending_protocol_enabled),
        |flag_mask| {
            tx::run_transactor_preflight0(
                tx::TransactorPreflight0Facts {
                    is_pseudo_tx: true,
                    inner_batch_flag_set: tx.is_flag(tfInnerBatchTxn),
                    network_id_present: tx.is_field_present(network_id),
                    node_network_id,
                    tx_network_id: tx
                        .is_field_present(network_id)
                        .then(|| tx.get_field_u32(network_id)),
                    tx_id_is_zero: tx.get_transaction_id().is_zero(),
                    tx_flags: tx.get_flags(),
                },
                flag_mask,
            )
        },
        || {
            tx::run_change_preflight(
                Ter::TES_SUCCESS,
                tx::ChangePreflightFacts {
                    account_is_zero: tx.get_account_id(account).is_zero(),
                    fee_is_native_and_zero: tx.get_field_amount(fee).native()
                        && tx.get_field_amount(fee).xrp().drops() == 0,
                    signing_pub_key_empty: !tx.is_field_present(signing_pub_key)
                        || tx.get_field_vl(signing_pub_key).is_empty(),
                    signature_empty: !tx.is_field_present(txn_signature)
                        || tx.get_field_vl(txn_signature).is_empty(),
                    signers_present: tx.is_field_present(signers),
                    sequence_is_zero: !tx.is_field_present(sequence)
                        || tx.get_field_u32(sequence) == 0,
                    previous_txn_id_present: tx.is_field_present(previous_txn_id),
                },
            )
        },
    )
    .unwrap_or(Ter::TEM_UNKNOWN)
}

/// Shared canonical admission used before any queue or ledger-builder sandbox
/// is created. Signature checking belongs to shared preclaim, after typed
/// preflight, exactly as in rippled's `invokePreclaim`.
struct LoanSetCounterpartyPreflightTx {
    is_inner_batch_txn: bool,
    has_counterparty: bool,
    counterparty_signature: Option<STObject>,
}

impl tx::LoanSetPreflightTx for LoanSetCounterpartyPreflightTx {
    type CounterpartySignature = STObject;

    fn is_inner_batch_txn(&self) -> bool {
        self.is_inner_batch_txn
    }

    fn has_counterparty(&self) -> bool {
        self.has_counterparty
    }

    fn counterparty_signature(&self) -> Option<&Self::CounterpartySignature> {
        self.counterparty_signature.as_ref()
    }
}

/// `../rippled/src/libxrpl/tx/transactors/lending/LoanSet.cpp::LoanSet::preflight`: enforces the `CounterpartySignature` gate.
fn loan_set_counterparty_preflight_ter(tx: &STTx, rules: &Rules) -> Ter {
    let counterparty_signature = tx
        .is_field_present(get_field_by_symbol("sfCounterpartySignature"))
        .then(|| tx.get_field_object(get_field_by_symbol("sfCounterpartySignature")));
    let adapted = LoanSetCounterpartyPreflightTx {
        is_inner_batch_txn: tx.is_flag(tfInnerBatchTxn),
        has_counterparty: tx.is_field_present(get_field_by_symbol("sfCounterparty")),
        counterparty_signature,
    };

    match tx::run_loan_set_preflight_signature_gate(
        &adapted,
        rules.enabled(&protocol::feature_batch()),
        |signature| {
            let signing_pub_key = signature.get_field_vl(get_field_by_symbol("sfSigningPubKey"));
            tx::run_preflight_check_signing_key(tx::TransactorPreflightSigningKeyFacts {
                signing_pub_key_is_empty: signing_pub_key.is_empty(),
                signing_pub_key_type_known: PublicKey::from_slice(&signing_pub_key).is_ok(),
            })
        },
    ) {
        Ok(_) => Ter::TES_SUCCESS,
        Err(ter) => ter,
    }
}

pub(crate) fn transaction_preflight_ter(tx: &STTx, rules: &Rules) -> Ter {
    transaction_preflight_ter_with_flags(tx, rules, ApplyFlags::NONE)
}

pub(crate) fn transaction_preflight_ter_with_network_id(
    tx: &STTx,
    rules: &Rules,
    node_network_id: u32,
) -> Ter {
    transaction_preflight_ter_with_flags_and_network_id(
        tx,
        rules,
        ApplyFlags::NONE,
        node_network_id,
    )
}

/// Shared semantic preflight with explicit application flags. `simulate`
/// supplies `DRY_RUN`, which is how rippled lets unsigned simulated
/// transactions pass the signing boundary before TxQ admission.
pub fn transaction_preflight_ter_with_flags(tx: &STTx, rules: &Rules, flags: ApplyFlags) -> Ter {
    transaction_preflight_ter_with_flags_and_network_id(tx, rules, flags, 0)
}

pub fn transaction_preflight_ter_with_flags_and_network_id(
    tx: &STTx,
    rules: &Rules,
    flags: ApplyFlags,
    node_network_id: u32,
) -> Ter {
    transaction_preflight_ter_with_parent_batch_id(tx, rules, None, flags, node_network_id)
}

/// Shared semantic preflight with the `parentBatchId` supplied by
/// `rippled::preflight(..., parentBatchId, ..., TapBatch, ...)`.
fn transaction_preflight_ter_with_parent_batch_id(
    tx: &STTx,
    rules: &Rules,
    parent_batch_id: Option<Uint256>,
    flags: ApplyFlags,
    node_network_id: u32,
) -> Ter {
    tx::with_transaction_step_runtime(rules, || {
        transaction_preflight_ter_with_parent_batch_id_inner(
            tx,
            rules,
            parent_batch_id,
            flags,
            node_network_id,
        )
    })
}

fn transaction_preflight_ter_with_parent_batch_id_inner(
    tx: &STTx,
    rules: &Rules,
    parent_batch_id: Option<Uint256>,
    flags: ApplyFlags,
    node_network_id: u32,
) -> Ter {
    if is_change_pseudo_transaction(tx.get_txn_type()) {
        return change_pseudo_transaction_preflight_ter(tx, rules, node_network_id);
    }

    // The shared dispatcher preserves rippled's invokePreflight ordering for
    // Batch too: feature/extra-feature, preflight1, universal and sponsor
    // checks precede Batch's outer structure and canonical inner preflights.
    let semantic = tx::validate_sttx_transaction_preflight_with_rules_and_context(
        tx,
        rules,
        node_network_id,
        parent_batch_id.is_some(),
    );
    if !is_tes_success(semantic) {
        return semantic;
    }

    if tx.get_txn_type() == TxType::NFTOKEN_CANCEL_OFFER {
        let offer_ids = tx.get_field_v256(get_field_by_symbol("sfNFTokenOffers"));
        let ids = offer_ids.value();
        if ids.is_empty() || ids.len() > protocol::MAX_TOKEN_OFFER_CANCEL_COUNT {
            return Ter::TEM_MALFORMED;
        }
        if rules.enabled(&protocol::fix_cleanup_3_2_0()) && ids.iter().any(Uint256::is_zero) {
            return Ter::TEM_MALFORMED;
        }
        let mut sorted_ids = ids.to_vec();
        sorted_ids.sort();
        if sorted_ids.windows(2).any(|pair| pair[0] == pair[1]) {
            return Ter::TEM_MALFORMED;
        }
    }

    if tx.get_txn_type() == TxType::LOAN_SET {
        let counterparty_preflight = loan_set_counterparty_preflight_ter(tx, rules);
        if !is_tes_success(counterparty_preflight) {
            return counterparty_preflight;
        }
    }

    // `applySteps.cpp::preflight` constructs a context with parentBatchId for
    // inner transactions. Its signer gate is deliberately deferred to the
    // matching parent-aware shared preclaim path below; an inner transaction
    // has no standalone signature to validate here.
    if parent_batch_id.is_some() {
        return if tx.is_flag(tfInnerBatchTxn) {
            Ter::TES_SUCCESS
        } else {
            Ter::TEM_INVALID_INNER_BATCH
        };
    }

    if tx::any_apply_flags(flags & ApplyFlags::DRY_RUN) {
        // Parity: ../rippled/src/libxrpl/tx/Transactor.cpp::
        // preflightCheckSimulateKeys. Immutable preclaim remains responsible
        // for rejecting supplied malformed signature material.
        return Ter::TES_SUCCESS;
    }

    // checkValidity verifies the signature before local checks. preflight2
    // rejects only SigBad; SigGoodOnly (a locally non-canonical transaction)
    // remains a successful consensus preflight result and is filtered at the
    // outer admission boundary, exactly as in rippled.
    if tx.check_sign(rules).is_err() {
        return Ter::TEM_INVALID;
    }
    let _ = protocol::passes_local_checks(tx);

    // Concrete preflightSigValidated tails run after preflight2.
    if tx.get_txn_type() == TxType::ESCROW_FINISH {
        let credentials = get_field_by_symbol("sfCredentialIDs");
        if tx.is_field_present(credentials) {
            let ids = tx.get_field_v256(credentials);
            if rules.enabled(&protocol::feature_id("fixCleanup3_4_0"))
                && ids.value().iter().any(Uint256::is_zero)
            {
                return Ter::TEM_MALFORMED;
            }
            let result = ledger::credential_helpers::check_fields(tx, rules);
            if !is_tes_success(result) {
                return result;
            }
        }
    }
    if tx.get_txn_type() == TxType::BATCH {
        return tx::validate_sttx_batch_preflight_sig_validated(tx);
    }
    Ter::TES_SUCCESS
}

pub(crate) fn calculate_default_sttx_base_fee(view: &impl ReadView, tx: &STTx) -> u64 {
    let signer_count = if tx.is_field_present(get_field_by_symbol("sfSigners")) {
        tx.get_field_array(get_field_by_symbol("sfSigners")).len()
    } else {
        0
    };
    let sponsor_signer_count = if tx.is_field_present(get_field_by_symbol("sfSponsorSignature")) {
        let sponsor = tx.get_field_object(get_field_by_symbol("sfSponsorSignature"));
        if sponsor.is_field_present(get_field_by_symbol("sfSigners")) {
            sponsor
                .get_field_array(get_field_by_symbol("sfSigners"))
                .len()
        } else {
            0
        }
    } else {
        0
    };
    tx::run_transactor_calculate_base_fee(
        view.fees().base,
        signer_count.saturating_add(sponsor_signer_count),
    )
}

/// Shared exact base-fee dispatch for TxQ, replay, consensus, and direct
/// ledger construction. It starts with Transactor's multisign amount and then
/// applies only rippled's known specialized fee owners.
pub(crate) fn calculate_sttx_base_fee(view: &impl ReadView, tx: &STTx) -> Result<u64, Ter> {
    let rules = view.rules();
    tx::with_transaction_step_runtime(&rules, || calculate_sttx_base_fee_inner(view, tx))
}

fn calculate_sttx_base_fee_inner(view: &impl ReadView, tx: &STTx) -> Result<u64, Ter> {
    let ledger_base_fee = view.fees().base;
    let transactor_base_fee = calculate_default_sttx_base_fee(view, tx);
    let owner_reserve_fee = view.fees().increment;

    let fee = match tx.get_txn_type() {
        TxType::AMENDMENT | TxType::FEE | TxType::UNL_MODIFY => {
            tx::run_change_calculate_base_fee(0_u64)
        }
        TxType::BATCH => return batch_base_fee(view, tx),
        TxType::REGULAR_KEY_SET => {
            let signing_key =
                PublicKey::from_slice(&tx.get_field_vl(get_field_by_symbol("sfSigningPubKey")));
            let signing_key_matches = signing_key.as_ref().is_ok_and(|key| {
                calc_account_id(key.as_bytes())
                    == tx.get_account_id(get_field_by_symbol("sfAccount"))
            });
            let account_state = view
                .read(account_keylet(Uint160::from_void(
                    tx.get_account_id(get_field_by_symbol("sfAccount")).data(),
                )))
                .map_err(|_| Ter::TEF_BAD_LEDGER)?;
            let password_spent = account_state.as_ref().is_some_and(|account| {
                account.get_field_u32(get_field_by_symbol("sfFlags")) & protocol::lsfPasswordSpent
                    != 0
            });
            if signing_key_matches && account_state.is_some() && !password_spent {
                0
            } else {
                transactor_base_fee
            }
        }
        TxType::ACCOUNT_DELETE => {
            tx::run_account_delete_calculate_base_fee(ledger_base_fee, owner_reserve_fee)
        }
        TxType::AMM_CREATE => {
            tx::run_amm_create_calculate_base_fee(ledger_base_fee, owner_reserve_fee)
        }
        TxType::ESCROW_FINISH => tx::run_escrow_finish_calculate_base_fee(
            transactor_base_fee,
            ledger_base_fee,
            tx.is_field_present(get_field_by_symbol("sfFulfillment"))
                .then(|| tx.get_field_vl(get_field_by_symbol("sfFulfillment")).len()),
        ),
        TxType::LOAN_SET => {
            let counterparty = tx.get_field_object(get_field_by_symbol("sfCounterpartySignature"));
            let counterparty_signers =
                if counterparty.is_field_present(get_field_by_symbol("sfSigners")) {
                    counterparty
                        .get_field_array(get_field_by_symbol("sfSigners"))
                        .len()
                } else if counterparty.is_field_present(get_field_by_symbol("sfTxnSignature")) {
                    1
                } else {
                    0
                };
            transactor_base_fee
                + ledger_base_fee
                    * u64::try_from(counterparty_signers)
                        .expect("counterparty signer count must fit into u64")
        }
        TxType::LOAN_PAY => {
            crate::state::lending::calculate_loan_pay_base_fee(view, tx, transactor_base_fee)?
        }
        TxType::LEDGER_STATE_FIX => {
            tx::run_ledger_state_fix_calculate_base_fee(ledger_base_fee, owner_reserve_fee)
        }
        TxType::CONFIDENTIAL_MPT_CONVERT
        | TxType::CONFIDENTIAL_MPT_MERGE_INBOX
        | TxType::CONFIDENTIAL_MPT_CONVERT_BACK
        | TxType::CONFIDENTIAL_MPT_SEND
        | TxType::CONFIDENTIAL_MPT_CLAWBACK => {
            transactor_base_fee
                + ledger_base_fee
                    * u64::from(protocol::confidential_transfer::CONFIDENTIAL_FEE_MULTIPLIER)
        }
        _ => transactor_base_fee,
    };
    Ok(fee)
}

/// Explicitly infallible adapter for non-consensus fee displays/metrics.
/// Consensus and TxQ admission must call `calculate_sttx_base_fee` and
/// propagate its hard error.
pub(crate) fn calculate_sttx_base_fee_for_metrics(view: &impl ReadView, tx: &STTx) -> u64 {
    calculate_sttx_base_fee(view, tx).unwrap_or_else(|_| calculate_default_sttx_base_fee(view, tx))
}

/// Batch's invalid calculation is a documented sentinel consumed by its typed
/// preclaim. Every other fee must be representable at this signed TxQ boundary.
pub(crate) fn fee_drops_as_i64(fee: u64) -> i64 {
    if fee == INVALID_BATCH_BASE_FEE {
        i64::MAX
    } else {
        i64::try_from(fee).expect("validated XRPL fee must fit into i64")
    }
}

pub(crate) fn queue_apply_preclaim_ter(
    view: &impl ReadView,
    tx: &STTx,
    current_ledger_seq: u32,
    flags: ApplyFlags,
) -> Ter {
    queue_apply_preclaim_ter_with_parent_batch_id(view, tx, current_ledger_seq, flags, None)
}

/// Shared immutable preclaim with the same parent Batch context passed by
/// `rippled::applySteps.cpp::preclaim` into `PreclaimContext`.
fn queue_apply_preclaim_ter_with_parent_batch_id(
    view: &impl ReadView,
    tx: &STTx,
    current_ledger_seq: u32,
    flags: ApplyFlags,
    parent_batch_id: Option<Uint256>,
) -> Ter {
    let rules = view.rules();
    tx::with_transaction_step_runtime(&rules, || {
        crate::state::invoke_preclaim::invoke_preclaim_with_parent_batch_id(
            view,
            tx,
            current_ledger_seq,
            flags,
            parent_batch_id,
            || batch_check_sign_ter(view, tx, flags),
            || calculate_sttx_base_fee(view, tx).map(fee_drops_as_i64),
            |base_fee| base_fee,
            || {
                let typed_preclaim = typed_preclaim_ter(view, tx, flags);
                if !is_tes_success(typed_preclaim) {
                    return typed_preclaim;
                }

                if tx.get_txn_type() == TxType::BATCH {
                    batch_preclaim_ter(view, tx, flags)
                } else {
                    Ter::TES_SUCCESS
                }
            },
        )
    })
}

pub(crate) fn queue_apply_preclaim_ter_with_load_fee(
    view: &impl ReadView,
    tx: &STTx,
    current_ledger_seq: u32,
    flags: ApplyFlags,
    load_fee_track: &SharedLoadFeeTrack,
) -> Ter {
    let (fee_factor, remote_fee_factor) = load_fee_track.scaling_factors();
    let rules = view.rules();
    tx::with_transaction_step_runtime(&rules, || {
        crate::state::invoke_preclaim::invoke_preclaim_with_parent_batch_id(
            view,
            tx,
            current_ledger_seq,
            flags,
            None,
            || batch_check_sign_ter(view, tx, flags),
            || calculate_sttx_base_fee(view, tx).map(fee_drops_as_i64),
            |base_fee| {
                crate::state::invoke_preclaim::scale_fee_load(
                    base_fee,
                    fee_factor,
                    remote_fee_factor,
                    load_fee_track.load_base(),
                    tx::any_apply_flags(flags & ApplyFlags::UNLIMITED),
                )
            },
            || {
                let typed_preclaim = typed_preclaim_ter(view, tx, flags);
                if !is_tes_success(typed_preclaim) {
                    return typed_preclaim;
                }

                if tx.get_txn_type() == TxType::BATCH {
                    batch_preclaim_ter(view, tx, flags)
                } else {
                    Ter::TES_SUCCESS
                }
            },
        )
    })
}
/// ../rippled/src/libxrpl/tx/applySteps.cpp::invokePreclaim (lines 162-201).
/// Explicit classification for every routed Quaxar transaction type's typed
/// preclaim tail. A route may only name an already-compiled immutable
/// ReadView helper, an audited rippled inherited no-op owned by such a helper,
/// the existing Batch special preclaim, or the fail-closed result below.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TypedPreclaimRoute {
    AppReadViewHelper,
    ChangeReadViewHelper,
    AppAuditedNoop,
    DexReadViewHelper,
    LoanReadViewHelper,
    NfTokenReadViewHelper,
    TokenReadViewHelper,
    TokenAuditedNoop,
    VaultReadViewHelper,
    BridgeDomainReadViewHelper,
    BridgeDomainAuditedNoop,
    SystemReadViewHelper,
    SponsorshipReadViewHelper,
    ConfidentialMptReadViewHelper,
    BatchSpecialPreclaim,
    FailClosed,
}

const UNVERIFIED_TYPED_PRECLAIM_TER: Ter = tx::UNKNOWN_TRANSACTION_TYPE_TER;

fn typed_preclaim_route(txn_type: TxType) -> TypedPreclaimRoute {
    match txn_type {
        TxType::ACCOUNT_SET
        | TxType::ACCOUNT_DELETE
        | TxType::DELEGATE_SET
        | TxType::DEPOSIT_PREAUTH
        | TxType::PAYMENT
        | TxType::PAYCHAN_CREATE
        | TxType::PAYCHAN_CLAIM
        | TxType::CHECK_CREATE
        | TxType::CHECK_CASH
        | TxType::CHECK_CANCEL
        | TxType::ESCROW_CREATE
        | TxType::ESCROW_FINISH
        | TxType::ESCROW_CANCEL => TypedPreclaimRoute::AppReadViewHelper,
        // These are explicit no-op arms inside the existing application
        // ReadView helper because their rippled transactors inherit
        // Transactor::preclaim unchanged.
        TxType::REGULAR_KEY_SET | TxType::SIGNER_LIST_SET | TxType::PAYCHAN_FUND => {
            TypedPreclaimRoute::AppAuditedNoop
        }
        TxType::OFFER_CREATE
        | TxType::OFFER_CANCEL
        | TxType::AMM_CREATE
        | TxType::AMM_DEPOSIT
        | TxType::AMM_WITHDRAW
        | TxType::AMM_VOTE
        | TxType::AMM_BID
        | TxType::AMM_DELETE
        | TxType::AMM_CLAWBACK => TypedPreclaimRoute::DexReadViewHelper,
        TxType::LOAN_SET
        | TxType::LOAN_MANAGE
        | TxType::LOAN_PAY
        | TxType::LOAN_DELETE
        | TxType::LOAN_BROKER_SET
        | TxType::LOAN_BROKER_DELETE
        | TxType::LOAN_BROKER_COVER_DEPOSIT
        | TxType::LOAN_BROKER_COVER_WITHDRAW
        | TxType::LOAN_BROKER_COVER_CLAWBACK => TypedPreclaimRoute::LoanReadViewHelper,
        TxType::NFTOKEN_MINT
        | TxType::NFTOKEN_BURN
        | TxType::NFTOKEN_CREATE_OFFER
        | TxType::NFTOKEN_CANCEL_OFFER
        | TxType::NFTOKEN_ACCEPT_OFFER
        | TxType::NFTOKEN_MODIFY => TypedPreclaimRoute::NfTokenReadViewHelper,
        TxType::TRUST_SET
        | TxType::CLAWBACK
        | TxType::MPTOKEN_AUTHORIZE
        | TxType::MPTOKEN_ISSUANCE_DESTROY
        | TxType::MPTOKEN_ISSUANCE_SET => TypedPreclaimRoute::TokenReadViewHelper,
        // Explicit inside token_read_view_preclaim.rs: rippled
        // MPTokenIssuanceCreate inherits Transactor::preclaim unchanged.
        TxType::MPTOKEN_ISSUANCE_CREATE => TypedPreclaimRoute::TokenAuditedNoop,
        TxType::VAULT_CREATE
        | TxType::VAULT_SET
        | TxType::VAULT_DELETE
        | TxType::VAULT_DEPOSIT
        | TxType::VAULT_WITHDRAW
        | TxType::VAULT_CLAWBACK => TypedPreclaimRoute::VaultReadViewHelper,
        TxType::XCHAIN_CREATE_CLAIM_ID
        | TxType::XCHAIN_COMMIT
        | TxType::XCHAIN_CLAIM
        | TxType::XCHAIN_ACCOUNT_CREATE_COMMIT
        | TxType::XCHAIN_ADD_CLAIM_ATTESTATION
        | TxType::XCHAIN_ADD_ACCOUNT_CREATE_ATTESTATION
        | TxType::XCHAIN_MODIFY_BRIDGE
        | TxType::XCHAIN_CREATE_BRIDGE
        | TxType::ORACLE_SET
        | TxType::ORACLE_DELETE
        | TxType::PERMISSIONED_DOMAIN_SET
        | TxType::PERMISSIONED_DOMAIN_DELETE
        | TxType::CREDENTIAL_CREATE
        | TxType::CREDENTIAL_ACCEPT
        | TxType::CREDENTIAL_DELETE => TypedPreclaimRoute::BridgeDomainReadViewHelper,
        // Explicit inside bridge_domain_read_view_preclaim.rs: DIDSet and
        // DIDDelete inherit Transactor::preclaim unchanged in rippled.
        TxType::DID_SET | TxType::DID_DELETE => TypedPreclaimRoute::BridgeDomainAuditedNoop,
        // Batch has its own existing immutable preclaim below, after the
        // family-tail dispatch has succeeded.
        TxType::BATCH => TypedPreclaimRoute::BatchSpecialPreclaim,
        TxType::AMENDMENT | TxType::FEE | TxType::UNL_MODIFY => {
            TypedPreclaimRoute::ChangeReadViewHelper
        }
        TxType::TICKET_CREATE | TxType::LEDGER_STATE_FIX => {
            TypedPreclaimRoute::SystemReadViewHelper
        }
        TxType::SPONSORSHIP_TRANSFER | TxType::SPONSORSHIP_SET => {
            TypedPreclaimRoute::SponsorshipReadViewHelper
        }
        TxType::CONFIDENTIAL_MPT_CONVERT
        | TxType::CONFIDENTIAL_MPT_MERGE_INBOX
        | TxType::CONFIDENTIAL_MPT_CONVERT_BACK
        | TxType::CONFIDENTIAL_MPT_SEND
        | TxType::CONFIDENTIAL_MPT_CLAWBACK => TypedPreclaimRoute::ConfidentialMptReadViewHelper,
        // Unknown and non-dispatchable protocol values are likewise closed.
        _ => TypedPreclaimRoute::FailClosed,
    }
}

/// Shared application-owned typed preclaim dispatcher used by both TxQ and
/// consensus BuildLedger. Every success result comes from a concrete existing
/// helper, a documented inherited no-op, or Batch's existing special path.
fn typed_preclaim_ter(view: &impl ReadView, tx: &STTx, flags: ApplyFlags) -> Ter {
    match typed_preclaim_route(tx.get_txn_type()) {
        TypedPreclaimRoute::AppReadViewHelper | TypedPreclaimRoute::AppAuditedNoop => {
            crate::state::read_view_preclaim::run_read_view_preclaim(
                view,
                tx,
                tx.get_txn_type(),
                flags,
            )
            .unwrap_or(UNVERIFIED_TYPED_PRECLAIM_TER)
        }
        TypedPreclaimRoute::ChangeReadViewHelper => {
            tx::run_change_read_view_preclaim(view, tx, tx.get_txn_type())
                .unwrap_or(UNVERIFIED_TYPED_PRECLAIM_TER)
        }
        TypedPreclaimRoute::DexReadViewHelper => {
            tx::run_dex_read_view_preclaim_with_flags(view, tx, tx.get_txn_type(), flags)
                .unwrap_or(UNVERIFIED_TYPED_PRECLAIM_TER)
        }
        TypedPreclaimRoute::LoanReadViewHelper => {
            tx::run_loan_read_view_preclaim(view, tx, tx.get_txn_type())
                .unwrap_or(UNVERIFIED_TYPED_PRECLAIM_TER)
        }
        TypedPreclaimRoute::NfTokenReadViewHelper => {
            tx::run_nftoken_read_view_preclaim(view, tx, tx.get_txn_type())
                .unwrap_or(UNVERIFIED_TYPED_PRECLAIM_TER)
        }
        TypedPreclaimRoute::TokenReadViewHelper | TypedPreclaimRoute::TokenAuditedNoop => {
            tx::run_token_read_view_preclaim(view, tx, tx.get_txn_type())
                .unwrap_or(UNVERIFIED_TYPED_PRECLAIM_TER)
        }
        TypedPreclaimRoute::VaultReadViewHelper => {
            tx::run_vault_read_view_preclaim(view, tx, tx.get_txn_type())
                .unwrap_or(UNVERIFIED_TYPED_PRECLAIM_TER)
        }
        TypedPreclaimRoute::BridgeDomainReadViewHelper
        | TypedPreclaimRoute::BridgeDomainAuditedNoop => {
            tx::run_bridge_domain_read_view_preclaim(view, tx, tx.get_txn_type())
                .unwrap_or(UNVERIFIED_TYPED_PRECLAIM_TER)
        }
        TypedPreclaimRoute::SystemReadViewHelper => match tx.get_txn_type() {
            TxType::TICKET_CREATE => {
                tx::run_ticket_create_read_view_preclaim(view, tx, TxType::TICKET_CREATE)
                    .unwrap_or(UNVERIFIED_TYPED_PRECLAIM_TER)
            }
            TxType::LEDGER_STATE_FIX => {
                tx::run_ledger_state_fix_read_view_preclaim(view, tx, TxType::LEDGER_STATE_FIX)
                    .unwrap_or(UNVERIFIED_TYPED_PRECLAIM_TER)
            }
            _ => UNVERIFIED_TYPED_PRECLAIM_TER,
        },
        TypedPreclaimRoute::BatchSpecialPreclaim => Ter::TES_SUCCESS,
        TypedPreclaimRoute::SponsorshipReadViewHelper => {
            crate::state::sponsorship::preclaim(view, tx)
        }
        TypedPreclaimRoute::ConfidentialMptReadViewHelper => {
            crate::state::confidential_mpt::preclaim(view, tx)
        }
        TypedPreclaimRoute::FailClosed => UNVERIFIED_TYPED_PRECLAIM_TER,
    }
}

struct SubmitOracleSetReserveSink {
    balance_drops: i64,
    effective_owner_count: u32,
    effective_account_count: u32,
    fees: ledger::Fees,
}

impl tx::OracleSetReserveSink for SubmitOracleSetReserveSink {
    fn is_reserve_sufficient(&mut self, adjust_reserve: i8) -> bool {
        let owner_count = i64::from(self.effective_owner_count) + i64::from(adjust_reserve);
        owner_count >= 0
            && self.balance_drops
                >= self.fees.account_reserve_with_account_count(
                    owner_count as usize,
                    self.effective_account_count as usize,
                ) as i64
    }
}

fn oracle_set_series(st_tx: &STTx) -> Vec<tx::OracleSetSeriesEntry> {
    tx::oracle_set_series_from_stobject(st_tx)
}

fn run_oracle_set_preclaim_with_view<V: ReadView>(view: &V, st_tx: &STTx) -> Ter {
    let provider_field = get_field_by_symbol("sfProvider");
    let asset_class_field = get_field_by_symbol("sfAssetClass");
    let preflight = tx::run_oracle_set_sttx_preflight(st_tx);
    if preflight != Ter::TES_SUCCESS {
        return preflight;
    }

    let account = st_tx.get_account_id(get_field_by_symbol("sfAccount"));
    let account_sle = match view.read(account_keylet(
        Uint160::from_slice(account.data()).expect("account width should match Uint160"),
    )) {
        Ok(Some(sle)) => sle,
        Ok(None) => return Ter::TER_NO_ACCOUNT,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    let oracle = match view.read(protocol::oracle_keylet(
        Uint160::from_slice(account.data()).expect("account width should match Uint160"),
        st_tx.get_field_u32(get_field_by_symbol("sfOracleDocumentID")),
    )) {
        Ok(oracle) => oracle,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };
    let provider_present = st_tx.is_field_present(provider_field);
    let asset_class_present = st_tx.is_field_present(asset_class_field);
    let oracle_exists = oracle.is_some();
    let (
        tx_provider_matches_existing,
        tx_asset_class_matches_existing,
        previous_last_update_time_secs,
        existing_pairs,
    ) = if let Some(oracle) = oracle.as_ref() {
        (
            !provider_present
                || st_tx.get_field_vl(provider_field) == oracle.get_field_vl(provider_field),
            !asset_class_present
                || st_tx.get_field_vl(asset_class_field) == oracle.get_field_vl(asset_class_field),
            u64::from(oracle.get_field_u32(get_field_by_symbol("sfLastUpdateTime"))),
            oracle_set_series(&STTx::from_stobject(oracle.clone_as_object()))
                .into_iter()
                .map(|entry| entry.pair)
                .collect(),
        )
    } else {
        (false, false, 0, Vec::new())
    };

    let facts = tx::OracleSetPreclaimFacts {
        front: tx::OracleSetPreclaimFrontFacts {
            account_exists: true,
            close_time_secs: u64::from(view.header().close_time),
            last_update_time_secs: u64::from(
                st_tx.get_field_u32(get_field_by_symbol("sfLastUpdateTime")),
            ),
        },
        oracle_exists,
        tx_provider_present: provider_present,
        tx_asset_class_present: asset_class_present,
        tx_provider_matches_existing,
        tx_asset_class_matches_existing,
        previous_last_update_time_secs,
        tx_series: oracle_set_series(st_tx),
        existing_pairs,
    };
    let mut reserve_sink = SubmitOracleSetReserveSink {
        balance_drops: account_sle
            .get_field_amount(get_field_by_symbol("sfBalance"))
            .xrp()
            .drops(),
        effective_owner_count: ledger::reserve_owner_count(&account_sle, 0),
        effective_account_count: ledger::reserve_account_count(&account_sle, 0),
        fees: view.fees(),
    };
    tx::run_oracle_set_preclaim(facts, &mut reserve_sink)
}

fn submit_confine_owner_count(current: u32, adjustment: i32) -> u32 {
    let result = current as i64 + adjustment as i64;
    if result < 0 {
        0
    } else if result > u32::MAX as i64 {
        u32::MAX
    } else {
        result as u32
    }
}

fn delete_submit_ticket<V: ledger::ApplyView>(
    view: &mut V,
    account: AccountID,
    account_state: &mut STLedgerEntry,
    tx_seq_proxy: SeqProxy,
) -> Ter {
    let account_uint160 =
        Uint160::from_slice(account.data()).expect("account width should match Uint160");
    let ticket_keylet = protocol::ticket_keylet_from_seq_proxy(account_uint160, tx_seq_proxy);
    let ticket = match view.peek(ticket_keylet) {
        Ok(Some(sle)) => Some(SubmitConsumedTicket {
            owner_page: sle.get_field_u64(get_field_by_symbol("sfOwnerNode")),
            sle,
        }),
        Ok(None) => None,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    let Some(ticket) = ticket else {
        // Preclaim already established that the ticket existed. Disappearing
        // before apply is corrupt ledger state in Transactor::ticketDelete.
        return Ter::TEF_BAD_LEDGER;
    };

    if !ledger::dir_remove(
        view,
        &protocol::owner_dir_keylet(account_uint160),
        ticket.owner_page,
        *ticket.sle.key(),
        true,
    )
    .unwrap_or(false)
    {
        return Ter::TEF_BAD_LEDGER;
    }

    if !account_state.is_field_present(get_field_by_symbol("sfTicketCount")) {
        return Ter::TEF_BAD_LEDGER;
    }

    let ticket_count = account_state.get_field_u32(get_field_by_symbol("sfTicketCount"));
    if ticket_count == 1 {
        account_state.make_field_absent(get_field_by_symbol("sfTicketCount"));
    } else {
        account_state.set_field_u32(get_field_by_symbol("sfTicketCount"), ticket_count - 1);
    }

    let owner_count = account_state.get_field_u32(get_field_by_symbol("sfOwnerCount"));
    account_state.set_field_u32(
        get_field_by_symbol("sfOwnerCount"),
        submit_confine_owner_count(owner_count, -1),
    );

    match view.erase(ticket.sle) {
        Ok(()) => Ter::TES_SUCCESS,
        Err(_) => Ter::TEF_BAD_LEDGER,
    }
}

/// Apply exactly the canonical admission prefix used by `simulate`: semantic
/// preflight, immutable preclaim, then the dry-run transaction shell. This
/// mirrors ../rippled/src/xrpld/rpc/handlers/transaction/Simulate.cpp, which
/// invokes `TxQ::apply(..., TapDryRun)` rather than dispatching a transactor
/// directly.
pub fn apply_simulated_transaction<V: ledger::ApplyView>(
    view: &mut V,
    tx: &STTx,
) -> (Ter, Option<STAmount>) {
    apply_simulated_transaction_with_network_id(view, tx, 0)
}

pub fn apply_simulated_transaction_with_network_id<V: ledger::ApplyView>(
    view: &mut V,
    tx: &STTx,
    node_network_id: u32,
) -> (Ter, Option<STAmount>) {
    let flags = ApplyFlags::DRY_RUN;
    let preflight = transaction_preflight_ter_with_flags_and_network_id(
        tx,
        &view.rules(),
        flags,
        node_network_id,
    );
    let preclaim = if is_tes_success(preflight) {
        queue_apply_preclaim_ter(view, tx, view.seq(), flags)
    } else {
        preflight
    };

    if is_tes_success(preclaim) || is_tec_claim(preclaim) {
        let outcome =
            apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim_and_network_id(
                view,
                tx,
                tx.get_txn_type(),
                flags,
                preclaim,
                node_network_id,
            );
        (outcome.result, outcome.delivered_amount)
    } else {
        (preclaim, None)
    }
}

pub fn apply_submit_transactor_shell<V: ledger::ApplyView>(
    view: &mut V,
    tx: &STTx,
    txn_type: TxType,
) -> Ter {
    apply_submit_transactor_shell_with_flags(view, tx, txn_type, ApplyFlags::NONE)
}

pub fn apply_submit_transactor_shell_with_flags<V: ledger::ApplyView>(
    view: &mut V,
    tx: &STTx,
    txn_type: TxType,
    flags: ApplyFlags,
) -> Ter {
    apply_submit_transactor_shell_with_flags_and_delivered_amount(view, tx, txn_type, flags).0
}

/// Applies a transaction and returns any `ApplyContext::deliver` value recorded
/// by Payment, CheckCash, or AccountDelete for canonical metadata construction.
pub fn apply_submit_transactor_shell_with_delivered_amount<V: ledger::ApplyView>(
    view: &mut V,
    tx: &STTx,
    txn_type: TxType,
) -> (Ter, Option<STAmount>) {
    apply_submit_transactor_shell_with_flags_and_delivered_amount(
        view,
        tx,
        txn_type,
        ApplyFlags::NONE,
    )
}

fn apply_submit_transactor_shell_with_flags_and_delivered_amount<V: ledger::ApplyView>(
    view: &mut V,
    tx: &STTx,
    txn_type: TxType,
    flags: ApplyFlags,
) -> (Ter, Option<STAmount>) {
    apply_submit_transactor_shell_with_preclaim_and_delivered_amount(
        view,
        tx,
        txn_type,
        flags,
        Ter::TES_SUCCESS,
    )
}

pub(crate) fn apply_submit_transactor_shell_with_preclaim_and_delivered_amount<
    V: ledger::ApplyView,
>(
    view: &mut V,
    tx: &STTx,
    txn_type: TxType,
    flags: ApplyFlags,
    preclaim_result: Ter,
) -> (Ter, Option<STAmount>) {
    let outcome = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim(
        view,
        tx,
        txn_type,
        flags,
        preclaim_result,
    );
    (outcome.result, outcome.delivered_amount)
}

pub(crate) fn apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim<
    V: ledger::ApplyView,
>(
    view: &mut V,
    tx: &STTx,
    txn_type: TxType,
    flags: ApplyFlags,
    preclaim_result: Ter,
) -> SubmitApplyOutcome {
    apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim_and_network_id(
        view,
        tx,
        txn_type,
        flags,
        preclaim_result,
        0,
    )
}

pub(crate) fn apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim_and_network_id<
    V: ledger::ApplyView,
>(
    view: &mut V,
    tx: &STTx,
    txn_type: TxType,
    flags: ApplyFlags,
    mut preclaim_result: Ter,
    node_network_id: u32,
) -> SubmitApplyOutcome {
    // An inner Batch transaction is valid only while its parent Batch applies
    // it through apply_submit_batch_followup. Never allow one through the
    // standalone transaction entry point.
    if txn_type != TxType::BATCH && tx.is_flag(tfInnerBatchTxn) {
        return SubmitApplyOutcome {
            result: Ter::TEM_INVALID_INNER_BATCH,
            applied: false,
            delivered_amount: None,
            prebuilt_outer_metadata: None,
            applied_batch_inner_transactions: Vec::new(),
        };
    }

    let rules = view.rules();
    // This is the exact ApplyStateTable destination boundary: normal open
    // ledger application does not build/thread metadata, while closed-ledger
    // and TapDryRun application do. Capture it before opening child views so
    // Batch does not accidentally infer the mode from an intermediate parent.
    let batch_destination = BatchApplyDestination::for_view(view, flags);
    // Consensus, acquired-ledger, and replay builders call the shared
    // semantic preflight and immutable preclaim before entering this shell.
    // The public TxQ apply path already owns the same facts, so only Batch's
    // outer-only validation belongs here before its sandbox is opened.
    // Public/consensus paths reach this shell only after shared preflight and
    // invokePreclaim. Keep the direct Batch guard structural so test and
    // builder callers retain Batch::preflight's inner validation without
    // duplicating the outer raw-signature gate that shared preclaim owns.
    if txn_type == TxType::BATCH {
        let preflight = tx::validate_sttx_batch_preflight_with_rules_and_network_id(
            tx,
            &rules,
            node_network_id,
        );
        if !is_tes_success(preflight) {
            return SubmitApplyOutcome {
                result: preflight,
                applied: false,
                delivered_amount: None,
                prebuilt_outer_metadata: None,
                applied_batch_inner_transactions: Vec::new(),
            };
        }
        if is_tes_success(preclaim_result) {
            let batch_preclaim = batch_preclaim_ter(view, tx, flags);
            if !is_tes_success(batch_preclaim) && !is_tec_claim(batch_preclaim) {
                return SubmitApplyOutcome {
                    result: batch_preclaim,
                    applied: false,
                    delivered_amount: None,
                    prebuilt_outer_metadata: None,
                    applied_batch_inner_transactions: Vec::new(),
                };
            }
            preclaim_result = batch_preclaim;
        }
    }

    // applySteps.cpp::invokeApply enters withTxnType before constructing the
    // concrete Transactor; Transactor::operator() then installs its legacy
    // apply-time rules guard inside that scope.  The ordering matters on
    // ledgers without Lending/Vault: withTxnType's small-mantissa guard must
    // remain active throughout the common preamble, doApply, reset,
    // invariants and metadata construction, not only in typed helpers.
    tx::with_transaction_step_runtime(&rules, || {
        tx::with_transaction_apply_runtime(&rules, || {
            // ApplyContext owns DeliveredAmount in rippled. Scope its Rust
            // equivalent to this transaction so a Batch inner delivery cannot
            // populate its parent Batch metadata.
            let delivered_amount_capture = matches!(
                txn_type,
                TxType::PAYMENT | TxType::CHECK_CASH | TxType::ACCOUNT_DELETE
            )
            .then(crate::state::payment::DeliveredAmountCapture::new);

            // Match rippled's ApplyContext: every mutation, including the common
            // sequence/ticket and fee preamble, stays in a per-transaction view
            // until the final TER says the transaction is applied. rippled's
            // Transactor/BuildLedger catches arithmetic exceptions at this
            // transaction boundary; retain the same atomicity here by dropping the
            // unapplied FlowSandbox and reporting tefEXCEPTION.
            // Keep the complete applyTransaction operation isolated. This extra
            // level is essential for Batch: outer and inner phases have distinct
            // ApplyStateTables, yet an internal failure must not expose only the
            // already-threaded outer phase to an open-ledger caller.
            let mut transaction_sequence_view = ledger::FlowSandbox::new_with_flags(view, flags);
            let mut tx_view =
                ledger::FlowSandbox::new_with_flags(&mut transaction_sequence_view, flags);
            let mut invariant_fee_reset = false;
            let mut result = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                apply_submit_transactor_shell_impl(
                    &mut tx_view,
                    tx,
                    txn_type,
                    flags,
                    preclaim_result,
                    &mut invariant_fee_reset,
                    node_network_id,
                )
            })) {
                Ok(result) => result,
                Err(payload) => {
                    let message = payload
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| {
                            payload
                                .downcast_ref::<&str>()
                                .map(|message| (*message).to_owned())
                        })
                        .unwrap_or_else(|| "non-string panic payload".to_owned());
                    tracing::error!(
                        target: "tx",
                        tx_id = %tx.get_transaction_id(),
                        ?txn_type,
                        %message,
                        "transaction execution panicked; mapped to tefEXCEPTION"
                    );
                    return SubmitApplyOutcome {
                        result: Ter::TEF_EXCEPTION,
                        applied: false,
                        delivered_amount: None,
                        prebuilt_outer_metadata: None,
                        applied_batch_inner_transactions: Vec::new(),
                    };
                }
            };

            // `rippled::applyTransaction` finishes ApplyStateTable::apply for the
            // outer Batch before it opens the whole-batch view. That boundary is
            // consensus-significant: outer metadata must not contain inner nodes,
            // and the final SLE thread must belong to the last inner transaction.
            let mut applied_batch_inner_transactions = Vec::new();
            if is_tes_success(result)
                && txn_type == TxType::BATCH
                && batch_destination == BatchApplyDestination::Closed
            {
                let outer_tx_id = tx.get_transaction_id();
                let outer_ledger_seq = tx_view.seq();
                let outer_metadata = if batch_destination.builds_metadata() {
                    match tx_view.to_tx_meta(outer_tx_id, outer_ledger_seq, None, &rules) {
                        Ok(metadata) => metadata,
                        Err(_) => {
                            return SubmitApplyOutcome {
                                result: Ter::TEF_INTERNAL,
                                applied: false,
                                delivered_amount: None,
                                prebuilt_outer_metadata: None,
                                applied_batch_inner_transactions: Vec::new(),
                            };
                        }
                    }
                } else {
                    protocol::TxMeta::new(outer_tx_id, outer_ledger_seq)
                };
                let outer_commit = if batch_destination == BatchApplyDestination::Closed {
                    tx_view.apply_with_tx_meta(outer_tx_id, outer_ledger_seq, None, None, &rules)
                } else {
                    tx_view.apply().map(|()| outer_metadata.clone())
                };
                let outer_metadata = match outer_commit {
                    Ok(metadata) => metadata,
                    Err(_) => {
                        return SubmitApplyOutcome {
                            result: Ter::TEF_INTERNAL,
                            applied: false,
                            delivered_amount: None,
                            prebuilt_outer_metadata: None,
                            applied_batch_inner_transactions: Vec::new(),
                        };
                    }
                };
                // The parent now contains only the fully-applied outer Batch.
                // Open the inner whole-batch phase over that state, as rippled
                // does, rather than folding it back into the outer state table.
                let followup = apply_submit_batch_followup(
                    &mut transaction_sequence_view,
                    tx,
                    batch_destination,
                    node_network_id,
                );
                result = followup.result;
                applied_batch_inner_transactions = followup.applied_inner_transactions;
                if !is_tes_success(result) {
                    applied_batch_inner_transactions.clear();
                    return SubmitApplyOutcome {
                        result,
                        applied: false,
                        delivered_amount: None,
                        prebuilt_outer_metadata: None,
                        applied_batch_inner_transactions,
                    };
                }
                if transaction_sequence_view.apply().is_err() {
                    return SubmitApplyOutcome {
                        result: Ter::TEF_INTERNAL,
                        applied: false,
                        delivered_amount: None,
                        prebuilt_outer_metadata: None,
                        applied_batch_inner_transactions: Vec::new(),
                    };
                }
                return SubmitApplyOutcome {
                    result,
                    applied: batch_destination != BatchApplyDestination::DryRun,
                    delivered_amount: None,
                    prebuilt_outer_metadata: (batch_destination == BatchApplyDestination::Closed)
                        .then_some(outer_metadata),
                    applied_batch_inner_transactions,
                };
            }

            let fail_hard_tec =
                is_tec_claim(result) && protocol::any_apply_flags(flags & ApplyFlags::FAIL_HARD);
            let persistent_cleanup_tec = matches!(
                result,
                Ter::TEC_OVERSIZE | Ter::TEC_KILLED | Ter::TEC_INCOMPLETE | Ter::TEC_EXPIRED
            );
            let invariant_fee_reset_applies =
                invariant_fee_reset && result == Ter::TEC_INVARIANT_FAILED;
            let mut applied = false;
            if (likely_to_claim_fee(result, flags)
                || persistent_cleanup_tec
                || invariant_fee_reset_applies)
                && (!fail_hard_tec || invariant_fee_reset_applies)
            {
                // Ordinary retry-pass `tec` results remain unapplied so
                // BuildLedger can retry them after the canonical input. rippled
                // immediately applies the four persistent-cleanup outcomes even
                // during that pass, preserving their canonical deletions.
                // A commit failure means the parent changed underneath this
                // transaction. Never report an applied result after discarding a
                // `FlowSandbox::apply` error.
                if tx_view.apply().is_err() || transaction_sequence_view.apply().is_err() {
                    result = Ter::TEF_INTERNAL;
                    applied_batch_inner_transactions.clear();
                } else {
                    applied = !protocol::any_apply_flags(flags & ApplyFlags::DRY_RUN);
                }
            } else {
                applied_batch_inner_transactions.clear();
            }
            let delivered_amount = delivered_amount_capture
                .and_then(crate::state::payment::DeliveredAmountCapture::finish)
                .filter(|_| is_tes_success(result));
            SubmitApplyOutcome {
                result,
                applied,
                delivered_amount,
                prebuilt_outer_metadata: None,
                applied_batch_inner_transactions,
            }
        })
    })
}

fn apply_submit_transactor_shell_impl<V: ledger::ApplyView + ?Sized>(
    view: &mut ledger::FlowSandbox<'_, V>,
    tx: &STTx,
    txn_type: TxType,
    flags: ApplyFlags,
    preclaim_result: Ter,
    invariant_fee_reset: &mut bool,
    node_network_id: u32,
) -> Ter {
    let account_field = get_field_by_symbol("sfAccount");

    let is_pseudo = is_change_pseudo_transaction(txn_type);
    if is_pseudo {
        let preflight = tx::validate_sttx_transaction_preflight_with_rules_and_network_id(
            tx,
            &view.rules(),
            node_network_id,
        );
        if !is_tes_success(preflight) {
            return preflight;
        }
        return if is_tes_success(preclaim_result) {
            handle_real_dispatch(view, tx, txn_type, None)
        } else {
            preclaim_result
        };
    }

    // --- reference preflight1 checks ---
    // Bad account ID
    if tx.is_field_present(account_field) {
        let account = tx.get_account_id(account_field);
        if account.data().iter().all(|&b| b == 0) {
            return Ter::TEM_BAD_SRC_ACCOUNT;
        }
    }
    // Bad fee (must be native, non-negative)
    let fee_field = get_field_by_symbol("sfFee");
    if tx.is_field_present(fee_field) {
        let fee = tx.get_field_amount(fee_field);
        if !fee.native() || fee.negative() {
            return Ter::TEM_BAD_FEE;
        }
    }
    // Ticket + AccountTxnID is invalid
    let account_txn_id_field = get_field_by_symbol("sfAccountTxnID");
    if tx.get_seq_proxy().is_ticket() && tx.is_field_present(account_txn_id_field) {
        return Ter::TEM_INVALID;
    }

    let tx_object: &protocol::STObject = tx;
    if view
        .rules()
        .enabled(&protocol::feature_id("fixCleanup3_2_0"))
        && protocol::has_invalid_amount(tx_object)
    {
        return Ter::TEM_BAD_AMOUNT;
    }

    if !tx.is_field_present(account_field) {
        return if is_tes_success(preclaim_result) {
            handle_real_dispatch(view, tx, txn_type, None)
        } else {
            preclaim_result
        };
    }

    // Change pseudo-transactions were dispatched above after their typed
    // preflight; all remaining transaction types use the regular preamble.

    let sequence_field = get_field_by_symbol("sfSequence");
    let balance_field = get_field_by_symbol("sfBalance");
    let sponsor_field = get_field_by_symbol("sfSponsor");
    let sponsor_flags_field = get_field_by_symbol("sfSponsorFlags");
    let sponsor_signature_field = get_field_by_symbol("sfSponsorSignature");
    let sponsor_fee_amount_field = get_field_by_symbol("sfFeeAmount");
    let sponsor_max_fee_field = get_field_by_symbol("sfMaxFee");
    let account = tx.get_account_id(account_field);
    let account_uint160 =
        Uint160::from_slice(account.data()).expect("account width should match Uint160");
    let account_key = account_keylet(account_uint160);

    let account_root = match view.peek(account_key) {
        Ok(Some(account_root)) => account_root,
        Ok(None) => return Ter::TER_NO_ACCOUNT,
        Err(_) => return Ter::TEF_BAD_LEDGER,
    };

    // Match Transactor::checkPriorTxAndLastLedger: all ordering and replay
    // guards run against the unmodified view, before fee or sequence handling.
    if tx.is_field_present(account_txn_id_field) {
        let prior = if account_root.is_field_present(account_txn_id_field) {
            account_root.get_field_h256(account_txn_id_field)
        } else {
            Uint256::zero()
        };
        if prior != tx.get_field_h256(account_txn_id_field) {
            return Ter::TEF_WRONG_PRIOR;
        }
    }
    let last_ledger_sequence_field = get_field_by_symbol("sfLastLedgerSequence");
    if tx.is_field_present(last_ledger_sequence_field)
        && view.seq() > tx.get_field_u32(last_ledger_sequence_field)
    {
        return Ter::TEF_MAX_LEDGER;
    }
    match view.tx_exists(tx.get_transaction_id()) {
        Ok(true) => return Ter::TEF_ALREADY,
        Ok(false) => {}
        Err(_) => return Ter::TEF_BAD_LEDGER,
    }

    // `OfferCreate::preclaim` is an immutable, pre-fee decision in rippled:
    // `applySteps.cpp::invokePreclaim` runs it before `Transactor::apply`
    // consumes a sequence or deducts a fee. Preserve a tec outcome through
    // the remainder of this shell so the standard fee-claim lifecycle still
    // runs, but never dispatch it into the mutating OfferCreate flow.
    let offer_preclaim = if txn_type == TxType::OFFER_CREATE {
        let preclaim = crate::state::offer_create::preclaim_offer_create(&*view, tx, flags);
        if !is_tes_success(preclaim) && !is_tec_claim(preclaim) {
            return preclaim;
        }
        preclaim
    } else {
        Ter::TES_SUCCESS
    };

    let oracle_preclaim = if txn_type == TxType::ORACLE_SET {
        run_oracle_set_preclaim_with_view(view, tx)
    } else {
        Ter::TES_SUCCESS
    };
    if !is_tes_success(oracle_preclaim) && !is_tec_claim(oracle_preclaim) {
        return oracle_preclaim;
    }

    // Match Transactor::checkSponsor/getFeePayer. Fee-sponsored transactions
    // prefer a prefunded Sponsorship entry; absent that entry, a valid sponsor
    // signature authorizes payment from the sponsor account above its reserve.
    // The transaction account still owns sequence/ticket consumption.
    let fee_sponsored = tx.is_field_present(sponsor_field)
        && tx.is_field_present(sponsor_flags_field)
        && ledger::is_fee_sponsored(tx.get_field_u32(sponsor_flags_field));
    let mut prefunded_sponsorship = None;
    let fee_payer = if tx.is_field_present(sponsor_field) {
        let sponsor = tx.get_account_id(sponsor_field);
        if sponsor == account {
            return Ter::TEM_MALFORMED;
        }
        if !tx.is_field_present(sponsor_flags_field) {
            return Ter::TEM_INVALID_FLAG;
        }
        let sponsor_flags = tx.get_field_u32(sponsor_flags_field);
        if sponsor_flags == 0 || (sponsor_flags & ledger::SPF_SPONSOR_FLAG_MASK) != 0 {
            return Ter::TEM_INVALID_FLAG;
        }
        if tx.is_field_present(get_field_by_symbol("sfDelegate"))
            && ledger::is_reserve_sponsored(sponsor_flags)
        {
            return Ter::TEM_INVALID;
        }
        match view.read(account_keylet(Uint160::from_void(sponsor.data()))) {
            Ok(Some(_)) => {}
            Ok(None) => return Ter::TER_NO_ACCOUNT,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        }

        let sponsorship_keylet = protocol::sponsorship_keylet(
            Uint160::from_void(sponsor.data()),
            Uint160::from_void(tx.get_initiator().data()),
        );
        let sponsorship = match view.read(sponsorship_keylet) {
            Ok(sponsorship) => sponsorship,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        if !tx.is_field_present(sponsor_signature_field) {
            let Some(sponsorship) = sponsorship.as_ref() else {
                return Ter::TER_NO_PERMISSION;
            };
            let sponsor_flags = sponsorship.get_field_u32(get_field_by_symbol("sfFlags"));
            if fee_sponsored
                && (sponsor_flags & protocol::LSF_SPONSORSHIP_REQUIRE_SIGN_FOR_FEE) != 0
            {
                return Ter::TER_NO_PERMISSION;
            }
            if tx.is_field_present(sponsor_flags_field)
                && ledger::is_reserve_sponsored(tx.get_field_u32(sponsor_flags_field))
                && (sponsor_flags & protocol::LSF_SPONSORSHIP_REQUIRE_SIGN_FOR_RESERVE) != 0
            {
                return Ter::TER_NO_PERMISSION;
            }
        }
        if fee_sponsored {
            if sponsorship.is_some() {
                prefunded_sponsorship = Some(sponsorship_keylet);
            }
        }
        tx.get_fee_payer_id()
    } else {
        tx.get_fee_payer_id()
    };

    let mut updated =
        STLedgerEntry::from_stobject(account_root.clone_as_object(), *account_root.key());
    let mut charged_fee_drops = if tx.is_field_present(fee_field) {
        tx.get_field_amount(fee_field).xrp().drops()
    } else {
        0
    };
    let mut fee_payment_result = Ter::TES_SUCCESS;
    let pre_fee_balance_drops = if updated.is_field_present(balance_field) {
        Some(updated.get_field_amount(balance_field).xrp().drops())
    } else {
        None
    };

    let consume_result = if tx.get_seq_proxy().is_seq() {
        updated.set_field_u32(sequence_field, tx.get_seq_proxy().value() + 1);
        Ter::TES_SUCCESS
    } else {
        delete_submit_ticket(view, account, &mut updated, tx.get_seq_proxy())
    };
    if !is_tes_success(consume_result) {
        return consume_result;
    }

    if fee_payer == account {
        if updated.is_field_present(balance_field) && tx.is_field_present(fee_field) {
            let balance_drops = updated.get_field_amount(balance_field).xrp().drops();
            let fee_drops = tx.get_field_amount(fee_field).xrp().drops();
            if balance_drops < fee_drops {
                // return tecINSUFF_FEE (claimed) — cap fee to actual balance, burn it,
                // consume sequence, discard all other state changes.
                // In an open ledger, return terINSUF_FEE_B (retry, no fee burned).
                // The build path is always a closed ledger.
                if balance_drops > 0 && !view.open() {
                    charged_fee_drops = balance_drops;
                    fee_payment_result = Ter::TEC_INSUFF_FEE;
                    updated.set_field_amount(
                        balance_field,
                        STAmount::from_xrp_amount(XRPAmount::from_drops(0)),
                    );
                } else {
                    return Ter::TER_INSUF_FEE_B;
                }
            } else {
                updated.set_field_amount(
                    balance_field,
                    STAmount::from_xrp_amount(XRPAmount::from_drops(balance_drops - fee_drops)),
                );
            }
        }
    } else if let Some(sponsorship_keylet) = prefunded_sponsorship {
        let sponsorship_sle = match view.peek(sponsorship_keylet) {
            Ok(Some(sle)) => sle,
            Ok(None) => return Ter::TEF_INTERNAL,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        let balance_drops = if sponsorship_sle.is_field_present(sponsor_fee_amount_field) {
            sponsorship_sle
                .get_field_amount(sponsor_fee_amount_field)
                .xrp()
                .drops()
        } else {
            0
        };
        let max_fee_drops = if sponsorship_sle.is_field_present(sponsor_max_fee_field) {
            sponsorship_sle
                .get_field_amount(sponsor_max_fee_field)
                .xrp()
                .drops()
        } else {
            i64::MAX
        };
        let fee_drops = tx.get_field_amount(fee_field).xrp().drops();
        let spendable = balance_drops.min(max_fee_drops);
        if spendable < fee_drops {
            if spendable <= 0 || view.open() {
                return Ter::TER_INSUF_FEE_B;
            }
            // Transactor::reset caps a closed-ledger fee claim to the
            // prefunded balance/MaxFee and still consumes the sequence.
            charged_fee_drops = spendable;
            fee_payment_result = Ter::TEC_INSUFF_FEE;
        }
        let mut updated_sponsorship =
            STLedgerEntry::from_stobject(sponsorship_sle.clone_as_object(), *sponsorship_sle.key());
        let remaining = balance_drops - charged_fee_drops;
        if remaining == 0 {
            updated_sponsorship.make_field_absent(sponsor_fee_amount_field);
        } else {
            updated_sponsorship.set_field_amount(
                sponsor_fee_amount_field,
                STAmount::from_xrp_amount(XRPAmount::from_drops(remaining)),
            );
        }
        if view.update(Arc::new(updated_sponsorship)).is_err() {
            return Ter::TEF_BAD_LEDGER;
        }
    } else {
        let fee_payer_uint160 =
            Uint160::from_slice(fee_payer.data()).expect("fee payer width should match Uint160");
        let fee_payer_sle = match view.peek(account_keylet(fee_payer_uint160)) {
            Ok(Some(sle)) => sle,
            Ok(None) => return Ter::TEF_INTERNAL,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        let balance_drops = fee_payer_sle.get_field_amount(balance_field).xrp().drops();
        let fee_drops = tx.get_field_amount(fee_field).xrp().drops();
        // A co-signed sponsor may not pay into its account reserve. Ordinary
        // delegates retain the standard account-fee behavior.
        let spendable = if fee_sponsored {
            let reserve =
                ledger::effective_account_reserve(view.fees(), &fee_payer_sle, 0, 0) as i64;
            (balance_drops - reserve).max(0)
        } else {
            balance_drops
        };
        if fee_sponsored && spendable < fee_drops {
            if spendable <= 0 || view.open() {
                return Ter::TER_INSUF_FEE_B;
            }
            charged_fee_drops = spendable;
            fee_payment_result = Ter::TEC_INSUFF_FEE;
        }
        let mut updated_fee_payer =
            STLedgerEntry::from_stobject(fee_payer_sle.clone_as_object(), *fee_payer_sle.key());
        updated_fee_payer.set_field_amount(
            balance_field,
            STAmount::from_xrp_amount(XRPAmount::from_drops(balance_drops - charged_fee_drops)),
        );
        if view.update(Arc::new(updated_fee_payer)).is_err() {
            return Ter::TEF_BAD_LEDGER;
        }
    }

    if view.update(Arc::new(updated)).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }
    if tx.is_field_present(fee_field) {
        if charged_fee_drops > 0 {
            if view
                .destroy_xrp(XRPAmount::from_drops(charged_fee_drops))
                .is_err()
            {
                return Ter::TEF_BAD_LEDGER;
            }
        }
    }
    {
        // that failed to fully cross), discard all transactor state changes but keep the
        // fee deduction and sequence consumption that were already applied above.
        // We achieve this by running handle_real_dispatch in a nested FlowSandbox and
        // only applying it to the outer view when the result is NOT tecKILLED.
        let invariant_prefix = match crate::state::invariants::InvariantDeltaPrefix::capture(view) {
            Ok(prefix) => prefix,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        let preamble_item_keys = view.items().keys().copied().collect::<BTreeSet<_>>();
        let mut inner = ledger::FlowSandbox::new(view);
        // Transactor::apply updates sfAccountTxnID before doApply so the
        // handler can observe it, but Transactor::reset discards that update
        // and reapplies only the fee plus sequence/ticket. Keep the prior-tx
        // chain in the success-only child sandbox rather than the persistent
        // fee preamble, so every ordinary/persistent/invariant tec matches the
        // canonical reset state.
        if account_root.is_field_present(account_txn_id_field) {
            let account_after_preamble = match inner.peek(account_key) {
                Ok(Some(account)) => account,
                Ok(None) => return Ter::TEF_INTERNAL,
                Err(_) => return Ter::TEF_BAD_LEDGER,
            };
            let mut account_after_preamble = STLedgerEntry::from_stobject(
                account_after_preamble.clone_as_object(),
                *account_after_preamble.key(),
            );
            account_after_preamble.set_field_h256(account_txn_id_field, tx.get_transaction_id());
            if inner.update(Arc::new(account_after_preamble)).is_err() {
                return Ter::TEF_BAD_LEDGER;
            }
        }
        let mut result = if is_tec_claim(fee_payment_result) {
            fee_payment_result
        } else if is_tec_claim(preclaim_result) {
            preclaim_result
        } else if is_tec_claim(offer_preclaim) {
            offer_preclaim
        } else if is_tes_success(oracle_preclaim) {
            handle_real_dispatch(&mut inner, tx, txn_type, pre_fee_balance_drops)
        } else {
            oracle_preclaim
        };

        // tef* and tem* failures should NOT consume sequence or fee.
        // Revert the account root to its pre-apply state so the transaction
        // is as if it was never applied.
        if is_tef_failure(result) || is_tem_malformed(result) {
            return if view.update(account_root.clone()).is_err() {
                Ter::TEF_BAD_LEDGER
            } else {
                result
            };
        }

        // Rippld computes oversize before invariant evaluation; invariant
        // failure must retain precedence rather than being overwritten later.
        // Protocol.h::kOversizeMetaDataCap is a count of entries in the
        // transaction ApplyStateTable, not a byte limit.  This boundary is
        // consensus-critical because crossing it changes the result to
        // tecOVERSIZE and preserves only the permitted cleanup deletions.
        let transaction_item_count = preamble_item_keys
            .iter()
            .copied()
            .chain(inner.items().keys().copied())
            .collect::<BTreeSet<_>>()
            .len();
        if exceeds_oversize_metadata_cap(transaction_item_count) {
            result = Ter::TEC_OVERSIZE;
        }

        let fee_amt = protocol::XRPAmount::from_drops(charged_fee_drops);

        // rippled checks an ordinary tec only after resetting the handler
        // context to fee/sequence state. At this point `inner` still contains
        // partial doApply mutations, so only successful state is eligible for
        // invariant evaluation here.
        if protocol::is_tes_success(result) {
            result = crate::state::invariants::check_invariants_for_tx_with_prefix(
                &inner,
                tx,
                result,
                fee_amt,
                Some(-fee_amt.drops()),
                Some(&invariant_prefix),
            );
            *invariant_fee_reset = result == Ter::TEC_INVARIANT_FAILED;
        }

        let fail_hard_tec =
            is_tec_claim(result) && protocol::any_apply_flags(flags & ApplyFlags::FAIL_HARD);
        let do_offers =
            !fail_hard_tec && (result == Ter::TEC_OVERSIZE || result == Ter::TEC_KILLED);
        let do_lines_or_mpts = !fail_hard_tec && result == Ter::TEC_INCOMPLETE;
        let do_nf_token_offers = !fail_hard_tec && result == Ter::TEC_EXPIRED;
        let do_credentials = !fail_hard_tec && result == Ter::TEC_EXPIRED;

        if result == Ter::TEC_INVARIANT_FAILED {
            // `inner` is the doApply portion of this transaction context. Its
            // drop is equivalent to Transactor::reset's discard because the
            // outer FlowSandbox contains only the already-replayed fee and
            // sequence/ticket changes. Recheck that real fee-claim context:
            // a repeated failure maps to tefINVARIANT_FAILED in the checker.
            drop(inner);
            result = crate::state::invariants::check_invariants_for_tx_with_expected_xrp_delta(
                view,
                tx,
                result,
                fee_amt,
                Some(-fee_amt.drops()),
            );
        } else if !do_offers && !do_lines_or_mpts && !do_nf_token_offers && !do_credentials {
            if is_tes_success(result) {
                // Only a successful doApply commits its handler sandbox.
                // rippled resets every ordinary tec result to fee/sequence
                // changes; those changes already live in the outer view.
                if inner.apply().is_err() {
                    result = Ter::TEF_INTERNAL;
                }
            } else {
                // Discard all partial handler mutations for ordinary tec
                // outcomes. In particular, a second owner-directory insert
                // may fail after the first insert and owner-count adjustment.
                drop(inner);
                if likely_to_claim_fee(result, flags)
                    && !protocol::any_apply_flags(flags & ApplyFlags::FAIL_HARD)
                {
                    result =
                        crate::state::invariants::check_invariants_for_tx_with_expected_xrp_delta(
                            view,
                            tx,
                            result,
                            fee_amt,
                            Some(-fee_amt.drops()),
                        );
                }
            }
        } else {
            // Cleanup path
            let mut removed_offers = Vec::new();
            let mut removed_trust_lines = Vec::new();
            let mut expired_nft_offers = Vec::new();
            let mut expired_credentials = Vec::new();

            // rippled applies `sbCancel`, not the main `sb`, when OfferCreate
            // returns `tecKILLED`. An explicit sfOfferSequence deletion lives
            // in the main sandbox, so it must be discarded with the failed
            // replacement. Keep filtering only that key; flow-discovered
            // unfunded offers remain eligible for canonical cleanup.
            let preserved_offer_sequence_cancel = (result == Ter::TEC_KILLED
                && txn_type == TxType::OFFER_CREATE
                && tx.is_field_present(get_field_by_symbol("sfOfferSequence")))
            .then(|| {
                protocol::offer_keylet(
                    Uint160::from_void(tx.get_account_id(account_field).data()),
                    tx.get_field_u32(get_field_by_symbol("sfOfferSequence")),
                )
                .key
            });

            let erased_entries: Vec<(basics::base_uint::Uint256, Arc<protocol::STLedgerEntry>)> =
                inner
                    .items()
                    .iter()
                    .filter(|(_, entry)| entry.action == ledger::flow_sandbox::Action::Erase)
                    .map(|(k, entry)| (*k, entry.sle.clone()))
                    .collect();

            drop(inner); // discard transactor state changes
            let mut cleanup = ledger::FlowSandbox::new(view);
            let mut cleanup_read_failed = false;

            for (index, after) in erased_entries {
                match cleanup.peek(protocol::Keylet::new(after.get_type(), index)) {
                    Ok(Some(before)) => {
                        if do_offers
                            && Some(index) != preserved_offer_sequence_cancel
                            && before.get_type() == protocol::LedgerEntryType::Offer
                        {
                            let taker_pays = protocol::get_field_by_symbol("sfTakerPays");
                            if before.get_field_amount(taker_pays)
                                == after.get_field_amount(taker_pays)
                            {
                                removed_offers.push(index);
                            }
                        }
                        if do_lines_or_mpts
                            && before.get_type() == protocol::LedgerEntryType::RippleState
                        {
                            // Pinned Transactor::typesForResult(tecINCOMPLETE)
                            // preserves only ltRIPPLE_STATE deletions. MPToken
                            // deletions are ordinary doApply state and must reset.
                            removed_trust_lines.push(index);
                        }
                        if do_nf_token_offers
                            && before.get_type() == protocol::LedgerEntryType::NFTokenOffer
                        {
                            expired_nft_offers.push(index);
                        }
                        if do_credentials
                            && before.get_type() == protocol::LedgerEntryType::Credential
                        {
                            expired_credentials.push(index);
                        }
                    }
                    Ok(None) => {}
                    Err(_) => {
                        cleanup_read_failed = true;
                        break;
                    }
                }
            }

            if !cleanup_read_failed && do_offers && !removed_offers.is_empty() {
                let mut count = 0;
                for index in removed_offers {
                    let sle = match cleanup.peek(protocol::Keylet::new(
                        protocol::LedgerEntryType::Offer,
                        index,
                    )) {
                        Ok(Some(sle)) => sle,
                        Ok(None) => continue,
                        Err(_) => {
                            cleanup_read_failed = true;
                            break;
                        }
                    };
                    let account = sle.get_account_id(protocol::get_field_by_symbol("sfAccount"));
                    // C++ ApplyView mutation cannot fail at this boundary and
                    // therefore ignores the semantic helper TER. A Rust
                    // storage failure is represented as a hard TER and must
                    // discard the entire cleanup sandbox, never commit a
                    // partially removed offer.
                    let cleanup_ter =
                        crate::state::offer_create::offer_delete_pub(&mut cleanup, &account, sle);
                    if is_tef_failure(cleanup_ter) || cleanup_ter == Ter::TEC_INTERNAL {
                        cleanup_read_failed = true;
                        break;
                    }
                    count += 1;
                    if count == protocol::UNFUNDED_OFFER_REMOVE_LIMIT {
                        break;
                    }
                }
            }

            if !cleanup_read_failed && result == Ter::TEC_EXPIRED && !expired_nft_offers.is_empty()
            {
                let mut count = 0;
                for index in expired_nft_offers {
                    let offer = match cleanup.peek(protocol::keylet::nft_offer_keylet(index)) {
                        Ok(Some(offer)) => offer,
                        Ok(None) => continue,
                        Err(_) => {
                            cleanup_read_failed = true;
                            break;
                        }
                    };
                    // Pinned Transactor::removeExpiredNFTokenOffers delegates
                    // the complete two-directory/owner-count/erase sequence to
                    // nft::deleteTokenOffer and deliberately ignores only its
                    // `false` return. Keep the same helper and mutation order;
                    // a Rust view error is a hard bad-ledger condition, not a
                    // missing offer.
                    if ledger::nftoken_helpers::delete_token_offer(&mut cleanup, offer).is_err() {
                        cleanup_read_failed = true;
                        break;
                    }
                    count += 1;
                    if count == protocol::EXPIRED_OFFER_REMOVE_LIMIT {
                        break;
                    }
                }
            }

            if !cleanup_read_failed && result == Ter::TEC_INCOMPLETE {
                if !removed_trust_lines.is_empty()
                    && removed_trust_lines.len()
                        <= usize::from(protocol::MAX_DELETABLE_AMM_TRUST_LINES)
                {
                    for index in removed_trust_lines {
                        let sle = match cleanup.peek(protocol::Keylet::new(
                            protocol::LedgerEntryType::RippleState,
                            index,
                        )) {
                            Ok(Some(sle)) => sle,
                            Ok(None) => continue,
                            Err(_) => {
                                cleanup_read_failed = true;
                                break;
                            }
                        };
                        let low = sle
                            .get_field_amount(protocol::get_field_by_symbol("sfLowLimit"))
                            .issue()
                            .account;
                        let high = sle
                            .get_field_amount(protocol::get_field_by_symbol("sfHighLimit"))
                            .issue()
                            .account;
                        // Preserve pinned logging/continuation for semantic
                        // non-tes results, but fail the atomic cleanup on the
                        // Rust storage/impossible-state hard boundary.
                        let cleanup_ter =
                            crate::state::trust_set::trust_delete(&mut cleanup, &sle, &low, &high);
                        if is_tef_failure(cleanup_ter) || cleanup_ter == Ter::TEC_INTERNAL {
                            cleanup_read_failed = true;
                            break;
                        }
                    }
                }
            }

            if !cleanup_read_failed && result == Ter::TEC_EXPIRED && !expired_credentials.is_empty()
            {
                for index in expired_credentials {
                    let sle = match cleanup.peek(protocol::Keylet::new(
                        protocol::LedgerEntryType::Credential,
                        index,
                    )) {
                        Ok(Some(sle)) => sle,
                        Ok(None) => continue,
                        Err(_) => {
                            cleanup_read_failed = true;
                            break;
                        }
                    };
                    match ledger::credential_helpers::delete_sle(&mut cleanup, sle) {
                        Ok(ter) if protocol::is_tes_success(ter) => {}
                        Ok(ter) => {
                            tracing::error!(
                                target: "tx",
                                ?ter,
                                credential = %index,
                                "persistent expired-credential cleanup failed"
                            );
                        }
                        Err(_) => {
                            cleanup_read_failed = true;
                            break;
                        }
                    }
                }
            }

            if cleanup_read_failed {
                result = Ter::TEF_BAD_LEDGER;
            } else if is_tec_claim(result) {
                result = crate::state::invariants::check_invariants_for_tx_with_prefix(
                    &cleanup,
                    tx,
                    result,
                    fee_amt,
                    Some(-fee_amt.drops()),
                    Some(&invariant_prefix),
                );
                *invariant_fee_reset = result == Ter::TEC_INVARIANT_FAILED;
            }
            if result == Ter::TEC_INVARIANT_FAILED {
                drop(cleanup);
                result = crate::state::invariants::check_invariants_for_tx_with_expected_xrp_delta(
                    view,
                    tx,
                    result,
                    fee_amt,
                    Some(-fee_amt.drops()),
                );
            } else if is_tec_claim(result) && cleanup.apply().is_err() {
                result = Ter::TEF_INTERNAL;
            }
        }
        result
    }
}

#[inline]
fn exceeds_oversize_metadata_cap(item_count: usize) -> bool {
    item_count > protocol::OVERSIZE_METADATA_CAP
}

/// Implements `rippled/src/libxrpl/tx/apply.cpp::applyBatchTransactions`.
/// Each inner transaction must use the same semantic preflight and immutable
/// preclaim admission path as a standalone transaction, but with the parent
/// batch ID and TapBatch context carried through both phases.
fn apply_submit_batch_followup<V: ledger::ApplyView + ?Sized>(
    view: &mut V,
    batch_tx: &STTx,
    destination: BatchApplyDestination,
    node_network_id: u32,
) -> BatchFollowupOutcome {
    let batch_mode = BatchTransactionFlags::from_bits(batch_tx.get_flags());
    let parent_batch_id = batch_tx.get_transaction_id();
    let mut whole_batch = ledger::FlowSandbox::new(view);
    let mut applied_inner_transactions = Vec::new();

    let inner_transactions = match tx::canonical_batch_inner_transactions(batch_tx) {
        Ok(inner_transactions) => inner_transactions,
        Err(error) => {
            return BatchFollowupOutcome {
                result: error,
                applied_inner_transactions,
            };
        }
    };

    for inner_tx in inner_transactions {
        let whole_batch_view: &mut dyn ledger::ApplyView = &mut whole_batch;
        // This is rippled's `OpenView(kBatchView, batchView)` followed by
        // `apply(..., parentBatchId, tx, TapBatch, ...)`, not a dry-run or a
        // direct transactor dispatch substitute.
        let inner_flags = if destination == BatchApplyDestination::DryRun {
            ApplyFlags::BATCH | ApplyFlags::DRY_RUN
        } else {
            ApplyFlags::BATCH
        };
        let mut per_tx_batch_view =
            ledger::FlowSandbox::new_with_flags(whole_batch_view, inner_flags);
        let rules = per_tx_batch_view.rules();
        let preflight = transaction_preflight_ter_with_parent_batch_id(
            &inner_tx,
            &rules,
            Some(parent_batch_id),
            inner_flags,
            node_network_id,
        );
        let preclaim = if is_tes_success(preflight) {
            queue_apply_preclaim_ter_with_parent_batch_id(
                &per_tx_batch_view,
                &inner_tx,
                per_tx_batch_view.seq(),
                inner_flags,
                Some(parent_batch_id),
            )
        } else {
            preflight
        };
        let result = if is_tes_success(preclaim) || is_tec_claim(preclaim) {
            // `apply.cpp::applyBatchTransactions` invokes the normal
            // per-transaction lifecycle. Contain a malformed inner handler
            // at that boundary so a panic cannot unwind and partially expose
            // the whole Batch view.
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let delivered_amount_capture = matches!(
                    inner_tx.get_txn_type(),
                    TxType::PAYMENT | TxType::CHECK_CASH | TxType::ACCOUNT_DELETE
                )
                .then(crate::state::payment::DeliveredAmountCapture::new);
                let mut invariant_fee_reset = false;
                let result = apply_submit_transactor_shell_impl(
                    &mut per_tx_batch_view,
                    &inner_tx,
                    inner_tx.get_txn_type(),
                    inner_flags,
                    preclaim,
                    &mut invariant_fee_reset,
                    node_network_id,
                );
                let delivered_amount = delivered_amount_capture
                    .and_then(crate::state::payment::DeliveredAmountCapture::finish)
                    .filter(|_| is_tes_success(result));
                (result, delivered_amount)
            })) {
                Ok(result) => result,
                Err(_) => {
                    tracing::error!(
                        target: "tx",
                        parent_batch_id = %parent_batch_id,
                        inner_tx_id = %inner_tx.get_transaction_id(),
                        "inner Batch transaction panicked; mapped to tefEXCEPTION"
                    );
                    (Ter::TEF_EXCEPTION, None)
                }
            }
        } else {
            (preclaim, None)
        };
        let (result, delivered_amount) = result;
        let inner_applied = is_tes_success(result) || is_tec_claim(result);

        if inner_applied {
            let inner_tx_id = inner_tx.get_transaction_id();
            let inner_ledger_seq = per_tx_batch_view.seq();
            let metadata = if destination.builds_metadata() {
                per_tx_batch_view
                    .to_tx_meta(
                        inner_tx_id,
                        inner_ledger_seq,
                        delivered_amount.clone(),
                        &rules,
                    )
                    .map(|mut metadata| {
                        metadata.set_parent_batch_id(Some(parent_batch_id));
                        metadata
                    })
            } else {
                Ok(protocol::TxMeta::new(inner_tx_id, inner_ledger_seq))
            };
            let metadata = match metadata {
                Ok(metadata) => metadata,
                Err(_) => {
                    return BatchFollowupOutcome {
                        result: Ter::TEF_INTERNAL,
                        applied_inner_transactions: Vec::new(),
                    };
                }
            };
            let committed = if destination == BatchApplyDestination::Closed {
                per_tx_batch_view.apply_with_tx_meta(
                    inner_tx_id,
                    inner_ledger_seq,
                    delivered_amount,
                    Some(parent_batch_id),
                    &rules,
                )
            } else {
                per_tx_batch_view.apply().map(|()| metadata.clone())
            };
            if committed.is_err() {
                return BatchFollowupOutcome {
                    result: Ter::TEF_INTERNAL,
                    applied_inner_transactions: Vec::new(),
                };
            }
            applied_inner_transactions.push(AppliedBatchInnerTransaction {
                transaction: inner_tx,
                result,
                metadata,
            });
        }

        if !is_tes_success(result) {
            if batch_mode.contains(BatchTransactionFlags::ALL_OR_NOTHING) {
                // Do not expose any individually-applied result: dropping the
                // whole-batch view atomically discards every inner mutation.
                return BatchFollowupOutcome {
                    result: Ter::TES_SUCCESS,
                    applied_inner_transactions: Vec::new(),
                };
            }

            if batch_mode.contains(BatchTransactionFlags::UNTIL_FAILURE) {
                break;
            }
        } else if batch_mode.contains(BatchTransactionFlags::ONLY_ONE) {
            break;
        }
    }

    if !applied_inner_transactions.is_empty() && whole_batch.apply().is_err() {
        return BatchFollowupOutcome {
            result: Ter::TEF_INTERNAL,
            applied_inner_transactions: Vec::new(),
        };
    }

    BatchFollowupOutcome {
        result: Ter::TES_SUCCESS,
        applied_inner_transactions,
    }
}

/// Serializes every applied inner transaction only after its whole-batch view
/// is committed. This is the `TxMeta::setParentBatchID(parentBatchId)` effect
/// from rippled's `ApplyStateTable::apply` for each independently applied inner.
fn stage_accepted_batch_inner_transactions(
    accepted_entries: &mut Vec<StandaloneAcceptedTx>,
    inner_transactions: Vec<AppliedBatchInnerTransaction>,
    closed_seq: u32,
) {
    for inner in inner_transactions {
        let index = accepted_entries.len() as u32;
        let transaction_id = inner.transaction.get_transaction_id();
        let mut meta = inner.metadata;
        debug_assert_eq!(meta.get_lgr_seq(), closed_seq);
        let delta_meta_nodes = meta.get_nodes().json(protocol::JsonOptions::NONE);
        let mut serializer = protocol::Serializer::default();
        meta.add_raw(&mut serializer, inner.result, index);

        accepted_entries.push(StandaloneAcceptedTx {
            transaction_id,
            txn: Arc::new(protocol::Serializer::from_bytes(
                inner.transaction.get_serializer().data(),
            )),
            metadata: Arc::new(serializer),
            delta_meta_nodes,
        });
    }
}

fn canonical_sttx_consequences(sttx: &STTx) -> TxConsequences {
    let fee = sttx
        .is_field_present(get_field_by_symbol("sfFee"))
        .then(|| {
            sttx.get_field_amount(get_field_by_symbol("sfFee"))
                .xrp()
                .drops()
                .max(0) as u64
        })
        .unwrap_or(0);
    // TxConsequences(STTx const&) uses getSeqProxy(), preserving tickets.
    // Treating a ticket as Sequence(0) corrupts TxQ replacement, account
    // window, and blocker admission semantics.
    let seq = sttx.get_seq_proxy();
    let native_spend = |field: &'static protocol::SField| {
        if !sttx.is_field_present(field) {
            return 0;
        }
        let amount = sttx.get_field_amount(field);
        if amount.native() && amount.signum() > 0 {
            amount.xrp().drops() as u64
        } else {
            0
        }
    };

    match sttx.get_txn_type() {
        TxType::ACCOUNT_SET => tx::run_account_set_make_tx_consequences(
            fee,
            seq,
            sttx.get_flags(),
            sttx.get_field_u32(get_field_by_symbol("sfSetFlag")),
            sttx.get_field_u32(get_field_by_symbol("sfClearFlag")),
        ),
        TxType::REGULAR_KEY_SET | TxType::ACCOUNT_DELETE | TxType::SIGNER_LIST_SET => {
            TxConsequences::with_category(fee, seq, tx::TxConsequencesCategory::Blocker)
        }
        TxType::XCHAIN_CLAIM
        | TxType::XCHAIN_ADD_CLAIM_ATTESTATION
        | TxType::XCHAIN_ADD_ACCOUNT_CREATE_ATTESTATION => {
            TxConsequences::with_category(fee, seq, tx::TxConsequencesCategory::Blocker)
        }
        TxType::PAYMENT => tx::run_payment_make_tx_consequences(
            fee,
            seq,
            sttx.is_field_present(get_field_by_symbol("sfSendMax"))
                .then(|| native_spend(get_field_by_symbol("sfSendMax"))),
            Some(native_spend(get_field_by_symbol("sfAmount"))),
        ),
        TxType::OFFER_CREATE => TxConsequences::with_potential_spend(
            fee,
            seq,
            native_spend(get_field_by_symbol("sfTakerGets")),
        ),
        TxType::ESCROW_CREATE => {
            let amount = sttx.get_field_amount(get_field_by_symbol("sfAmount"));
            let kind = if amount.native() {
                tx::EscrowCreateAmountKind::Xrp
            } else if amount.holds_mpt_issue() {
                tx::EscrowCreateAmountKind::Mpt
            } else {
                tx::EscrowCreateAmountKind::Issue
            };
            tx::run_escrow_create_make_tx_consequences(
                fee,
                seq,
                kind,
                native_spend(get_field_by_symbol("sfAmount")),
            )
        }
        TxType::PAYCHAN_CREATE => tx::run_payment_channel_create_make_tx_consequences(
            fee,
            seq,
            native_spend(get_field_by_symbol("sfAmount")),
        ),
        TxType::PAYCHAN_FUND => tx::run_payment_channel_fund_make_tx_consequences(
            fee,
            seq,
            native_spend(get_field_by_symbol("sfAmount")),
        ),
        TxType::TICKET_CREATE => tx::run_ticket_create_make_tx_consequences(
            fee,
            seq,
            sttx.get_field_u32(get_field_by_symbol("sfTicketCount")),
        ),
        TxType::XCHAIN_COMMIT => TxConsequences::with_potential_spend(
            fee,
            seq,
            native_spend(get_field_by_symbol("sfAmount")),
        ),
        TxType::SPONSORSHIP_SET => TxConsequences::with_potential_spend(
            fee,
            seq,
            native_spend(get_field_by_symbol("sfFeeAmountDelta")),
        ),
        _ => TxConsequences::new(fee, seq),
    }
}

#[cfg(test)]
mod canonical_consequences_tests {
    use super::canonical_sttx_consequences;
    use protocol::{AccountID, STAmount, STTx, SeqProxy, TxType, get_field_by_symbol};

    fn tx(txn_type: TxType, sequence: u32) -> STTx {
        STTx::new(txn_type, |tx| {
            tx.set_account_id(
                get_field_by_symbol("sfAccount"),
                AccountID::from_array([0x11; 20]),
            );
            tx.set_field_u32(get_field_by_symbol("sfSequence"), sequence);
            tx.set_field_amount(
                get_field_by_symbol("sfFee"),
                STAmount::new_native(10, false),
            );
        })
    }

    #[test]
    fn ticket_proxy_and_ticket_create_sequence_span_match_rippled() {
        let mut ordinary = tx(TxType::PAYMENT, 0);
        ordinary.set_field_u32(get_field_by_symbol("sfTicketSequence"), 77);
        let ordinary = canonical_sttx_consequences(&ordinary);
        assert_eq!(ordinary.seq_proxy(), SeqProxy::ticket(77));
        assert_eq!(ordinary.sequences_consumed(), 0);

        let mut create = tx(TxType::TICKET_CREATE, 9);
        create.set_field_u32(get_field_by_symbol("sfTicketCount"), 4);
        let create = canonical_sttx_consequences(&create);
        assert_eq!(create.seq_proxy(), SeqProxy::sequence(9));
        assert_eq!(create.sequences_consumed(), 4);
    }

    #[test]
    fn blockers_and_custom_xrp_spend_match_pinned_factories() {
        for txn_type in [
            TxType::REGULAR_KEY_SET,
            TxType::ACCOUNT_DELETE,
            TxType::SIGNER_LIST_SET,
            TxType::XCHAIN_CLAIM,
            TxType::XCHAIN_ADD_CLAIM_ATTESTATION,
            TxType::XCHAIN_ADD_ACCOUNT_CREATE_ATTESTATION,
        ] {
            assert!(canonical_sttx_consequences(&tx(txn_type, 1)).is_blocker());
        }

        let mut payment = tx(TxType::PAYMENT, 1);
        payment.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::new_native(25, false),
        );
        payment.set_field_amount(
            get_field_by_symbol("sfSendMax"),
            STAmount::new_native(40, false),
        );
        assert_eq!(canonical_sttx_consequences(&payment).potential_spend(), 40);

        let mut offer = tx(TxType::OFFER_CREATE, 1);
        offer.set_field_amount(
            get_field_by_symbol("sfTakerGets"),
            STAmount::new_native(55, false),
        );
        assert_eq!(canonical_sttx_consequences(&offer).potential_spend(), 55);
    }
}

impl
    AcceptLedgerPendingApplyRuntime<
        AppPlaceholder,
        Option<Arc<Ledger>>,
        Option<Arc<Ledger>>,
        AcceptLedgerPendingTransaction,
        Arc<crate::state::app_registry::AppJournal>,
        AppPlaceholder,
    > for AcceptLedgerPendingRuntime
{
    type Fee = u64;
    type PreflightError = ();
    type PreclaimError = ();
    type ApplyError = ();

    fn dispatch_preflight(
        &mut self,
        ctx: &tx::PreflightContext<
            AppPlaceholder,
            AcceptLedgerPendingTransaction,
            Arc<crate::state::app_registry::AppJournal>,
            AppPlaceholder,
        >,
        _txn_type: TxType,
    ) -> Result<(NotTec, TxConsequences), Self::PreflightError> {
        let sttx = Self::read_sttx(&ctx.tx);
        let consequences = canonical_sttx_consequences(sttx.as_ref());
        let result = transaction_preflight_ter(sttx.as_ref(), &ctx.rules);

        Ok((
            result,
            if is_tes_success(result) {
                consequences
            } else {
                TxConsequences::from_preflight_result(result)
            },
        ))
    }

    fn fallback_consequences(
        &mut self,
        ctx: &tx::PreflightContext<
            AppPlaceholder,
            AcceptLedgerPendingTransaction,
            Arc<crate::state::app_registry::AppJournal>,
            AppPlaceholder,
        >,
    ) -> TxConsequences {
        let sttx = Self::read_sttx(&ctx.tx);
        canonical_sttx_consequences(sttx.as_ref())
    }

    fn dispatch_preclaim(
        &mut self,
        ctx: &tx::PreclaimContext<
            AppPlaceholder,
            Option<Arc<Ledger>>,
            AcceptLedgerPendingTransaction,
            Arc<crate::state::app_registry::AppJournal>,
            AppPlaceholder,
        >,
        _txn_type: TxType,
    ) -> Result<Ter, Self::PreclaimError> {
        let Some(view) = ctx.view.as_ref() else {
            return Ok(Ter::TER_NO_ACCOUNT);
        };
        let sttx = Self::read_sttx(&ctx.tx);
        Ok(queue_apply_preclaim_ter(
            view.as_ref(),
            sttx.as_ref(),
            view.header().seq,
            ctx.flags,
        ))
    }

    fn calculate_base_fee(
        &mut self,
        base: &Option<Arc<Ledger>>,
        tx: &AcceptLedgerPendingTransaction,
        _txn_type: TxType,
    ) -> Self::Fee {
        let Some(ledger) = base.as_ref() else {
            return 0;
        };
        let sttx = Self::read_sttx(tx);
        let calculated = calculate_sttx_base_fee_for_metrics(ledger.as_ref(), sttx.as_ref());
        if calculated == INVALID_BATCH_BASE_FEE {
            ledger.fees().base
        } else {
            calculated
        }
    }

    fn zero_fee(&mut self) -> Self::Fee {
        0
    }

    fn dispatch_apply(
        &mut self,
        ctx: &mut tx::ApplyContext<
            AppPlaceholder,
            Option<Arc<Ledger>>,
            Option<Arc<Ledger>>,
            AcceptLedgerPendingTransaction,
            Self::Fee,
            Arc<crate::state::app_registry::AppJournal>,
            AppPlaceholder,
        >,
        txn_type: TxType,
    ) -> Result<ApplyResult, Self::ApplyError> {
        if Self::is_system_transaction(txn_type) {
            return Ok(ApplyResult::new(Ter::TES_SUCCESS, true, false));
        }

        let result = ctx.preclaim_result;
        Ok(ApplyResult::new(
            result,
            is_tes_success(result) || is_tec_claim(result),
            false,
        ))
    }
}

impl LedgerAcceptor for ConsensusLedgerAcceptor {
    fn spawn_consensus_accept_job(&self, job: Box<dyn FnOnce() + Send + 'static>) {
        // Matches rippled's app_.getJobQueue().addJob(JtAccept, "AcceptLedger", ...)
        // in RCLConsensus::Adaptor::onAccept: run the heavy do_accept +
        // end_consensus work on a JobQueue worker thread, off the consensus
        // timer thread, so peer proposal draining stays responsive under
        // load. The JobQueue's persistent worker-thread pool (spawned at
        // startup via run_worker_loop, matching reference JobQueue's
        // permanent worker threads) services this automatically — no manual
        // dispatch pump needed here.
        let mut job_slot = Some(job);
        if !self.job_queue.add_job(
            crate::job::job_types::JobType::JtAccept,
            "AcceptLedger",
            move || {
                if let Some(job) = job_slot.take() {
                    job();
                }
            },
        ) {
            // JobQueue is stopping (shutdown in progress) — run inline as a
            // last resort so consensus state isn't silently dropped.
            tracing::warn!(target: "consensus", "accept job queue is stopping; running on_accept inline");
        }
    }

    fn accept_ledger(
        &self,
        closed_seq: u32,
        close_time: u32,
        close_resolution: u8,
        correct_close_time: bool,
        base_fee_drops: u64,
        txns: Vec<Arc<protocol::STTx>>,
        validation: Option<PendingValidation>,
    ) -> Result<u32, String> {
        let root = self.root.clone();
        let name = format!("AcceptLedger#{closed_seq}");

        if !self
            .job_queue
            .add_job(crate::job::job_types::JobType::JtAccept, name, move || {
                match root.accept_ledger_with_txns(closed_seq, close_time, close_resolution, correct_close_time, base_fee_drops, txns) {
                    Ok(_) => {
                        // Matches the reference's `RCLConsensus::Adaptor::doAccept`
                        // calling `notify(neACCEPTED_LEDGER, built, haveCorrectLCL)`
                        // unconditionally after every successful accept -- not just
                        // at genesis. Broadcasting this on every round (rather than
                        // only once, as the previous implementation did) is what
                        // lets a node that started a round late learn its peers
                        // have already closed the next one, so its own
                        // `shouldCloseLedger` fast-close path
                        // (`proposersClosed + proposersValidated > prevProposers/2`)
                        // can fire instead of always waiting out the full idle
                        // interval and staying permanently offset by its startup
                        // delay.
                        //
                        // `root.closed_ledger()` is read exactly ONCE here and
                        // reused for BOTH the StatusChange broadcast and the
                        // validation signing below. This is deliberate: this
                        // whole match arm runs synchronously, immediately
                        // after `root.accept_ledger(...)` (the call that
                        // performs `on_closed_ledger`) returns -- so this is
                        // the first point at which the real, just-built
                        // ledger's hash is guaranteed to be visible. Signing
                        // a validation from a DIFFERENT read (e.g. back in
                        // `on_accept`'s caller, before this job even runs)
                        // would race the async `ConsensusLedgerAcceptor::
                        // accept_ledger` wrapper below returning immediately
                        // without waiting for this job -- producing a
                        // validation whose `sfLedgerHash` doesn't match its
                        // claimed `sfLedgerSequence` (this was a real,
                        // previously-shipped bug: the trust trie ended up
                        // with `(seq=2, id=<genesis hash>)`, corrupting
                        // `Validations::getPreferred` and causing
                        // `Consensus::checkLedger` to reset back to genesis
                        // every round).
                        if let Some(closed) = root.closed_ledger() {
                            let hdr = closed.header();
                            root.broadcast_consensus_status_change(
                                closed.as_ref(),
                                2, // neACCEPTED_LEDGER
                                true,
                            );

                            if let Some(pending) = validation {
                                let ledger_hash = *hdr.hash.as_uint256();
                                let validation_time = close_time.max(1);
                                match protocol::STValidation::new_signed(validation_time, &pending.public_key, pending.node_id, &pending.secret_key, |v| {
                                    v.set_field_h256(protocol::get_field_by_symbol("sfLedgerHash"), ledger_hash);
                                    v.set_field_h256(protocol::get_field_by_symbol("sfConsensusHash"), pending.consensus_hash);
                                    v.set_field_u32(protocol::get_field_by_symbol("sfLedgerSequence"), closed_seq);
                                    if pending.proposing {
                                        v.set_flag(protocol::VF_FULL_VALIDATION);
                                    }
                                }) {
                                    Ok(built_validation) => root.clone_ledger_acceptor().publish_validation(Arc::new(built_validation)),
                                    Err(err) => {
                                        tracing::error!(target: "consensus", closed_seq, ?err, "on_accept: validation signing failed");
                                    }
                                }
                            }
                        }
                        // Preferred-LCL policy and the next-round handoff
                        // are exclusively owned by NetworkOpsStrand. This
                        // legacy acceptor remains a publication/validation
                        // service and only wakes that serialized owner.
                        root.notify_consensus_event();
                    }
                    Err(err) => {
                        tracing::error!(target: "consensus", closed_seq, %err, "ConsensusLedgerAcceptor: inner accept_ledger job failed");
                    }
                }
            })
        {
            return Err("accept job queue is stopping".to_owned());
        }

        Ok(closed_seq.saturating_add(1))
    }

    fn publish_validation(&self, validation: Arc<protocol::STValidation>) {
        // Matches the reference's `RCLConsensus::Adaptor::validate` tail:
        // `handleNewValidation(app_, v, "local")` followed by
        // `app_.getOverlay().broadcast(TMValidation)`. Feeding it through
        // the SAME `receive_validation_to_network_ops` path used for
        // incoming peer validations (rather than a separate "local-only"
        // insert) matches the reference registering its own validation in
        // the identical trust-trie/`Validations` structure peer validations
        // use, which is what lets `Validations::getPreferred` later compare
        // this node's own validated branch against what its peers report.
        let mut owned = (*validation).clone();
        let serialized = owned.get_serialized();
        let suppression = protocol::sha512_half(&serialized);
        if let Some(overlay_rt) = self.root.overlay_runtime() {
            overlay_rt.overlay().suppress_validation(suppression);
        }
        let _ = self
            .root
            .receive_validation_to_network_ops_with_accept(&mut owned, "local", &self.root);

        if let Some(overlay_rt) = self.root.overlay_runtime() {
            overlay_rt.overlay().broadcast_validation(
                overlay::TmValidation {
                    validation: serialized,
                    ..Default::default()
                },
                *owned.get_signer_public(),
            );
        }
    }

    fn closed_ledger(&self) -> Option<Arc<Ledger>> {
        self.root.closed_ledger()
    }

    fn consensus_built(&self, ledger: Arc<ledger::Ledger>) -> Result<(), String> {
        let root = self.root.clone();
        let seq = ledger.header().seq;
        let name = format!("ConsensusBuilt#{seq}");

        if !self
            .job_queue
            .add_job(crate::job::job_types::JobType::JtAccept, name, move || {
                root.on_consensus_built_ledger(Arc::clone(&ledger));
            })
        {
            return Err("consensus_built job queue is stopping".to_owned());
        }

        Ok(())
    }

    fn consensus_closed_ledger(&self) -> Option<Arc<Ledger>> {
        self.root.consensus_closed_ledger()
    }

    fn consensus_previous_ledger(&self) -> Option<Arc<Ledger>> {
        self.root.consensus_previous_ledger()
    }

    fn node_fetcher(
        &self,
    ) -> Option<
        Arc<
            dyn Fn(
                    basics::sha_map_hash::SHAMapHash,
                ) -> Option<
                    basics::memory::intrusive_pointer::SharedIntrusive<
                        shamap::nodes::tree_node::SHAMapTreeNode,
                    >,
                > + Send
                + Sync,
        >,
    > {
        let guard = self.shared_node_store.read().ok()?;
        let ns = guard.as_ref();
        if ns.is_none() {
            static FETCH_MISS: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
            if FETCH_MISS.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < 3 {
                tracing::debug!(target: "consensus",
                    "[consensus_fetcher] shared_node_store is None — node store not yet attached"
                );
            }
            return None;
        }
        let ns = ns?.clone();
        Some(Arc::new(move |hash| {
            let data = match &ns {
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Single(db) => db
                    .fetch_node_object(
                        hash.as_uint256(),
                        0,
                        nodestore::FetchType::Synchronous,
                        false,
                    ),
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Rotating(db) => db
                    .fetch_node_object(
                        hash.as_uint256(),
                        0,
                        nodestore::FetchType::Synchronous,
                        false,
                    ),
            }?;
            shamap::nodes::tree_node::SHAMapTreeNode::make_from_prefix(data.data(), hash).ok()
        }))
    }
}

impl ApplicationRoot {
    pub fn clone_ledger_acceptor(&self) -> Arc<dyn LedgerAcceptor> {
        Arc::new(ConsensusLedgerAcceptor {
            root: self.clone(),
            job_queue: Arc::clone(&self.job_queue),
            basic_app: Arc::clone(&self.basic_app),
            shared_node_store: Arc::clone(&self.shared_consensus_node_store),
        })
    }
    pub fn new(worker_threads: usize) -> std::io::Result<Self> {
        Self::with_options(ApplicationRootOptions {
            io_threads: worker_threads,
            job_queue_threads: worker_threads.max(1),
            ..ApplicationRootOptions::default()
        })
    }

    pub fn with_runtime_bindings(
        options: ApplicationRootOptions,
        runtime_bindings: RuntimeBindings,
    ) -> std::io::Result<Self> {
        let mut root = Self::with_options(options)?;
        root.set_runtime_bindings(runtime_bindings);
        Ok(root)
    }

    pub fn with_options(options: ApplicationRootOptions) -> std::io::Result<Self> {
        let ApplicationRootOptions {
            io_threads,
            job_queue_threads,
            network_id,
            start_valid,
            elb_support,
            standalone,
            start_type,
            start_ledger,
            import,
            quorum,
            network_quorum,
            ledger_fetch_depth,
            fee_setup,
            collector_params,
            load_manager_timing,
        } = options;

        let mut registry = ApplicationRegistryOwners::new().map_err(std::io::Error::other)?;
        registry.network_id_service = FixedNetworkIdService::new(network_id);
        registry.config.standalone = standalone;
        registry.config.start_valid = start_valid;
        registry.config.start_up = start_type;
        registry.config.start_ledger = start_ledger;
        registry.config.do_import = import;
        if let Some(q) = quorum {
            registry.config.validation_quorum = q;
        }
        registry.config.network_quorum = network_quorum;
        let perf_log = Arc::clone(
            registry
                .perf_log
                .as_ref()
                .expect("application root must own a perf log"),
        );
        let job_queue = JobQueue::with_worker_threads(job_queue_threads.max(1));
        let shared_job_queue = Arc::new(job_queue.clone());
        let load_fee_track = Arc::new(SharedLoadFeeTrack::default());
        let collector_manager = CollectorManager::new(collector_params);
        let time_keeper = Arc::new(TimeKeeper::new());
        let close_time_provider = Arc::clone(&time_keeper)
            as Arc<dyn crate::ledger::ledger_master_state::LedgerMasterCloseTimeProvider>;
        let ledger_master_state = Arc::new(SharedLedgerMasterState::new(close_time_provider));
        let validations = SharedAppValidations::new(
            Arc::clone(&time_keeper),
            Arc::clone(&ledger_master_state),
            registry.logs.journal("Validations"),
        );
        let validators = Arc::new(ValidatorList::new_with_shared_caches(
            Arc::clone(&registry.validator_manifest_cache),
            Arc::clone(&registry.publisher_manifest_cache),
            SystemValidatorListClock,
            std::env::temp_dir().join("quaxar-application-root-validator-list"),
            quorum,
        ));
        let _ = validators.load(None, &[], &[], None);

        let network_ops_state = Arc::new(SharedNetworkOpsState::new(if start_valid {
            NetworkOpsOperatingMode::Full
        } else {
            NetworkOpsOperatingMode::Disconnected
        }));

        *registry
            .network_ops_state_sink
            .lock()
            .expect("network_ops_state_sink mutex poisoned") = Some(Arc::clone(&network_ops_state));

        let shared_subscription_manager: SharedSubscriptionPublisher =
            Arc::new(std::sync::RwLock::new(None));
        let fee_change_reporter = Arc::new(FeeChangeReporter {
            job_queue: Arc::clone(&shared_job_queue),
            load_fee_track: Arc::clone(&load_fee_track),
            open_ledger: registry.open_ledger.clone(),
            tx_q: registry.tx_q.clone(),
            network_ops_state: Arc::clone(&network_ops_state),
            subscription_manager: Arc::clone(&shared_subscription_manager),
            last_summary: Arc::new(Mutex::new(None)),
        });
        let load_fee_control: Arc<dyn crate::load::load_manager::LoadFeeControl> =
            load_fee_track.clone();
        let load_manager = LoadManager::with_timing(
            job_queue.clone(),
            load_fee_control,
            Arc::new(AppLoadManagerEvents {
                collector_manager: collector_manager.clone(),
                fee_change_reporter: Arc::clone(&fee_change_reporter),
            }),
            registry.logs.journal("load_manager"),
            load_manager_timing,
        );
        let transaction_master = Arc::new(TransactionMaster::new());
        let consensus_tx_set_submit_adapter = Arc::new(
            crate::consensus::consensus_trans_set_sf::ConsensusFetchedTxSubmitAdapter::default(),
        );
        // rippled installs ConsensusTransSetSF on every inbound transaction-set
        // acquisition. Its prefix payload is the NodeStore/SHAMap prefix
        // format (not the peer wire format); SHAMapTreeNode::make_from_prefix
        // is the corresponding decoder and is covered by an exact hash test.
        // Keeping this disabled made every disputed set re-download transaction
        // leaves already resident in TransactionMaster.
        let consensus_tx_set_filter = Arc::new(
            crate::consensus::consensus_trans_set_sf::ConsensusTransSetSFFactory::new(
                Arc::clone(&transaction_master),
                Arc::clone(&registry.temp_node_cache),
                Arc::downgrade(&consensus_tx_set_submit_adapter),
            ),
        );
        registry
            .inbound_transactions
            .lock()
            .expect("inbound transactions mutex must not be poisoned")
            .set_filter_factory(consensus_tx_set_filter);

        Ok(Self {
            basic_app: Arc::new(BasicApp::new(io_threads)?),
            job_queue: Arc::clone(&shared_job_queue),
            ledger_persistence_runtime: Arc::new(std::sync::RwLock::new(Arc::new(
                crate::AppLedgerPersistenceRuntime::with_job_queue(
                    None,
                    None,
                    Arc::clone(&transaction_master),
                    0,
                    None,
                    Some(Arc::clone(&shared_job_queue)),
                ),
            ))),
            time_keeper: Arc::clone(&time_keeper),
            sntp_client: None,
            stop_tree: Arc::new(StopTree::new("application")),
            collector_manager: Arc::new(collector_manager),
            load_manager: Arc::new(load_manager),
            load_fee_track,
            fee_vote_setup: fee_setup,
            ledger_fetch_depth,
            fee_change_reporter,
            registry,
            manifest_limits: ManifestLimits::default(),
            node_store_scheduler: Arc::new(NodeStoreScheduler::new(job_queue)),
            node_family: None,
            resolver_runtime: None,
            overlay_runtime: None,
            overlay_status: None,
            server_ports_setup: None,
            published_server_ports: None,
            status_metrics: Some(Arc::clone(&perf_log) as Arc<dyn StatusMetricsSource>),
            ledger_delta_publisher: None,
            ledger_close_publisher: None,
            transaction_publisher: None,
            shared_subscription_manager,
            network_ops_state,
            network_ops_runtime: None,
            network_ops_validation_runtime: None,
            ledger_master_runtime: None,
            consensus_runtime: None,
            ledger_master_state,
            transaction_master: Arc::clone(&transaction_master),
            consensus_tx_set_submit_adapter: Some(consensus_tx_set_submit_adapter),
            validations,
            validators,
            status_rpc_state: Arc::new(StatusRpcState::new()),
            snapshot_export_state: Arc::new(SnapshotExportState::default()),
            amendment_status: Arc::new(AmendmentStatus::new()),
            elb_support,
            node_identity: None,
            validation_public_key: None,
            runtime_bindings: RuntimeBindings {
                grpc: GrpcRuntime::default(),
                ..RuntimeBindings::default()
            },
            shamap_store_service: None,
            shared_consensus_node_store: Arc::new(std::sync::RwLock::new(None)),
            shared_consensus_rt: Arc::new(std::sync::RwLock::new(None)),
            shared_network_ops_rt: Arc::new(std::sync::RwLock::new(None)),
            fetch_pack_ready: Arc::new(std::sync::atomic::AtomicBool::new(false)),
            pending_replay_startup: Arc::new(Mutex::new(None)),
            open_ledger_account_seqs: Arc::new(std::sync::Mutex::new(
                std::collections::HashMap::new(),
            )),
            open_ledger_sandbox: Arc::new(std::sync::Mutex::new(None)),
            close_gate: Arc::new(std::sync::Mutex::new(())),
            lcl_transition_gate: Arc::new(parking_lot::ReentrantMutex::new(())),
            validation_advance_gate: Arc::new(parking_lot::Mutex::new(())),
            publication_advance: Arc::new(Mutex::new(PublicationAdvanceState::default())),
            consensus_notify: Arc::new((std::sync::Mutex::new(false), std::sync::Condvar::new())),
            shared_tree_cache: std::sync::OnceLock::new(),
            max_disallowed_ledger: Arc::new(std::sync::atomic::AtomicU32::new(0)),
        })
    }

    pub fn basic_app(&self) -> &BasicApp {
        &self.basic_app
    }

    /// Signal that the shared fetch-pack cache was populated.
    /// InboundLedger workers should re-check local storage.
    pub fn signal_fetch_pack_ready(&self) {
        self.fetch_pack_ready
            .store(true, std::sync::atomic::Ordering::Release);
    }

    /// Check and clear the fetch-pack-ready flag. Returns true if it was set.
    pub fn take_fetch_pack_ready(&self) -> bool {
        self.fetch_pack_ready
            .swap(false, std::sync::atomic::Ordering::AcqRel)
    }

    /// Park replay startup until the exact historical parent has completed
    /// the normal inbound `History` acquisition lifecycle.
    pub fn defer_replay_startup(&self, pending: PendingReplayStartup) {
        *self
            .pending_replay_startup
            .lock()
            .expect("pending replay startup mutex must not be poisoned") = Some(pending);
    }

    /// Returns the replay startup request without consuming it. The recovery
    /// coordinator retains it until replay has successfully reloaded the
    /// fully persisted parent from NodeStore.
    pub fn pending_replay_startup(&self) -> Option<PendingReplayStartup> {
        self.pending_replay_startup
            .lock()
            .expect("pending replay startup mutex must not be poisoned")
            .clone()
    }

    /// Clear a completed replay startup request. Matching on the exact parent
    /// prevents a stale recovery worker from clearing a newer request.
    pub fn clear_pending_replay_startup(&self, parent_hash: Uint256) -> bool {
        let mut pending = self
            .pending_replay_startup
            .lock()
            .expect("pending replay startup mutex must not be poisoned");
        if pending
            .as_ref()
            .is_some_and(|request| request.parent_hash == parent_hash)
        {
            *pending = None;
            return true;
        }
        false
    }

    /// Returns the close gate mutex. Used by on_close (adaptor) and the
    /// relay router (bootstrap.rs) to serialize transaction application
    /// with open-ledger capture — matching rippled's single-strand guarantee.
    pub fn close_gate(&self) -> &std::sync::Mutex<()> {
        &self.close_gate
    }

    /// Gate all LCL writers and the complete consensus accept handoff. The
    /// re-entrant mutex permits consensus-built reconciliation to install a
    /// preferred LCL while the consensus strand owns the outer transition.
    pub fn lcl_transition_gate(&self) -> &parking_lot::ReentrantMutex<()> {
        &self.lcl_transition_gate
    }

    #[cfg(test)]
    pub(crate) fn validation_advance_gate(&self) -> &parking_lot::Mutex<()> {
        &self.validation_advance_gate
    }

    /// Enqueue an already-authorized `JtBatch` job. Async ingress invokes
    /// this while it holds NetworkOps' state mutex and has atomically moved
    /// the dispatch state from `None` to `Scheduled`.
    pub fn enqueue_network_ops_transaction_batch(&self) -> bool {
        let root = self.clone();
        self.job_queue.add_job(
            crate::job::job_types::JobType::JtBatch,
            "TxBatchAsync",
            move || root.run_network_ops_transaction_batch(),
        )
    }

    /// Schedule pending async work only through NetworkOps' guarded
    /// `None -> Scheduled` transition. This is for retry and ledger paths;
    /// normal ingress already owns that transition and uses the enqueue helper.
    pub fn schedule_network_ops_transaction_batch(&self) -> bool {
        let Some(runtime) = self.network_ops_runtime() else {
            return false;
        };
        let root = self.clone();
        runtime.schedule_pending_transaction_batch(|| root.enqueue_network_ops_transaction_batch())
    }

    /// Execute the complete `NetworkOPsImp::transactionBatch` drain loop on a
    /// JobQueue worker. This is intentionally not a consensus-strand task.
    ///
    /// Matches rippled's `transactionBatch` exactly: the while-loop condition
    /// check does NOT hold any ledger gate. Only the inner
    /// `apply_network_ops_pending_to_open_ledger` acquires the gate for the
    /// actual open-ledger modification. This allows concurrent
    /// `process_transaction` calls (from JtTransaction jobs processing relayed
    /// peer transactions) to enqueue new work between iterations — matching
    /// rippled's `batchLock.unlock()` before `apply()` pattern.
    pub fn run_network_ops_transaction_batch(&self) {
        while self.network_ops_pending_transaction_count().unwrap_or(0) != 0 {
            if self.apply_network_ops_pending_to_open_ledger().is_none() {
                if let Some(runtime) = self.network_ops_runtime() {
                    if runtime.take_pending_batch_panic_recovery() {
                        let _ = self.schedule_network_ops_transaction_batch();
                    } else {
                        let _ = runtime.release_scheduled_transaction_batch_for_retry();
                    }
                }
                break;
            }
        }
    }

    /// Notify the consensus strand loop that proposals or other consensus-
    /// relevant events are pending. Called by the overlay when proposals
    /// arrive. Wakes the strand loop from its condvar wait immediately.
    pub fn notify_consensus_event(&self) {
        let (lock, cvar) = &*self.consensus_notify;
        let mut pending = lock.lock().expect("consensus_notify lock");
        *pending = true;
        cvar.notify_one();
    }

    /// Narrow wake capability for background producers which must notify the
    /// serialized NetworkOps owner without retaining an ApplicationRoot clone
    /// (and therefore without forming a component ownership cycle).
    pub(crate) fn consensus_wake_callback(&self) -> Arc<dyn Fn() + Send + Sync> {
        let notify = Arc::clone(&self.consensus_notify);
        Arc::new(move || {
            let (lock, cvar) = &*notify;
            let mut pending = lock.lock().expect("consensus_notify lock");
            *pending = true;
            cvar.notify_one();
        })
    }

    /// Wait for a consensus event notification or timeout. Returns true if
    /// notified (proposals arrived), false on timeout.
    pub fn wait_consensus_or_timeout(&self, timeout: std::time::Duration) -> bool {
        let (lock, cvar) = &*self.consensus_notify;
        let mut pending = lock.lock().expect("consensus_notify lock");
        if *pending {
            *pending = false;
            return true;
        }
        let (mut guard, _timeout_result) = cvar
            .wait_timeout(pending, timeout)
            .expect("consensus_notify wait");
        let was_notified = *guard;
        *guard = false;
        was_notified
    }

    pub fn job_queue(&self) -> &JobQueue {
        &self.job_queue
    }

    pub fn collector_manager(&self) -> &CollectorManager {
        &self.collector_manager
    }

    pub fn load_manager(&self) -> &LoadManager {
        &self.load_manager
    }

    pub fn fd_required(&self) -> usize {
        let mut needed = 128usize;
        if let Some(setup) = self.server_ports_setup.as_ref() {
            needed += setup.fd_required();
        }
        if let Some(service) = self.shamap_store_service.as_ref() {
            needed += service.component().fd_required().max(5);
        }
        if let Some(node_store) = self.registry.node_store.as_ref() {
            needed += node_store.fd_required().max(5) as usize;
        }

        needed = needed.max(self.runtime_bindings().fd_required());
        needed.max(1024)
    }

    pub fn load_fee_track(&self) -> Arc<SharedLoadFeeTrack> {
        Arc::clone(&self.load_fee_track)
    }

    pub fn open_ledger(&self) -> &SharedAppOpenLedger {
        &self.registry.open_ledger
    }

    pub fn order_book_db(&self) -> Arc<OrderBookDB> {
        Arc::clone(&self.registry.order_book_db)
    }

    pub fn live_current_ledger_index(&self) -> Option<u32> {
        let current_index = self.registry.open_ledger.current().ledger_current_index;
        (current_index != 0).then_some(current_index)
    }

    /// Read the persistent current OpenView used by local transaction
    /// admission. The outer `None` means no open sandbox has been published
    /// yet; callers may then use the closed parent as the bootstrap fallback.
    /// Once available, its result is authoritative for RPC requests selecting
    /// `ledger_index: current`.
    pub fn current_open_ledger_entry(
        &self,
        keylet: protocol::Keylet,
    ) -> Option<Result<Option<STLedgerEntry>, ledger::ViewError>> {
        let sandbox = self.open_ledger_sandbox.lock().ok()?;
        sandbox.as_ref().map(|view| {
            view.read(keylet)
                .map(|entry| entry.map(|entry| entry.as_ref().clone()))
        })
    }

    /// Return the next state key from the persistent current OpenView. See
    /// `current_open_ledger_entry` for the availability and authority rules.
    pub fn current_open_ledger_successor(
        &self,
        key: Uint256,
        last: Option<Uint256>,
    ) -> Option<Result<Option<Uint256>, ledger::ViewError>> {
        let sandbox = self.open_ledger_sandbox.lock().ok()?;
        sandbox.as_ref().map(|view| view.succ(key, last))
    }

    pub fn tx_q(&self) -> &SharedAppTxQ {
        &self.registry.tx_q
    }

    pub fn tx_q_account_txs(
        &self,
        account_id: AccountID,
    ) -> Vec<TxDetails<AppTxQTransaction, AppTxQAccount>> {
        self.registry.tx_q.current_account_txs(account_id)
    }

    pub fn tx_q_metrics(&self) -> QueueTxQMetrics {
        let current = self.registry.open_ledger.current();
        let mut lock = AppTxQLock;
        self.registry.tx_q.get_metrics(&mut lock, current.as_ref())
    }

    pub fn tx_q_rpc_report(&self) -> QueueTxQRpcReport {
        let current = self.registry.open_ledger.current();
        let mut lock = AppTxQLock;
        self.registry
            .tx_q
            .get_rpc_fee_report(&mut lock, current.as_ref())
    }

    /// Runs simulate through TxQ's canonical admission and direct-apply path
    /// against cloned queue/view state. This follows
    /// ../rippled/src/xrpld/rpc/handlers/transaction/Simulate.cpp::simulateTxn,
    /// which copies the current OpenView before invoking TxQ::apply(TapDryRun).
    pub fn simulate_transaction(&self, ledger: Arc<Ledger>, tx: Arc<STTx>) -> SimulationOutcome {
        let mut open_view = (*self.open_ledger().current()).clone();
        if open_view.ledger_current_index == 0 {
            open_view.ledger_current_index = ledger.header().seq;
            open_view.base_fee_drops = ledger.fees().base;
            open_view.parent_hash = *ledger.header().hash.as_uint256();
        }
        // Simulate.cpp copies OpenLedger::current(), not its closed parent.
        // The persistent submit sandbox is Quaxar's concrete OpenView state:
        // it contains sequence, balance, and all prior open-ledger mutations.
        // Clone it for dry-run isolation so the simulation never publishes
        // changes back to the live open ledger.
        let mut apply_view = self
            .open_ledger_sandbox
            .lock()
            .expect("sandbox mutex")
            .as_ref()
            .cloned()
            .unwrap_or_else(|| {
                Sandbox::new(
                    Arc::new(ledger::OpenView::new_open(
                        Arc::clone(&ledger),
                        ledger.rules().clone(),
                    )),
                    ApplyFlags::DRY_RUN,
                )
            });
        let ledger_seq = open_view.ledger_current_index;
        let close_time = apply_view.header().close_time;
        let simulation_rules = apply_view.rules();
        let mut simulation_view =
            ledger::FlowSandbox::new_with_flags(&mut apply_view, ApplyFlags::DRY_RUN);
        let tx_source = AppQueueApplyTxSource::new(tx.as_ref());
        let account_seqs = Arc::new(std::sync::Mutex::new(std::collections::HashMap::new()));
        let result = self.registry.tx_q.simulate_with(|tx_q| {
            let metrics_snapshot = tx_q.metrics_snapshot();
            let live_queue_view =
                open_view.queue_apply_view(&simulation_view, tx.as_ref(), metrics_snapshot);
            let queue_view = snapshot_queue_apply_app_view_with_metrics(
                &tx_source,
                &live_queue_view,
                metrics_snapshot,
            );
            let mut runtime = AppOpenLedgerTxQApplyRuntime::new_with_clear_ahead(
                &mut open_view,
                &mut simulation_view,
                Arc::clone(&tx),
                ApplyFlags::DRY_RUN,
                ledger_seq,
                self.load_fee_track.as_ref(),
                Arc::clone(&account_seqs),
                self.registry.network_id_service.get_network_id(),
                tx_q.get_account_txs(
                    &mut AppTxQLock,
                    &tx.get_account_id(get_field_by_symbol("sfAccount")),
                ),
                metrics_snapshot,
            );
            let mut lock = AppTxQLock;
            let result = tx_q
                .apply_with_owned_metrics_and_derived_preflight_facts_and_hold_admission(
                    &mut lock,
                    &mut runtime,
                    &queue_view,
                    &tx_source,
                )
                .apply_result();
            (result, runtime.delivered_amount.clone())
        });
        let metadata = (is_tes_success(result.0.ter) || is_tec_claim(result.0.ter))
            .then(|| {
                simulation_view
                    .to_tx_meta(
                        tx.get_transaction_id(),
                        ledger_seq,
                        result.1,
                        &simulation_rules,
                    )
                    .ok()
                    .map(|mut metadata| {
                        let mut serialized = Serializer::default();
                        metadata.add_raw(&mut serialized, result.0.ter, 0);
                        metadata
                    })
            })
            .flatten();

        SimulationOutcome {
            result: result.0,
            ledger_seq,
            close_time,
            metadata,
        }
    }

    fn validated_fee_levels_for_closed_ledger(&self, ledger: &Ledger) -> Vec<u64> {
        let fee_field = get_field_by_symbol("sfFee");

        ledger
            .tx_snapshot()
            .map(|entries| {
                entries
                    .into_iter()
                    .map(|(tx, _meta)| {
                        let fee_paid_drops = if tx.is_field_present(fee_field) {
                            tx.get_field_amount(fee_field).xrp().drops()
                        } else {
                            0
                        };

                        // Parity: ../rippled/src/xrpld/app/misc/detail/TxQ.cpp::getFeeLevelPaid.
                        evaluate_fee_level_paid(QueueFeeLevelPaidInputs {
                            calculated_base_fee_drops: fee_drops_as_i64(
                                calculate_sttx_base_fee_for_metrics(ledger, &tx),
                            ),
                            fee_paid_drops,
                            default_base_fee_drops: fee_drops_as_i64(
                                calculate_default_sttx_base_fee(ledger, &tx),
                            ),
                        })
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    pub(crate) fn process_closed_ledger_txq(
        &self,
        ledger: &Ledger,
        time_leap: bool,
    ) -> tx::ClosedLedgerMaintenanceWithMetrics<AppTxQAccount> {
        let mut lock = AppTxQLock;
        self.registry.tx_q.process_closed_ledger(
            &mut lock,
            self,
            &AppClosedLedgerTxQView { ledger },
            time_leap,
        )
    }

    fn rebuild_open_ledger_after_close(&self, parent: Arc<Ledger>) {
        // OpenLedger::accept and the persistent sandbox replacement form one
        // current-open-state transition. Server-side legacy signing holds this
        // same re-entrant gate from TxQ::nextQueuableSeq through admission, so
        // it cannot read the old sandbox while this rebase is replaying local
        // transactions and then overwrite its newly admitted state.
        let _lcl_transition_guard = self.lcl_transition_gate().lock();
        let next_open_index = parent.header().seq.saturating_add(1);
        let base_fee_drops = parent.fees().base;
        let parent_hash = *parent.header().hash.as_uint256();
        let local_txs = self.local_open_ledger_records();
        let local_tx_count = local_txs.len();
        let mut already_in_parent_count = 0usize;
        let mut parent_lookup_diagnostic_errors = 0usize;
        for record in &local_txs {
            match parent.try_tx_exists(record.tx.get_transaction_id()) {
                Ok(true) => already_in_parent_count += 1,
                Ok(false) => {}
                Err(error) => {
                    parent_lookup_diagnostic_errors += 1;
                    tracing::error!(target: "lcl_audit", ?error, parent_seq = parent.header().seq,
                        tx = %record.tx.get_transaction_id(),
                        "open-ledger rebase diagnostic parent transaction lookup failed");
                }
            }
        }
        let local_tx_id_sample = local_txs
            .iter()
            .take(16)
            .map(|record| record.tx.get_transaction_id())
            .collect::<Vec<_>>();
        let open_before = self.open_ledger().current_open_transactions();
        let open_before_count = open_before.len();
        let open_before_id_sample = open_before
            .iter()
            .take(16)
            .map(|tx| tx.get_transaction_id())
            .collect::<Vec<_>>();
        tracing::info!(
            target: "lcl_audit",
            parent_hash = %parent.header().hash,
            parent_seq = parent.header().seq,
            next_open_index,
            local_tx_count,
            already_in_parent_count,
            parent_lookup_diagnostic_errors,
            local_tx_id_sample = ?local_tx_id_sample,
            open_before_count,
            open_before_id_sample = ?open_before_id_sample,
            "LCL_AUDIT open-ledger rebase started"
        );
        let mut retries = Vec::<AppOpenLedgerTxRecord>::new();
        let rebase_view = std::cell::RefCell::new(Sandbox::new(
            Arc::new(ledger::OpenView::new_open(
                Arc::clone(&parent),
                parent.rules().clone(),
            )),
            ApplyFlags::NONE,
        ));
        let applied_ids = std::cell::RefCell::new(std::collections::HashSet::new());

        let check_errors = self.open_ledger().accept(
            || {
                AppOpenLedgerView::with_parent_timing(
                    next_open_index,
                    base_fee_drops,
                    parent_hash,
                    parent.header().close_time,
                    parent.header().close_time_resolution,
                )
            },
            &|tx_id: &Uint256| parent.try_tx_exists(*tx_id),
            local_txs,
            false,
            &mut retries,
            ApplyFlags::NONE,
            &mut |view: &mut AppOpenLedgerView, tx: &AppOpenLedgerTxRecord, flags| {
                self.reapply_open_ledger_record(
                    view,
                    &mut *rebase_view.borrow_mut(),
                    &mut applied_ids.borrow_mut(),
                    tx,
                    flags,
                )
            },
            &mut |view: &mut AppOpenLedgerView, tx: &AppOpenLedgerTxRecord, flags| {
                let _ = self.apply_local_open_ledger_record_with_txq(
                    view,
                    &mut *rebase_view.borrow_mut(),
                    &mut applied_ids.borrow_mut(),
                    tx,
                    flags,
                );
            },
            Some(|view: &mut AppOpenLedgerView| {
                let snapshot = AppOpenLedgerTxQAcceptView {
                    open_ledger_tx_count: view.tx_ids().len(),
                    parent_hash: view.parent_hash,
                };
                let mut runtime = AppOpenLedgerTxQAcceptRuntime {
                    root: self,
                    view,
                    rebase_view: &mut *rebase_view.borrow_mut(),
                    applied_ids: &mut applied_ids.borrow_mut(),
                    flags: ApplyFlags::NONE,
                };
                let mut lock = AppTxQLock;
                self.registry
                    .tx_q
                    .accept(&mut lock, &mut runtime, &snapshot)
                    .ledger_changed
            }),
            // Match rippled OpenLedger::accept: re-relay every recovered
            // transaction that survives reapplication, so a peer that missed
            // the first ingress relay can include it in a later consensus set.
            &mut |_tx_id: &Uint256| true,
            &mut |record: &AppOpenLedgerTxRecord| {
                let tx = &record.tx;
                // Inner Batch transactions are never independently relayed.
                if tx.is_flag(tfInnerBatchTxn) {
                    return;
                }
                let tx_id = tx.get_transaction_id();
                let Some(to_skip) = self.registry.hash_router.should_relay(tx_id) else {
                    return;
                };
                let Some(overlay_rt) = self.overlay_runtime() else {
                    return;
                };
                let now = self.shared_time_keeper().now().as_seconds() as u64;
                overlay_rt.overlay().relay_transaction(
                    tx_id,
                    Some(queue_relay_envelope(
                        tx.get_serializer().data().to_vec(),
                        now,
                        false,
                    )),
                    &to_skip,
                );
            },
        );
        for error in check_errors {
            tracing::error!(target: "lcl_audit", ?error, parent_seq = parent.header().seq,
                "open-ledger rebase skipped a transaction whose parent lookup failed");
        }
        *self.open_ledger_sandbox.lock().expect("sandbox mutex") = Some(rebase_view.into_inner());
        let open_after = self.open_ledger().current_open_transactions();
        let open_after_id_sample = open_after
            .iter()
            .take(16)
            .map(|tx| tx.get_transaction_id())
            .collect::<Vec<_>>();
        tracing::info!(
            target: "lcl_audit",
            parent_hash = %parent.header().hash,
            parent_seq = parent.header().seq,
            next_open_index,
            retry_count = retries.len(),
            open_after_count = open_after.len(),
            open_after_id_sample = ?open_after_id_sample,
            "LCL_AUDIT open-ledger rebase completed"
        );
    }

    fn reapply_open_ledger_record<V: ledger::ApplyView>(
        &self,
        open_ledger: &mut AppOpenLedgerView,
        rebase_view: &mut V,
        applied_ids: &mut std::collections::HashSet<Uint256>,
        record: &AppOpenLedgerTxRecord,
        flags: ApplyFlags,
    ) -> ApplyResult {
        let tx = Arc::clone(&record.tx);
        let tx_id = tx.get_transaction_id();
        if applied_ids.contains(&tx_id) {
            return ApplyResult::new(Ter::TEF_ALREADY, false, false);
        }

        let preflight = transaction_preflight_ter_with_flags_and_network_id(
            tx.as_ref(),
            &rebase_view.rules(),
            flags,
            self.registry.network_id_service.get_network_id(),
        );
        let preclaim = if is_tes_success(preflight) {
            queue_apply_preclaim_ter_with_load_fee(
                rebase_view,
                tx.as_ref(),
                open_ledger.ledger_current_index,
                flags,
                self.load_fee_track.as_ref(),
            )
        } else {
            preflight
        };
        let outcome = if is_tes_success(preclaim) || is_tec_claim(preclaim) {
            apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim_and_network_id(
                rebase_view,
                tx.as_ref(),
                tx.get_txn_type(),
                flags,
                preclaim,
                self.registry.network_id_service.get_network_id(),
            )
        } else {
            SubmitApplyOutcome {
                result: preclaim,
                applied: false,
                delivered_amount: None,
                prebuilt_outer_metadata: None,
                applied_batch_inner_transactions: Vec::new(),
            }
        };
        if outcome.applied {
            applied_ids.insert(tx_id);
            for inner in &outcome.applied_batch_inner_transactions {
                applied_ids.insert(inner.transaction.get_transaction_id());
            }
            record_applied_open_transactions(
                open_ledger,
                tx,
                &outcome.applied_batch_inner_transactions,
            );
        }
        ApplyResult::new(outcome.result, outcome.applied, false)
    }

    /// Apply a LocalTx during `OpenLedger::accept` through the full TxQ
    /// admission path, matching rippled `TxQ::apply(app, view, tx, flags)`.
    ///
    /// rippled first preflights and tries a direct apply; if direct application
    /// cannot proceed, it performs complete persistent TxQ admission instead of
    /// losing the transaction. That queue admission includes account sequence
    /// ordering, replacement, fee escalation, blocker checks, and queue-size
    /// eviction. Reuse the same facade/runtime already used by ordinary local
    /// `submit`, rather than maintaining a narrower replay-only substitute.
    fn apply_local_open_ledger_record_with_txq<V: ledger::ApplyView>(
        &self,
        open_ledger: &mut AppOpenLedgerView,
        rebase_view: &mut V,
        applied_ids: &mut std::collections::HashSet<Uint256>,
        record: &AppOpenLedgerTxRecord,
        flags: ApplyFlags,
    ) -> ApplyResult {
        let tx = Arc::clone(&record.tx);
        let tx_id = tx.get_transaction_id();
        if applied_ids.contains(&tx_id) {
            return ApplyResult::new(Ter::TEF_ALREADY, false, false);
        }

        let tx_source = AppQueueApplyTxSource::new(tx.as_ref());
        let account = tx.get_account_id(get_field_by_symbol("sfAccount"));
        let tx_q = &self.registry.tx_q;
        let clear_ahead_queue = tx_q.current_account_txs(account);
        let metrics_snapshot = tx_q.metrics_snapshot();
        let view_snapshot = open_ledger.clone();
        let live_queue_view =
            view_snapshot.queue_apply_view(rebase_view, tx.as_ref(), metrics_snapshot);
        let queue_view = snapshot_queue_apply_app_view_with_metrics(
            &tx_source,
            &live_queue_view,
            metrics_snapshot,
        );
        let current_ledger_index = open_ledger.ledger_current_index;
        let mut runtime = AppOpenLedgerTxQApplyRuntime::new_with_clear_ahead(
            open_ledger,
            rebase_view,
            Arc::clone(&tx),
            flags,
            current_ledger_index,
            self.load_fee_track.as_ref(),
            Arc::clone(&self.open_ledger_account_seqs),
            self.registry.network_id_service.get_network_id(),
            clear_ahead_queue,
            metrics_snapshot,
        );
        let mut lock = AppTxQLock;
        let result = tx_q
            .apply_with_owned_metrics_and_derived_preflight_facts_and_hold_admission(
                &mut lock,
                &mut runtime,
                &queue_view,
                &tx_source,
            )
            .apply_result();
        let (clear_attempts, clear_removed) = runtime.take_clear_ahead_effects();
        tx_q.apply_try_clear_effects(account, &clear_attempts, &clear_removed);

        if result.applied {
            applied_ids.insert(tx_id);
        }
        result
    }

    /// Rebuild the open ledger on a newly selected closed parent.
    ///
    /// This mirrors rippled `OpenLedger::apply`: transactions already included
    /// in the parent must be discarded rather than carried into the next
    /// proposal. This matters especially when switching to an acquired LCL,
    /// whose transaction map can overlap the old local open ledger.
    pub(crate) fn rebuild_open_ledger_after_consensus(
        &self,
        parent: Arc<Ledger>,
        retry_transactions: &[Arc<STTx>],
        retries_first: bool,
    ) {
        self.rebuild_open_ledger_after_consensus_with_completed(
            parent,
            retry_transactions,
            retries_first,
            &std::collections::HashSet::new(),
        );
    }

    /// Rebuild the open ledger after consensus using the authoritative set of
    /// transactions that the accepted candidate terminalized. rippled's
    /// `OpenLedger::accept` begins from the new closed ledger, so completed
    /// work cannot return to the next proposal even if a backed transaction
    /// map is temporarily unavailable during rebase.
    pub(crate) fn rebuild_open_ledger_after_consensus_with_completed(
        &self,
        parent: Arc<Ledger>,
        retry_transactions: &[Arc<STTx>],
        retries_first: bool,
        completed_transaction_ids: &std::collections::HashSet<Uint256>,
    ) {
        // See `rebuild_open_ledger_after_close`: publication of the rebuilt
        // OpenLedger and persistent sandbox must be atomic with respect to
        // server-side signing's current-open TxQ sequence lookup.
        let _lcl_transition_guard = self.lcl_transition_gate().lock();
        let next_open_index = parent.header().seq.saturating_add(1);
        let base_fee_drops = parent.fees().base;
        let parent_hash = *parent.header().hash.as_uint256();
        let local_txs = self
            .local_open_ledger_records()
            .into_iter()
            .filter(|record| !completed_transaction_ids.contains(&record.tx.get_transaction_id()))
            .collect::<Vec<_>>();
        let completed_transaction_count = completed_transaction_ids.len();
        let local_tx_count = local_txs.len();
        let local_tx_id_sample = local_txs
            .iter()
            .take(16)
            .map(|record| record.tx.get_transaction_id())
            .collect::<Vec<_>>();
        let retry_count_in = retry_transactions.len();
        let mut retries = retry_transactions
            .iter()
            .filter(|tx| !completed_transaction_ids.contains(&tx.get_transaction_id()))
            .cloned()
            .map(AppOpenLedgerTxRecord::new)
            .collect::<Vec<_>>();
        tracing::info!(
            target: "lcl_audit",
            parent_hash = %parent.header().hash,
            parent_seq = parent.header().seq,
            next_open_index,
            local_tx_count,
            completed_transaction_count,
            retry_count_in,
            retries_first,
            local_tx_id_sample = ?local_tx_id_sample,
            "LCL_AUDIT consensus open-ledger rebuild started"
        );
        let rebase_view = std::cell::RefCell::new(Sandbox::new(
            Arc::new(ledger::OpenView::new_open(
                Arc::clone(&parent),
                parent.rules().clone(),
            )),
            ApplyFlags::NONE,
        ));
        let applied_ids = std::cell::RefCell::new(std::collections::HashSet::new());
        let check_errors = self.open_ledger().accept(
            || {
                AppOpenLedgerView::with_parent_timing(
                    next_open_index,
                    base_fee_drops,
                    parent_hash,
                    parent.header().close_time,
                    parent.header().close_time_resolution,
                )
            },
            &|tx_id: &Uint256| parent.try_tx_exists(*tx_id),
            local_txs,
            retries_first,
            &mut retries,
            ApplyFlags::NONE,
            &mut |view: &mut AppOpenLedgerView, tx: &AppOpenLedgerTxRecord, flags| {
                self.reapply_open_ledger_record(
                    view,
                    &mut *rebase_view.borrow_mut(),
                    &mut applied_ids.borrow_mut(),
                    tx,
                    flags,
                )
            },
            &mut |view: &mut AppOpenLedgerView, tx: &AppOpenLedgerTxRecord, flags| {
                let _ = self.apply_local_open_ledger_record_with_txq(
                    view,
                    &mut *rebase_view.borrow_mut(),
                    &mut applied_ids.borrow_mut(),
                    tx,
                    flags,
                );
            },
            Some(|view: &mut AppOpenLedgerView| {
                let snapshot = AppOpenLedgerTxQAcceptView {
                    open_ledger_tx_count: view.tx_ids().len(),
                    parent_hash: view.parent_hash,
                };
                let mut runtime = AppOpenLedgerTxQAcceptRuntime {
                    root: self,
                    view,
                    rebase_view: &mut *rebase_view.borrow_mut(),
                    applied_ids: &mut applied_ids.borrow_mut(),
                    flags: ApplyFlags::NONE,
                };
                let mut lock = AppTxQLock;
                self.registry
                    .tx_q
                    .accept(&mut lock, &mut runtime, &snapshot)
                    .ledger_changed
            }),
            // Match rippled OpenLedger::accept: re-relay every recovered
            // transaction that survives reapplication, so a peer that missed
            // the first ingress relay can include it in a later consensus set.
            &mut |_tx_id: &Uint256| true,
            &mut |record: &AppOpenLedgerTxRecord| {
                let tx = &record.tx;
                // Inner Batch transactions are never independently relayed.
                if tx.is_flag(tfInnerBatchTxn) {
                    return;
                }
                let tx_id = tx.get_transaction_id();
                let Some(to_skip) = self.registry.hash_router.should_relay(tx_id) else {
                    return;
                };
                let Some(overlay_rt) = self.overlay_runtime() else {
                    return;
                };
                let now = self.shared_time_keeper().now().as_seconds() as u64;
                overlay_rt.overlay().relay_transaction(
                    tx_id,
                    Some(queue_relay_envelope(
                        tx.get_serializer().data().to_vec(),
                        now,
                        false,
                    )),
                    &to_skip,
                );
            },
        );
        for error in check_errors {
            tracing::error!(target: "lcl_audit", ?error, parent_seq = parent.header().seq,
                "consensus open-ledger rebuild skipped a transaction whose parent lookup failed");
        }
        let open_after = self.open_ledger().current_open_transactions();
        let open_after_count = open_after.len();
        let open_after_id_sample = open_after
            .iter()
            .take(16)
            .map(|tx| tx.get_transaction_id())
            .collect::<Vec<_>>();
        tracing::info!(
            target: "lcl_audit",
            parent_hash = %parent.header().hash,
            parent_seq = parent.header().seq,
            next_open_index,
            local_tx_count,
            retry_count_in,
            retry_count_out = retries.len(),
            open_after_count,
            open_after_id_sample = ?open_after_id_sample,
            "LCL_AUDIT consensus open-ledger rebuild completed"
        );
        *self.open_ledger_sandbox.lock().expect("sandbox mutex") = Some(rebase_view.into_inner());
    }

    fn local_open_ledger_records(&self) -> Vec<AppOpenLedgerTxRecord> {
        self.ledger_master_runtime()
            .map(|runtime| {
                runtime
                    .local_tx_set()
                    .iter()
                    .map(|tx| AppOpenLedgerTxRecord::new(Arc::clone(tx)))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Matches rippled `buildLCL` calling `LedgerMaster::storeLedger` before
    /// `doAccept` emits accepted status/local validation. Makes the child
    /// visible by exact hash to validation `checkAccept` without running the
    /// later consensusBuilt scan yet.
    pub(crate) fn store_consensus_ledger(&self, ledger: Arc<Ledger>) -> Arc<Ledger> {
        let ledger = self.ledger_with_node_fetcher(ledger);
        if let Some(runtime) = self.ledger_master_runtime()
            && ledger.header().hash.is_non_zero()
        {
            runtime
                .ledger_master()
                .ledger_history()
                .insert(Arc::clone(&ledger), false);
        }
        self.validations().register_ledger(&ledger);
        ledger
    }

    /// Execute the ledger-master portion of `consensusBuilt` exactly once for
    /// a child previously registered through `store_consensus_ledger`.
    /// The live AppConsensus path calls this after notification/local validation
    /// and before OpenLedger acceptance; alternate acceptors store first then
    /// reuse it through `on_consensus_built_ledger`.
    pub(crate) fn record_consensus_built_ledger(
        &self,
        ledger: Arc<Ledger>,
        consensus_hash: Uint256,
    ) -> Arc<Ledger> {
        if let Some(lm_rt) = self.ledger_master_runtime() {
            // A completed build is no longer protected from checkAccept.
            lm_rt.set_building_ledger(0);
        }
        let ledger = self.ledger_with_node_fetcher(ledger);
        // Rippled consensusBuilt clears building state then returns in
        // standalone mode before built-ledger metadata/checkAccept scanning.
        if self.standalone() {
            return ledger;
        }
        if let Some(runtime) = self.ledger_master_runtime()
            && ledger.header().hash.is_non_zero()
        {
            runtime.ledger_master().ledger_history().built_ledger(
                Arc::clone(&ledger),
                consensus_hash,
                JsonValue::Null,
            );
        }

        // `consensusBuilt` must check the built ledger and then scan the
        // current trusted validations before any next-round semantics.
        self.consensus_built_check_accept(&ledger);
        ledger
    }

    pub fn on_consensus_built_ledger(&self, ledger: Arc<Ledger>) {
        let consensus_hash = *ledger.header().tx_hash.as_uint256();
        let ledger = self.store_consensus_ledger(ledger);
        let ledger = self.record_consensus_built_ledger(ledger, consensus_hash);
        let _ = self.process_closed_ledger_txq(ledger.as_ref(), false);

        // Sweep local_txs: remove any TX already included in the built ledger
        // (matching rippled's localTxs_.sweep after consensus).
        let _ = self.update_local_tx(ledger.as_ref());

        let next_open_index = ledger.header().seq.saturating_add(1);
        self.rebuild_open_ledger_after_consensus(Arc::clone(&ledger), &[], false);

        if let Some(runtime) = self.ledger_master_runtime() {
            // `record_consensus_built_ledger` already inserted this built
            // ledger into history. Keep only LedgerMaster's closed slot here
            // for the alternate wrapper's legacy lookup behavior.
            runtime
                .ledger_master()
                .set_closed_ledger(Arc::clone(&ledger));
        }
        // buildLCL/storeLedger already populated history and the validation
        // cache above; mirror switchLCL without a second store/register.
        self.on_closed_ledger_after_store(Arc::clone(&ledger));
        self.set_status_rpc_current_ledger_index(Some(next_open_index));
        self.set_status_rpc_queue_report(Some(self.tx_q_rpc_report()));

        // `record_consensus_built_ledger` above is the sole owner of
        // LedgerHistory's built-ledger bookkeeping and its checkAccept scan.
    }

    /// Matches rippled's `LedgerMaster::consensusBuilt` validation scan.
    /// After building a local ledger, check whether the network has validated
    /// a different (or the same) ledger at a higher sequence than our current
    /// validated ledger, and advance to it.
    fn consensus_built_check_accept(&self, built_ledger: &Arc<Ledger>) {
        let Some(lm_rt) = self.ledger_master_runtime() else {
            return;
        };
        let lm = lm_rt.ledger_master();
        let valid_seq = lm.valid_ledger_seq();

        // If the built ledger is at or below the validated sequence, nothing
        // to do (we already validated past it).
        if built_ledger.header().seq <= valid_seq {
            return;
        }

        // Step 1: Try to validate our own built ledger directly.
        let built_hash = *built_ledger.header().hash.as_uint256();
        self.check_accept_hash_seq(built_hash, built_ledger.header().seq);

        // If that advanced us, we're done.
        if lm.valid_ledger_seq() >= built_ledger.header().seq {
            return;
        }

        // Step 2: Our built ledger didn't match the network. Scan all current
        // trusted validations to find the highest-sequence ledger above the
        // strict `consensusBuilt` alternate threshold.
        let needed_validations = self.needed_validations();

        let current_trusted = {
            let validations_guard = self
                .validations()
                .validations()
                .lock()
                .expect("validations mutex must not be poisoned");
            validations_guard.current_trusted()
        };

        // `current_trusted()` is deliberately generic and does not know the
        // app's negative UNL. Match rippled by filtering that current set,
        // then counting it by ledger hash. Do not substitute the historical
        // `getTrustedForLedger` set here: it can include validators whose
        // current validation has already moved to a different ledger.
        let current_trusted = self.validators().negative_unl_filter_validations(
            current_trusted
                .into_iter()
                .map(|validation| (*validation).clone())
                .collect(),
        );
        let candidates = consensus_built_current_validation_counts(
            current_trusted.into_iter().map(|validation| {
                (
                    validation.get_ledger_hash(),
                    validation.get_field_u32(protocol::get_field_by_symbol("sfLedgerSequence")),
                )
            }),
        );

        let mut max_seq = valid_seq;
        let mut max_hash = built_hash;
        for (hash, (validation_count, mut seq)) in candidates {
            if !consensus_built_alternate_threshold_met(validation_count, needed_validations) {
                continue;
            }
            // Validations without sfLedgerSequence require the same
            // ledger-history/closed-LCL lookup that rippled performs for a
            // zero `ValSeq::ledgerSeq` before comparing candidate sequence.
            if seq == 0 {
                seq = lm
                    .get_ledger_by_hash(SHAMapHash::new(hash))
                    .map(|ledger| ledger.header().seq)
                    .unwrap_or_default();
            }
            if seq > max_seq {
                max_seq = seq;
                max_hash = hash;
            }
        }

        if max_seq > valid_seq {
            tracing::info!(
                target: "consensus",
                max_seq,
                max_hash = %max_hash,
                built_seq = built_ledger.header().seq,
                "consensus_built: network validated a different ledger, advancing"
            );
            self.check_accept_hash_seq(max_hash, max_seq);
        }
    }

    pub fn perf_log(&self) -> Arc<PerfLogImp> {
        Arc::clone(
            self.registry
                .perf_log
                .as_ref()
                .expect("application root must own a perf log"),
        )
    }

    pub fn attach_perf_log(&mut self, perf_log: Arc<PerfLogImp>) -> Option<Arc<PerfLogImp>> {
        let previous = self.registry.attach_perf_log(Arc::clone(&perf_log));
        self.status_metrics = Some(Arc::clone(&perf_log) as Arc<dyn StatusMetricsSource>);
        previous
    }

    pub fn wallet_db(&self) -> Arc<DatabaseCon> {
        Arc::clone(&self.registry.wallet_db)
    }

    pub fn inbound_ledgers(&self) -> &AppInboundLedgers {
        &self.registry.inbound_ledgers
    }

    pub fn inbound_transactions(&self) -> &AppInboundTransactions {
        &self.registry.inbound_transactions
    }

    pub fn server_handler(&self) -> Arc<AppServerHandler> {
        Arc::clone(&self.registry.server_handler)
    }

    pub fn accepted_ledger_cache(&self) -> &AppAcceptedLedgerCache {
        &self.registry.accepted_ledger_cache
    }

    pub fn peer_reservations(&self) -> &PeerReservationTable<PublicKey> {
        self.registry.peer_reservations.as_ref()
    }

    pub fn peer_reservation_source(&self) -> Arc<dyn PeerReservationSource> {
        Arc::clone(&self.registry.peer_reservations) as Arc<dyn PeerReservationSource>
    }

    pub fn shared_cluster(&self) -> Arc<Cluster> {
        Arc::clone(&self.registry.cluster)
    }

    pub fn wire_overlay_cluster(&self, overlay: &OverlayImpl) {
        overlay.set_cluster_source(self.shared_cluster());
    }

    pub fn wire_overlay_peer_reservations(&self, overlay: &OverlayImpl) {
        overlay.set_peer_reservation_source(self.peer_reservation_source());
    }

    pub fn wire_overlay_membership_sources(&self, overlay: &OverlayImpl) {
        self.wire_overlay_cluster(overlay);
        self.wire_overlay_peer_reservations(overlay);
    }

    pub fn load_peer_reservations(&self) -> Result<bool, String> {
        xrpl_core::load_peer_reservations_from_registry(self)
    }

    pub fn logs(&self) -> Arc<AppLogs> {
        Arc::clone(&self.registry.logs)
    }

    pub fn load_monitor_journal_factory(&self) -> Arc<dyn LoadMonitorJournalFactory> {
        self.registry.load_monitor_journal_factory.clone()
    }

    pub fn config(&self) -> &AppConfig {
        &self.registry.config
    }

    pub fn standalone(&self) -> bool {
        self.registry.config.standalone
    }

    pub fn network_id(&self) -> u32 {
        self.registry.network_id_service.get_network_id()
    }

    pub fn path_search_max(&self) -> u32 {
        self.registry.config.path_search_max
    }

    pub fn relay_untrusted_validations(&self) -> bool {
        self.registry
            .config
            .relay_untrusted_validations
            .should_relay()
    }

    pub fn relay_untrusted_validations_policy(&self) -> RelayUntrustedPolicy {
        self.registry.config.relay_untrusted_validations
    }

    pub fn relay_untrusted_proposals(&self) -> bool {
        self.registry
            .config
            .relay_untrusted_proposals
            .should_relay()
    }

    pub fn relay_untrusted_proposals_policy(&self) -> RelayUntrustedPolicy {
        self.registry.config.relay_untrusted_proposals
    }

    pub fn path_search_old(&self) -> u32 {
        self.registry.config.path_search_old
    }

    pub fn path_search(&self) -> u32 {
        self.registry.config.path_search
    }

    pub fn path_search_fast(&self) -> u32 {
        self.registry.config.path_search_fast
    }

    pub fn set_path_search_levels(
        &mut self,
        path_search_old: u32,
        path_search: u32,
        path_search_fast: u32,
    ) {
        self.registry.config.path_search_old = path_search_old;
        self.registry.config.path_search = path_search;
        self.registry.config.path_search_fast = path_search_fast;
    }

    pub fn set_path_search_max(&mut self, path_search_max: u32) -> u32 {
        std::mem::replace(&mut self.registry.config.path_search_max, path_search_max)
    }

    pub fn set_relay_untrusted_validations(&mut self, relay_untrusted_validations: bool) -> bool {
        self.set_relay_untrusted_validations_policy(if relay_untrusted_validations {
            RelayUntrustedPolicy::All
        } else {
            RelayUntrustedPolicy::Trusted
        })
        .should_relay()
    }

    pub fn set_relay_untrusted_validations_policy(
        &mut self,
        relay_untrusted_validations: RelayUntrustedPolicy,
    ) -> RelayUntrustedPolicy {
        let previous = std::mem::replace(
            &mut self.registry.config.relay_untrusted_validations,
            relay_untrusted_validations,
        );
        if let Some(runtime) = self.network_ops_validation_runtime.as_ref() {
            let _ = runtime.set_relay_untrusted_validations_policy(relay_untrusted_validations);
        }
        previous
    }

    pub fn set_relay_untrusted_proposals(&mut self, relay_untrusted_proposals: bool) -> bool {
        self.set_relay_untrusted_proposals_policy(if relay_untrusted_proposals {
            RelayUntrustedPolicy::All
        } else {
            RelayUntrustedPolicy::Trusted
        })
        .should_relay()
    }

    pub fn set_relay_untrusted_proposals_policy(
        &mut self,
        relay_untrusted_proposals: RelayUntrustedPolicy,
    ) -> RelayUntrustedPolicy {
        std::mem::replace(
            &mut self.registry.config.relay_untrusted_proposals,
            relay_untrusted_proposals,
        )
    }

    pub fn node_store(&self) -> &Option<crate::shamap::shamap_store_backend::SHAMapStoreNodeStore> {
        &self.registry.node_store
    }

    /// Create a node_fetcher closure from the node store. Used by ConsensusLedgerAcceptor.
    pub fn node_fetcher_from_store(
        &self,
    ) -> Option<
        std::sync::Arc<
            dyn Fn(
                    basics::sha_map_hash::SHAMapHash,
                ) -> Option<
                    basics::memory::intrusive_pointer::SharedIntrusive<
                        shamap::nodes::tree_node::SHAMapTreeNode,
                    >,
                > + Send
                + Sync,
        >,
    > {
        // Try the local registry node_store first; fall back to the shared
        // consensus node store (Arc<RwLock>) which is populated by
        // attach_node_store after the consensus adaptor's ApplicationRoot
        // clone was created.
        let ns = self.node_store().as_ref().cloned().or_else(|| {
            self.shared_consensus_node_store
                .read()
                .ok()
                .and_then(|guard| guard.clone())
        })?;
        let node_family = self.node_family();
        Some(std::sync::Arc::new(move |hash| {
            if let Some(family) = node_family.as_ref()
                && let Some(node) = family.fetch_cached_node(hash, 0)
            {
                full_sync_debug!(
                    "[full_debug][node_fetch] source=family_cache hash={} result=hit",
                    hash
                );
                return Some(node);
            }

            let data = match &ns {
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Single(db) => db
                    .fetch_node_object(
                        hash.as_uint256(),
                        0,
                        nodestore::FetchType::Synchronous,
                        false,
                    ),
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Rotating(db) => db
                    .fetch_node_object(
                        hash.as_uint256(),
                        0,
                        nodestore::FetchType::Synchronous,
                        false,
                    ),
            };
            let Some(data) = data else {
                full_sync_debug!(
                    "[full_debug][node_fetch] source=nodestore hash={} result=miss",
                    hash
                );
                return None;
            };
            let decoded =
                shamap::nodes::tree_node::SHAMapTreeNode::make_from_prefix(data.data(), hash).ok();
            full_sync_debug!(
                "[full_debug][node_fetch] source=nodestore hash={} result={} bytes={}",
                hash,
                if decoded.is_some() {
                    "hit"
                } else {
                    "decode_fail"
                },
                data.data().len()
            );
            decoded
        }))
    }

    pub fn node_writer_result_from_store(
        &self,
    ) -> Option<
        std::sync::Arc<
            dyn Fn(
                    ledger::LedgerNodeObjectType,
                    basics::base_uint::Uint256,
                    Vec<u8>,
                    u32,
                ) -> Result<(), String>
                + Send
                + Sync,
        >,
    > {
        let ns = self.node_store().as_ref().cloned().or_else(|| {
            self.shared_consensus_node_store
                .read()
                .ok()
                .and_then(|guard| guard.clone())
        })?;
        Some(std::sync::Arc::new(
            move |object_type, hash, data, ledger_seq| match &ns {
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Single(db) => {
                    db.store(to_nodestore_type(object_type), data, hash, ledger_seq)
                }
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Rotating(db) => {
                    db.store(to_nodestore_type(object_type), data, hash, ledger_seq)
                }
            },
        ))
    }

    pub fn node_batch_writer_result_from_store(
        &self,
    ) -> Option<ledger::LedgerNodeBatchWriterResult> {
        let ns = self.node_store().as_ref().cloned().or_else(|| {
            self.shared_consensus_node_store
                .read()
                .ok()
                .and_then(|guard| guard.clone())
        })?;
        Some(std::sync::Arc::new(move |writes| {
            let objects = writes
                .into_iter()
                .map(|write| {
                    (
                        to_nodestore_type(write.object_type),
                        write.data,
                        write.hash,
                        write.ledger_seq,
                    )
                })
                .collect();
            match &ns {
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Single(db) => {
                    db.store_batch(objects)
                }
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Rotating(db) => {
                    db.store_batch(objects)
                }
            }
        }))
    }

    pub fn node_writer_from_store(
        &self,
    ) -> Option<
        std::sync::Arc<
            dyn Fn(ledger::LedgerNodeObjectType, basics::base_uint::Uint256, Vec<u8>, u32)
                + Send
                + Sync,
        >,
    > {
        // Try the local registry node_store first; fall back to the shared
        // consensus node store (Arc<RwLock>) which is populated by
        // attach_node_store after the consensus adaptor's ApplicationRoot
        // clone was created. This mirrors node_fetcher_from_store's fallback.
        let ns = self.node_store().as_ref().cloned().or_else(|| {
            self.shared_consensus_node_store
                .read()
                .ok()
                .and_then(|guard| guard.clone())
        })?;
        Some(std::sync::Arc::new(
            move |object_type, hash, data, ledger_seq| {
                let result = match &ns {
                    crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Single(db) => {
                        db.store(to_nodestore_type(object_type), data, hash, ledger_seq)
                    }
                    crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Rotating(db) => {
                        db.store(to_nodestore_type(object_type), data, hash, ledger_seq)
                    }
                };
                if let Err(error) = result {
                    tracing::error!(target: "nodestore", %error, "Failed to persist SHAMap node");
                }
            },
        ))
    }

    pub fn attach_node_store(
        &mut self,
        node_store: Option<crate::shamap::shamap_store_backend::SHAMapStoreNodeStore>,
    ) -> Option<crate::shamap::shamap_store_backend::SHAMapStoreNodeStore> {
        // Also populate the shared consensus node store so ConsensusLedgerAcceptor
        // can access it (it was created before the node store was attached).
        if let Some(ref ns) = node_store {
            if let Ok(mut guard) = self.shared_consensus_node_store.write() {
                *guard = Some(ns.clone());
            }
        }
        let previous = std::mem::replace(&mut self.registry.node_store, node_store);
        self.refresh_validation_ledger_lookup_runtime();
        self.refresh_ledger_persistence_runtime();
        previous
    }

    pub fn relational_database(
        &self,
    ) -> &Option<Arc<crate::shamap::shamap_store_relational::SqliteSHAMapStoreRelational>> {
        &self.registry.relational_database
    }

    pub fn attach_relational_database(
        &mut self,
        relational_database: Option<
            Arc<crate::shamap::shamap_store_relational::SqliteSHAMapStoreRelational>,
        >,
    ) -> Option<Arc<crate::shamap::shamap_store_relational::SqliteSHAMapStoreRelational>> {
        let previous =
            std::mem::replace(&mut self.registry.relational_database, relational_database);
        self.refresh_validation_ledger_lookup_runtime();
        self.refresh_ledger_persistence_runtime();
        previous
    }

    pub fn attach_ledger_db(
        &mut self,
        ledger_db: Option<std::sync::Arc<rdb::LedgerDb>>,
    ) -> Option<std::sync::Arc<rdb::LedgerDb>> {
        let previous = std::mem::replace(&mut self.registry.ledger_db, ledger_db);
        self.refresh_ledger_persistence_runtime();
        previous
    }

    /// Return a reference to the ledger header database, if open.
    pub fn ledger_db(&self) -> Option<&std::sync::Arc<rdb::LedgerDb>> {
        self.registry.ledger_db.as_ref()
    }

    fn refresh_ledger_persistence_runtime(&self) {
        let failed_save_handler = self.ledger_master_runtime().map(|runtime| {
            let ledger_master = runtime.ledger_master();
            let inbound_ledgers = Arc::clone(&runtime.inbound_ledgers);
            Arc::new(move |seq: u32, hash: SHAMapHash| {
                // Mirrors LedgerMaster::failedSave: a queue-admitted save that
                // later fails must retract its complete-ledger claim and
                // reacquire the exact hash, never a sequence-selected fork.
                ledger_master.clear_ledger(seq);
                if let Ok(guard) = inbound_ledgers.lock()
                    && let Some(inbound) = guard.as_ref()
                {
                    inbound.acquire_async(
                        *hash.as_uint256(),
                        seq,
                        crate::ledger::inbound_ledgers::AcquireReason::Generic,
                    );
                }
            }) as Arc<dyn Fn(u32, SHAMapHash) + Send + Sync>
        });
        let runtime = Arc::new(
            crate::AppLedgerPersistenceRuntime::with_job_queue_and_failed_save_handler(
                self.registry.relational_database.clone(),
                self.registry.node_store.clone(),
                Arc::clone(&self.transaction_master),
                self.registry.network_id_service.get_network_id(),
                self.registry.ledger_db.clone(),
                Some(Arc::clone(&self.job_queue)),
                failed_save_handler,
            ),
        );
        *self
            .ledger_persistence_runtime
            .write()
            .expect("ledger persistence runtime lock must not be poisoned") = runtime;
    }

    pub fn build_ledger_persistence_runtime(&self) -> Arc<crate::AppLedgerPersistenceRuntime> {
        Arc::clone(
            &self
                .ledger_persistence_runtime
                .read()
                .expect("ledger persistence runtime lock must not be poisoned"),
        )
    }

    pub fn node_store_scheduler(&self) -> &NodeStoreScheduler {
        &self.node_store_scheduler
    }

    pub fn time_keeper(&self) -> &TimeKeeper<SystemTimeKeeperClock> {
        self.time_keeper.as_ref()
    }

    pub fn shared_time_keeper(&self) -> Arc<TimeKeeper<SystemTimeKeeperClock>> {
        Arc::clone(&self.time_keeper)
    }

    /// Initialise the optional SNTP worker. Its TimeKeeper callback and
    /// worker handle remain application-owned until MainRuntime shutdown.
    pub fn start_sntp_client(&mut self, servers: Vec<String>) {
        if servers.is_empty() || self.sntp_client.is_some() {
            return;
        }
        let client = crate::state::sntp::SntpClient::new(self.registry.logs.journal("sntp"));
        let time_keeper = Arc::clone(&self.time_keeper);
        match client.start(servers, move |offset| time_keeper.set_sntp_offset(offset)) {
            Ok(()) => self.sntp_client = Some(client),
            Err(error) => tracing::warn!(target: "sntp", %error, "SNTP client did not start"),
        }
    }

    /// Stop and join the SNTP worker before the application-owned TimeKeeper
    /// and its runtime resources are torn down.
    pub fn stop_sntp_client(&self) {
        if let Some(client) = self.sntp_client.as_ref() {
            client.stop();
        }
    }

    pub fn stop_tree(&self) -> &StopTree {
        &self.stop_tree
    }

    pub fn node_family(&self) -> Option<Arc<dyn NodeFamilyRuntime>> {
        self.node_family.as_ref().map(Arc::clone)
    }

    pub fn resolver_runtime(&self) -> Option<Arc<AppResolverRuntime>> {
        self.resolver_runtime.as_ref().map(Arc::clone)
    }

    pub fn overlay_runtime(&self) -> Option<Arc<AppOverlayRuntime>> {
        self.overlay_runtime.as_ref().map(Arc::clone)
    }

    pub fn attach_node_family(
        &mut self,
        node_family: Arc<dyn NodeFamilyRuntime>,
    ) -> Option<Arc<dyn NodeFamilyRuntime>> {
        self.node_family.replace(node_family)
    }

    /// Attach the shared tree-node cache. Called by main.rs after creating
    /// the cache that is shared between `SHAMapFamily` and `InboundLedgers`.
    /// The cache reference is used by `persist_dirty_nodes_to_store` to
    /// canonicalize flushed nodes (matching rippled's `SHAMap::writeNode`
    /// → `canonicalize` + `db().store()` two-step pattern).
    pub fn attach_shared_tree_cache(
        &self,
        cache: Arc<TreeNodeCache<MonotonicClock, basics::hardened_hash::HardenedHashBuilder>>,
    ) {
        let _ = self.shared_tree_cache.set(cache);
    }

    /// Returns a reference to the shared tree-node cache, if attached.
    pub fn shared_tree_cache(
        &self,
    ) -> Option<&TreeNodeCache<MonotonicClock, basics::hardened_hash::HardenedHashBuilder>> {
        self.shared_tree_cache.get().map(|arc| arc.as_ref())
    }

    /// Returns the Arc to the shared tree-node cache, if attached.
    /// Used by InboundLedgers to share the same bounded cache as the NodeFamily.
    pub fn shared_tree_cache_arc(
        &self,
    ) -> Option<&Arc<TreeNodeCache<MonotonicClock, basics::hardened_hash::HardenedHashBuilder>>>
    {
        self.shared_tree_cache.get()
    }

    /// Returns the concrete FullBelow cache retained by the NodeFamily. The
    /// bootstrap path requires this value and never constructs a second cache
    /// for inbound acquisition.
    pub fn node_family_full_below_cache(&self) -> Option<crate::NodeFamilyFullBelowCache> {
        self.node_family()
            .and_then(|node_family| node_family.owned_full_below_cache())
    }

    /// Returns the current entry count of the NodeFamily-owned full-below
    /// cache. It is intentionally not cached on ApplicationRoot.
    pub fn full_below_cache_size(&self) -> usize {
        self.node_family_full_below_cache()
            .map(|cache| cache.size())
            .unwrap_or(0)
    }

    pub fn attach_resolver_runtime(
        &mut self,
        resolver_runtime: Arc<AppResolverRuntime>,
    ) -> Option<Arc<AppResolverRuntime>> {
        self.runtime_bindings.resolver = Some(resolver_runtime.clone());
        self.resolver_runtime.replace(resolver_runtime)
    }

    pub fn attach_default_resolver_runtime(&mut self) -> Arc<AppResolverRuntime> {
        if let Some(runtime) = self.resolver_runtime() {
            return runtime;
        }

        let runtime = Arc::new(AppResolverRuntime::default());
        let _ = self.attach_resolver_runtime(Arc::clone(&runtime));
        runtime
    }

    pub fn overlay_status(&self) -> Option<Arc<dyn OverlayStatusSource>> {
        self.overlay_status.as_ref().map(Arc::clone)
    }

    pub fn attach_overlay_status(
        &mut self,
        overlay_status: Arc<dyn OverlayStatusSource>,
    ) -> Option<Arc<dyn OverlayStatusSource>> {
        self.overlay_status.replace(overlay_status)
    }

    pub fn manifest_limits(&self) -> ManifestLimits {
        self.manifest_limits
    }

    pub fn configure_manifest_limits(&mut self, manifest_limits: ManifestLimits) {
        self.registry
            .validator_manifest_cache
            .set_max_untrusted_count(manifest_limits.max_untrusted_count);
        self.registry
            .publisher_manifest_cache
            .set_max_untrusted_count(manifest_limits.max_untrusted_count);
        self.manifest_limits = manifest_limits;
    }

    pub fn attach_overlay_runtime(
        &mut self,
        overlay_runtime: Arc<AppOverlayRuntime>,
    ) -> Option<Arc<AppOverlayRuntime>> {
        let overlay = overlay_runtime.overlay();
        let manifest_limits = self.manifest_limits;
        overlay.set_max_manifests_message_size(manifest_limits.maximum_message_size());
        let ledger_master_state = Arc::clone(&self.ledger_master_state);
        overlay.set_validated_ledger_status_provider(move || {
            ledger_master_state
                .validated_ledger_seq()
                .map(|sequence| (sequence, ledger_master_state.validated_ledger_age()))
        });
        let manifests = Arc::clone(&self.registry.validator_manifest_cache);
        let validators = self.validators();
        overlay.set_manifests_message_provider(move || {
            const MAX_MANIFEST_BYTES: usize = 358;
            let mut trusted = Vec::new();
            let mut untrusted = Vec::new();
            for serialized in manifests.serialized_manifests() {
                if serialized.len() > MAX_MANIFEST_BYTES {
                    continue;
                }
                let Some(manifest) = crate::state::manifest::deserialize_manifest(&serialized)
                else {
                    continue;
                };
                if validators.listed(manifest.master_key) {
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
            let list = trusted
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
        self.wire_overlay_membership_sources(overlay.as_ref());
        if let Some(closed_ledger) = self.closed_ledger() {
            overlay.set_handshake_ledgers(
                *closed_ledger.header().hash.as_uint256(),
                *closed_ledger.header().parent_hash.as_uint256(),
            );
        }
        let overlay_status: Arc<dyn OverlayStatusSource> = overlay;
        self.overlay_status = Some(overlay_status);
        self.runtime_bindings.overlay = Some(overlay_runtime.clone());
        // Provide the overlay to the validations adaptor so it can resolve
        // ledger sequence numbers from peers on acquisition cache misses.
        self.validations
            .set_overlay(Some(overlay_runtime.overlay()));
        self.overlay_runtime.replace(overlay_runtime)
    }

    pub fn attach_configured_overlay_runtime(
        &mut self,
        config: &basics::basic_config::BasicConfig,
        handoff: Arc<dyn OverlayHandoff>,
    ) -> Result<Arc<AppOverlayRuntime>, String> {
        let runtime = build_overlay_runtime(
            config,
            self.server_ports_setup.as_deref(),
            handoff,
            Some(self.network_ops_mode_owner()),
            Some(Arc::clone(&self.status_rpc_state)),
        )?;
        self.registry.network_id_service =
            FixedNetworkIdService::new(runtime.network_id().unwrap_or(0));
        if let Some(validation_runtime) = self.network_ops_validation_runtime.as_ref() {
            let _ = validation_runtime
                .set_network_id(self.registry.network_id_service.get_network_id());
        }
        let _ = self.attach_overlay_runtime(Arc::clone(&runtime));
        Ok(runtime)
    }

    pub fn load_cluster_nodes_from_config(
        &self,
        config: &basics::basic_config::BasicConfig,
    ) -> Result<bool, String> {
        let entries = config.section("cluster_nodes").values();
        if entries.is_empty() {
            return Ok(false);
        }
        if self.shared_cluster().load(entries) {
            Ok(true)
        } else {
            Err("Invalid entry in cluster configuration.".to_owned())
        }
    }

    pub fn attach_default_node_family(&mut self) -> Arc<dyn NodeFamilyRuntime> {
        if let Some(node_family) = self.node_family() {
            return node_family;
        }

        let profile =
            crate::NodeSizeResourceProfile::for_node_size(self.status_rpc_node_size().as_deref());
        let tree_node_cache = Arc::new(TreeNodeCache::new(
            "app-bootstrap-node-family",
            profile.tree_cache_size,
            Duration::seconds(profile.tree_cache_age_seconds),
            MonotonicClock::default(),
        ));
        self.attach_shared_tree_cache(Arc::clone(&tree_node_cache));
        let family: Arc<dyn NodeFamilyRuntime> =
            Arc::new(NodeFamily::new_with_owned_full_below_cache(
                tree_node_cache,
                1,
                profile.full_below_target_size,
                Duration::seconds(profile.full_below_expiration_seconds),
                NullNodeFetcher,
                NullMissingNodeReporter,
            ));
        let _ = self.attach_node_family(Arc::clone(&family));
        let _ = self.wire_node_family_reset();
        family
    }

    pub fn server_ports_setup(&self) -> Option<Arc<ServerPortsSetup>> {
        self.server_ports_setup.as_ref().map(Arc::clone)
    }

    pub fn attach_server_ports_setup(
        &mut self,
        server_ports_setup: Arc<ServerPortsSetup>,
    ) -> Option<Arc<ServerPortsSetup>> {
        self.server_ports_setup.replace(server_ports_setup)
    }

    pub fn attach_server_ports_from_config(
        &mut self,
        config: &basics::basic_config::BasicConfig,
        standalone: bool,
    ) -> Result<bool, String> {
        if self.server_ports_setup.is_some() {
            return Ok(false);
        }
        if !config.exists("server") {
            return Ok(false);
        }

        let setup = Arc::new(build_server_ports_setup(config, standalone)?);
        let _ = self.attach_server_ports_setup(setup);
        Ok(true)
    }

    pub fn published_server_ports(&self) -> Option<Arc<dyn PublishedServerPortsSource>> {
        if let Some(setup) = self.server_ports_setup.as_ref() {
            return Some(Arc::clone(setup) as Arc<dyn PublishedServerPortsSource>);
        }
        self.published_server_ports.as_ref().map(Arc::clone)
    }

    pub fn attach_published_server_ports(
        &mut self,
        published_server_ports: Arc<dyn PublishedServerPortsSource>,
    ) -> Option<Arc<dyn PublishedServerPortsSource>> {
        self.published_server_ports.replace(published_server_ports)
    }

    pub fn status_metrics(&self) -> Option<Arc<dyn StatusMetricsSource>> {
        if let Some(status_metrics) = self.status_metrics.as_ref() {
            return Some(Arc::clone(status_metrics));
        }

        self.registry
            .perf_log
            .as_ref()
            .map(|perf_log| Arc::clone(perf_log) as Arc<dyn StatusMetricsSource>)
    }

    pub fn attach_status_metrics(
        &mut self,
        status_metrics: Arc<dyn StatusMetricsSource>,
    ) -> Option<Arc<dyn StatusMetricsSource>> {
        self.status_metrics.replace(status_metrics)
    }

    pub fn node_identity(&self) -> Option<(PublicKey, SecretKey)> {
        self.node_identity
            .as_ref()
            .map(|(public, secret)| (*public, secret.clone()))
    }

    pub const fn validation_public_key(&self) -> Option<PublicKey> {
        self.validation_public_key
    }

    pub fn set_max_disallowed_ledger(&self, seq: u32) {
        use std::sync::atomic::Ordering;
        self.max_disallowed_ledger.store(seq, Ordering::Release);
    }

    pub fn max_disallowed_ledger(&self) -> u32 {
        use std::sync::atomic::Ordering;
        self.max_disallowed_ledger.load(Ordering::Acquire)
    }

    pub fn network_ops_state(&self) -> Arc<SharedNetworkOpsState> {
        Arc::clone(&self.network_ops_state)
    }

    pub fn ledger_master_state(&self) -> Arc<SharedLedgerMasterState> {
        Arc::clone(&self.ledger_master_state)
    }

    pub fn ledger_master_runtime(&self) -> Option<Arc<AppLedgerMasterRuntime>> {
        self.ledger_master_runtime.as_ref().map(Arc::clone)
    }

    pub fn set_ledger_delta_publisher(
        &mut self,
        publisher: impl Fn(protocol::JsonValue) + Send + Sync + 'static,
    ) {
        self.ledger_delta_publisher = Some(Arc::new(publisher));
    }

    pub fn set_ledger_close_publisher(
        &mut self,
        publisher: impl Fn(protocol::JsonValue) + Send + Sync + 'static,
    ) {
        self.ledger_close_publisher = Some(Arc::new(publisher));
    }

    pub fn set_transaction_publisher(
        &mut self,
        publisher: impl Fn(protocol::JsonValue) + Send + Sync + 'static,
    ) {
        self.transaction_publisher = Some(Arc::new(publisher));
    }

    /// Set a generic subscription publisher (stream_name, payload) → push to WS subscribers.
    /// Called by the server crate after binding HTTP/WS listeners.
    pub fn set_subscription_publisher(
        &self,
        publisher: impl Fn(&str, protocol::JsonValue) + Send + Sync + 'static,
    ) {
        if let Ok(mut guard) = self.shared_subscription_manager.write() {
            *guard = Some(Arc::new(publisher));
        }
    }

    /// Publish an applied open-ledger transaction to the real-time proposed
    /// stream. Accepted transaction publication remains owned by
    /// `on_published_ledger`, which emits only after validation/publication.
    pub fn publish_proposed_transaction(
        &self,
        transaction: &SharedTransaction,
        result: Ter,
    ) -> bool {
        let stx = Arc::clone(
            transaction
                .lock()
                .expect("transaction mutex must not be poisoned")
                .get_s_transaction(),
        );
        // Match `NetworkOPsImp::pubProposedTransaction`: inner Batch entries
        // are implementation details of their outer transaction and are never
        // exposed to client streams.
        if stx.is_flag(tfInnerBatchTxn) {
            return false;
        }

        let publisher = self
            .shared_subscription_manager
            .read()
            .ok()
            .and_then(|guard| guard.as_ref().cloned());
        let Some(publisher) = publisher else {
            return false;
        };
        let payload = std::collections::BTreeMap::from([
            (
                "type".to_owned(),
                JsonValue::String("transaction".to_owned()),
            ),
            (
                "status".to_owned(),
                JsonValue::String("proposed".to_owned()),
            ),
            (
                "ledger_current_index".to_owned(),
                JsonValue::Unsigned(u64::from(self.open_ledger().current().ledger_current_index)),
            ),
            (
                "hash".to_owned(),
                JsonValue::String(stx.get_transaction_id().to_string()),
            ),
            ("transaction".to_owned(), stx.json(JsonOptions::NONE)),
            (
                "engine_result".to_owned(),
                JsonValue::String(protocol::trans_token(result).to_owned()),
            ),
            (
                "engine_result_code".to_owned(),
                JsonValue::Signed(i64::from(result.to_int())),
            ),
            (
                "engine_result_message".to_owned(),
                JsonValue::String(protocol::trans_human(result).to_owned()),
            ),
            ("validated".to_owned(), JsonValue::Bool(false)),
        ]);
        publisher("transactions_proposed", JsonValue::Object(payload));
        true
    }

    /// Schedule rippled's `NetworkOPs::reportFeeChange` server-stream
    /// notification only when its ServerFeeSummary equivalent changed. Callers
    /// invoke this after the shared open ledger has been rebuilt, because the
    /// summary reflects its new fee and TxQ metrics.
    pub fn report_fee_change(&self) -> bool {
        self.fee_change_reporter.report_fee_change()
    }

    pub fn validations(&self) -> &SharedAppValidations<SystemTimeKeeperClock> {
        &self.validations
    }

    fn refresh_validation_ledger_lookup_runtime(&self) {
        let lookup_runtime = self.ledger_master_runtime().map(|runtime| {
            Arc::new(
                crate::ledger::loaded_ledger_runtime::AppLoadedLedgerRuntime::with_sources_and_ledger_master_state(
                    runtime.ledger_master(),
                    self.relational_database().clone(),
                    self.node_store().clone(),
                    Some(Arc::clone(&self.ledger_master_state)),
                ),
            )
        });
        self.validations.set_loaded_ledger_runtime(lookup_runtime);
    }

    pub fn attach_ledger_master_runtime(
        &mut self,
        ledger_master_runtime: Arc<AppLedgerMasterRuntime>,
    ) -> Option<Arc<AppLedgerMasterRuntime>> {
        if let Some(runtime) = self.network_ops_runtime.as_ref() {
            let _ = runtime.set_ledger_master_runtime(Arc::clone(&ledger_master_runtime));
        }
        self.validations.set_job_queue(Some(self.job_queue.clone()));
        let _ = self
            .validations
            .set_ledger_master_runtime(Some(Arc::clone(&ledger_master_runtime)));
        let previous = self.ledger_master_runtime.replace(ledger_master_runtime);
        self.refresh_validation_ledger_lookup_runtime();
        self.refresh_ledger_persistence_runtime();
        previous
    }

    pub fn attach_default_ledger_master_runtime(&mut self) -> Arc<AppLedgerMasterRuntime> {
        if let Some(runtime) = self.ledger_master_runtime() {
            return runtime;
        }

        let runtime = Arc::new(AppLedgerMasterRuntime::default());
        let _ = self.attach_ledger_master_runtime(Arc::clone(&runtime));
        runtime
    }

    pub fn network_ops_runtime(&self) -> Option<Arc<AppNetworkOpsRuntime>> {
        self.network_ops_runtime.as_ref().map(Arc::clone)
    }

    pub fn attach_network_ops_runtime(
        &mut self,
        network_ops_runtime: Arc<AppNetworkOpsRuntime>,
    ) -> Option<Arc<AppNetworkOpsRuntime>> {
        // Populate shared reference so JtAccept jobs can access it.
        if let Ok(mut guard) = self.shared_network_ops_rt.write() {
            *guard = Some(Arc::clone(&network_ops_runtime));
        }
        let previous = self.network_ops_runtime.replace(network_ops_runtime);

        // Match ConsensusTransSetSF::gotNode -> NetworkOPs::submitTransaction.
        // Remove the lifecycle owner before cloning so the callback's root
        // does not own the adapter that owns the callback (a strong cycle).
        if let Some(submit_adapter) = self.consensus_tx_set_submit_adapter.take() {
            let submit_root = self.clone();
            let submit_job_queue = self.job_queue.clone();
            submit_adapter.install(Arc::new(move |transaction| {
                // rippled's filter does not call NetworkOPs on the SHAMap
                // acquisition thread. It first posts `TxsToTxn` as a
                // JtTransaction job; `submitTransaction` then validates and
                // posts the normal `SubmitTxn` processing job. Preserve both
                // queue boundaries so acquisition lock ownership, ordering,
                // and load accounting stay identical.
                let transaction_root = submit_root.clone();
                let _ = submit_job_queue.add_job(
                    crate::job::job_types::JobType::JtTransaction,
                    "TxsToTxn",
                    move || {
                        let _ = transaction_root.submit_transaction_to_network_ops(transaction);
                    },
                );
            }));
            let weak_submit_adapter = Arc::downgrade(&submit_adapter);
            self.register_stop_callback("consensus-tx-set-submit", move || {
                if let Some(submit_adapter) = weak_submit_adapter.upgrade() {
                    submit_adapter.disable();
                }
            });
            // `attach_network_ops_runtime` can race shutdown. If StopTree
            // completed between callback installation and registration, the
            // newly registered child will not be visited by that completed
            // traversal. A final state check closes that window; if shutdown
            // begins afterward, the registered callback owns the disable.
            if self.is_stopping() {
                submit_adapter.disable();
            }
            self.consensus_tx_set_submit_adapter = Some(submit_adapter);
        }

        previous
    }

    pub fn network_ops_validation_runtime(&self) -> Option<Arc<AppNetworkOpsValidationRuntime>> {
        self.network_ops_validation_runtime.as_ref().map(Arc::clone)
    }

    pub fn consensus_runtime(&self) -> Option<Arc<AppConsensusRuntime>> {
        self.consensus_runtime.as_ref().map(Arc::clone)
    }

    pub fn attach_network_ops_validation_runtime(
        &mut self,
        network_ops_validation_runtime: Arc<AppNetworkOpsValidationRuntime>,
    ) -> Option<Arc<AppNetworkOpsValidationRuntime>> {
        self.network_ops_validation_runtime
            .replace(network_ops_validation_runtime)
    }

    pub fn attach_default_network_ops_validation_runtime(
        &mut self,
    ) -> Arc<AppNetworkOpsValidationRuntime> {
        if let Some(runtime) = self.network_ops_validation_runtime() {
            return runtime;
        }

        let runtime = Arc::new(AppNetworkOpsValidationRuntime::from_application_root(self));
        let _ = self.attach_network_ops_validation_runtime(Arc::clone(&runtime));
        runtime
    }

    pub fn attach_default_network_ops_runtime(&mut self) -> Arc<AppNetworkOpsRuntime> {
        if let Some(runtime) = self.network_ops_runtime() {
            return runtime;
        }

        let ledger_master_runtime = self.attach_default_ledger_master_runtime();
        let runtime = Arc::new(AppNetworkOpsRuntime::new(
            self.network_ops_state(),
            ledger_master_runtime,
            Arc::clone(&self.registry.hash_router),
            Arc::clone(&self.transaction_master),
            Arc::clone(&self.ledger_master_state),
            self.shared_time_keeper(),
        ));
        let _ = self.attach_network_ops_runtime(Arc::clone(&runtime));
        runtime
    }

    pub fn network_ops_mode_owner(&self) -> AppNetworkOpsModeOwner {
        let ledger_master_state = Arc::clone(&self.ledger_master_state);
        AppNetworkOpsModeOwner::new(
            self.network_ops_state(),
            Arc::new(move || ledger_master_state.validated_ledger_age()),
        )
    }

    pub fn bind_default_component_runtimes(&mut self) {
        if self.runtime_bindings.nodestore.is_none() {
            if let Some(node_store) = self.registry.node_store.as_ref().cloned() {
                let _ = self.bind_nodestore(Arc::new(AppNodeStoreRuntime::new(node_store)));
            }
        }

        if self.runtime_bindings.ledger.is_none() {
            let ledger_master_runtime = self.attach_default_ledger_master_runtime();
            let network_ops_runtime = self.network_ops_runtime();
            let _ = self.bind_ledger(Arc::new(AppLedgerRuntime::new(
                Arc::clone(&self.registry.ledger_cleaner),
                Arc::clone(&self.registry.inbound_ledgers),
                Arc::clone(&self.registry.inbound_transactions),
                Arc::clone(&self.registry.ledger_replayer),
                self.clone(),
                ledger_master_runtime,
                network_ops_runtime,
            )));
        }

        if self.runtime_bindings.consensus.is_none() {
            let _ = self.attach_default_consensus_runtime();
        }

        if self.runtime_bindings.validator_site.is_none() {
            self.runtime_bindings.validator_site =
                Some(Arc::new(AppValidatorSiteRuntime::new(self.clone())));
        }

        if self.runtime_bindings.perf_log.is_none() {
            if let Some(perf_log) = self.registry.perf_log.as_ref().cloned() {
                self.runtime_bindings.perf_log = Some(Arc::new(AppPerfLogRuntime::new(perf_log)));
            }
        }
    }

    pub fn attach_default_consensus_runtime(&mut self) -> Arc<AppConsensusRuntime> {
        if let Some(runtime) = self.consensus_runtime.as_ref() {
            return Arc::clone(runtime);
        }

        let _network_ops_runtime = self.attach_default_network_ops_runtime();
        let ledger_master_runtime = self.attach_default_ledger_master_runtime();

        use crate::consensus::rcl_consensus::{
            AppConsensus, AppRclConsensusAdaptor, AppRclConsensusOptions, AppRclConsensusRelay,
            NullRclConsensusJournal,
        };

        let validator_token_lines: Option<&[String]> = self.config().validator_token.as_deref();

        let relay = AppRclConsensusRelay::from_application_root(
            self,
            self.registry.inbound_transactions.clone(),
            crate::validator::validator_keys::ValidatorKeys::from_sources(
                self.config().validation_seed.as_deref(),
                validator_token_lines,
            ),
            NullRclConsensusJournal,
        );

        let adaptor = AppRclConsensusAdaptor::new(
            AppRclConsensusOptions {
                standalone: self.standalone(),
                ..Default::default()
            },
            self.shared_time_keeper(),
            ledger_master_runtime,
            self.registry.open_ledger.clone(),
            self.validations.clone(),
            self.validators.clone(),
            self.network_ops_mode_owner(),
            self.clone_ledger_acceptor(),
            self.registry.inbound_transactions.clone(),
            self.transaction_master.clone(),
            relay,
            NullRclConsensusJournal,
            crate::validator::validator_keys::ValidatorKeys::from_sources(
                self.config().validation_seed.as_deref(),
                validator_token_lines,
            ),
            Some(Arc::new(crate::load::fee_vote::FeeVote::new(
                self.fee_vote_setup,
                crate::load::fee_vote::NullFeeVoteJournal,
            ))),
            {
                // Create NegativeUNLVote if we have validator keys (matching
                // rippled's Application::setup which instantiates
                // negativeUNLVote_ from the local validator identity).
                let vk = crate::validator::validator_keys::ValidatorKeys::from_sources(
                    self.config().validation_seed.as_deref(),
                    validator_token_lines,
                );
                vk.keys.map(|keys| {
                    Arc::new(crate::amendments::negative_unl_vote::NegativeUNLVote::new(
                        calc_node_id(&keys.public_key),
                        crate::amendments::negative_unl_vote::NullNegativeUNLVoteJournal,
                    ))
                })
            },
            Some(self.amendment_status.clone()),
            self.overlay_runtime().map(|rt| rt.overlay().clone()),
            self.clone(),
        );

        let runner = AppConsensus::new(adaptor, consensus::ConsensusParms::default());
        let runtime = Arc::new(AppConsensusRuntime::new());
        runtime.set_runner(runner);

        let _ = self.bind_consensus(runtime.clone());
        self.consensus_runtime = Some(runtime.clone());
        // Populate shared reference so JtAccept jobs (which hold an
        // older clone of ApplicationRoot) can access the consensus runtime.
        if let Ok(mut guard) = self.shared_consensus_rt.write() {
            *guard = Some(runtime.clone());
        }
        runtime
    }

    pub fn submit_transaction_to_network_ops(
        &self,
        transaction: Arc<protocol::STTx>,
    ) -> Option<AppNetworkOpsSubmitReport> {
        let runtime = self.network_ops_runtime.as_ref()?.clone();
        let queued_runtime = Arc::clone(&runtime);
        let batch_root = self.clone();
        let job_queue = self.job_queue.clone();

        Some(
            runtime.submit_transaction(transaction, move |queued_transaction| {
                let runtime = Arc::clone(&queued_runtime);
                job_queue.add_job(
                    crate::job::job_types::JobType::JtTransaction,
                    "SubmitTxn",
                    move || {
                        let mut transaction = Arc::clone(&queued_transaction);
                        let _ = runtime.process_transaction(
                            &mut transaction,
                            false,
                            false,
                            false,
                            || batch_root.enqueue_network_ops_transaction_batch(),
                            || {},
                        );
                    },
                )
            }),
        )
    }

    pub fn network_ops_pending_transaction_count(&self) -> Option<usize> {
        self.network_ops_runtime
            .as_ref()
            .map(|runtime| runtime.pending_transaction_count())
    }

    pub fn network_ops_pending_validation_count(&self) -> Option<usize> {
        self.network_ops_validation_runtime
            .as_ref()
            .map(|runtime| runtime.pending_validation_count())
    }

    pub fn network_ops_submit_held_count(&self) -> Option<usize> {
        self.network_ops_runtime
            .as_ref()
            .map(|runtime| runtime.submit_held_count())
    }

    pub fn promote_included_transaction_to_network_ops(
        &self,
        transaction: &SharedTransaction,
    ) -> Option<usize> {
        self.network_ops_runtime
            .as_ref()
            .map(|runtime| runtime.promote_included_transaction(transaction))
    }

    pub fn apply_held_transactions_to_network_ops(
        &self,
        next_open_ledger_parent_hash: SHAMapHash,
        run_sync_batch: impl FnMut(crate::NetworkOpsProcessSetOwnerSync),
    ) -> Option<AppNetworkOpsApplyHeldOutcome> {
        self.network_ops_runtime.as_ref().map(|runtime| {
            runtime.apply_held_transactions_to_queue(next_open_ledger_parent_hash, run_sync_batch)
        })
    }

    /// Broadcast a consensus StatusChange with the same event downgrade and
    /// range/time payload that rippled's RCLConsensus::Adaptor::notify uses.
    pub(crate) fn broadcast_consensus_status_change(
        &self,
        ledger: &Ledger,
        event: i32,
        have_correct_lcl: bool,
    ) {
        let Some(overlay_rt) = self.overlay_runtime() else {
            return;
        };

        use overlay::Overlay;
        let (first_seq, last_seq) = self
            .ledger_master_runtime()
            .and_then(|runtime| runtime.ledger_master().full_validated_range())
            .map(|full_range| {
                let fetch_floor = self.earliest_ledger_fetch(self.ledger_fetch_depth);
                advertised_ledger_range(full_range, self.minimum_online_seq(), fetch_floor)
            })
            .unwrap_or((0, 0));
        let header = ledger.header();
        let status = overlay::ProtocolMessage::new(overlay::ProtocolPayload::StatusChange(
            overlay::message::wire::TmStatusChange {
                new_status: None,
                // rippled sends LOST_SYNC, rather than the requested event,
                // whenever consensus was operating on the wrong LCL.
                new_event: Some(consensus_status_event(event, have_correct_lcl)),
                ledger_seq: Some(header.seq),
                ledger_hash: Some(header.hash.as_uint256().data().to_vec()),
                ledger_hash_previous: Some(header.parent_hash.as_uint256().data().to_vec()),
                network_time: Some(self.shared_time_keeper().now().as_seconds() as u64),
                first_seq: Some(first_seq),
                last_seq: Some(last_seq),
            },
        ));
        overlay_rt.overlay().broadcast(&status);
    }

    pub fn apply_network_ops_pending_with<RelaySkip>(
        &self,
        current_ledger_index: u32,
        validated_ledger_index: Option<u32>,
        apply_tx: impl FnMut(&SharedTransaction, tx::ApplyFlags) -> tx::ApplyResult,
        report_fee_change: impl FnMut(),
        publish_proposed: impl FnMut(&SharedTransaction, protocol::Ter),
        set_bad_flag: impl FnMut(&SharedTransaction),
        set_held_flag: impl FnMut(&SharedTransaction) -> bool,
        should_relay: impl FnMut(&SharedTransaction) -> Option<RelaySkip>,
        relay: impl FnMut(&SharedTransaction, bool, RelaySkip),
        current_ledger_state: impl FnMut(
            &SharedTransaction,
        ) -> crate::NetworkOpsCurrentLedgerState<
            protocol::XRPAmount,
            u32,
        >,
    ) -> Option<AppNetworkOpsApplyReport> {
        self.network_ops_runtime.as_ref().and_then(|runtime| {
            runtime.apply_pending_with(
                current_ledger_index,
                validated_ledger_index,
                apply_tx,
                report_fee_change,
                publish_proposed,
                set_bad_flag,
                set_held_flag,
                should_relay,
                relay,
                current_ledger_state,
            )
        })
    }

    pub fn apply_network_ops_pending_batch_with<RelaySkip>(
        &self,
        current_ledger_index: u32,
        validated_ledger_index: Option<u32>,
        apply_batch: impl FnOnce(
            &mut [crate::network::network_ops_runtime::AppNetworkOpsPendingTransaction],
        ) -> bool,
        report_fee_change: impl FnMut(),
        publish_proposed: impl FnMut(&SharedTransaction, protocol::Ter),
        set_bad_flag: impl FnMut(&SharedTransaction),
        set_held_flag: impl FnMut(&SharedTransaction) -> bool,
        should_relay: impl FnMut(&SharedTransaction) -> Option<RelaySkip>,
        relay: impl FnMut(&SharedTransaction, bool, RelaySkip),
        current_ledger_state: impl FnMut(
            &SharedTransaction,
        ) -> crate::NetworkOpsCurrentLedgerState<
            protocol::XRPAmount,
            u32,
        >,
    ) -> Option<AppNetworkOpsApplyReport> {
        self.network_ops_runtime.as_ref().and_then(|runtime| {
            runtime.apply_pending_batch_with(
                current_ledger_index,
                validated_ledger_index,
                apply_batch,
                report_fee_change,
                publish_proposed,
                set_bad_flag,
                set_held_flag,
                should_relay,
                relay,
                current_ledger_state,
            )
        })
    }

    pub fn apply_network_ops_pending_to_open_ledger(&self) -> Option<AppNetworkOpsApplyReport> {
        // This method reads the closed-LCL-derived base and applies into the
        // open ledger. Hold the outer gate for both phases so it cannot capture
        // the old parent, wait through a jump, and then apply to the new view.
        // The mutex is re-entrant because close/batch callers already hold it.
        let _lcl_transition_guard = self.lcl_transition_gate().lock();
        let base_ledger = match self.ledger_master_state.latest_ledger() {
            Some(ledger) => self.ledger_with_node_fetcher(ledger),
            None => {
                tracing::warn!(target: "relay", pending_count = self.network_ops_pending_transaction_count(), "apply_pending: NO base_ledger — early return, txns NOT applied");
                return None;
            }
        };
        let current_ledger_index = self
            .live_current_ledger_index()
            .unwrap_or_else(|| base_ledger.header().seq.saturating_add(1).max(1));
        let validated_ledger_index = self.validated_ledger_seq();
        tracing::debug!(
            target: "rpc",
            base_seq = base_ledger.header().seq,
            current_ledger_index,
            pending_count = self.network_ops_pending_transaction_count(),
            "apply_network_ops_pending_to_open_ledger: entry"
        );
        let tx_q = self.registry.tx_q.clone();
        let open_ledger = self.registry.open_ledger.clone();
        // Clone for the current_ledger_state closure (the batch closure below
        // already moves tx_q/open_ledger, so the state closure needs its own
        // Arc refs to query the queue-aware fee and seq after apply).
        let tx_q_for_state = tx_q.clone();
        let open_ledger_for_state = open_ledger.clone();
        let state_ledger = Arc::clone(&base_ledger);
        let account_seqs = Arc::clone(&self.open_ledger_account_seqs);
        let sandbox_holder = Arc::clone(&self.open_ledger_sandbox);

        self.apply_network_ops_pending_batch_with(
            current_ledger_index,
            validated_ledger_index,
            move |transactions| {
                tracing::debug!(
                    target: "rpc",
                    batch_len = transactions.len(),
                    "apply_network_ops_pending_to_open_ledger: batch closure entered"
                );
                let mut changed = false;
                let mut lock = AppTxQLock;
                // Use the persistent sandbox (matching rippled's persistent OpenView).
                // This ensures subsequent submits see state from prior ones.
                let mut submit_view = PersistentSubmitSandbox::take_or_new(
                    Arc::clone(&sandbox_holder),
                    Arc::clone(&base_ledger),
                );
                let _ = open_ledger.modify(|view| {
                    for entry in transactions.iter_mut() {
                        let tx = Arc::clone(
                            entry
                                .transaction
                                .lock()
                                .expect("transaction mutex must not be poisoned")
                                .get_s_transaction(),
                        );
                        let tx_source = AppQueueApplyTxSource::new(tx.as_ref());
                        let clear_ahead_queue = tx_q.current_account_txs(
                            tx.get_account_id(get_field_by_symbol("sfAccount")),
                        );
                        let metrics_snapshot = tx_q.metrics_snapshot();
                        let view_snapshot = view.clone();
                        let live_queue_view = view_snapshot.queue_apply_view(
                            submit_view.view_mut(),
                            tx.as_ref(),
                            metrics_snapshot,
                        );
                        let queue_view = snapshot_queue_apply_app_view_with_metrics(
                            &tx_source,
                            &live_queue_view,
                            metrics_snapshot,
                        );
                        let mut runtime = AppOpenLedgerTxQApplyRuntime::new_with_clear_ahead(
                            view,
                            submit_view.view_mut(),
                            Arc::clone(&tx),
                            networkops_apply_flags(entry.admin, entry.fail_hard),
                            current_ledger_index,
                            self.load_fee_track.as_ref(),
                            Arc::clone(&account_seqs),
                            self.registry.network_id_service.get_network_id(),
                            clear_ahead_queue,
                            metrics_snapshot,
                        );
                        let result = tx_q
                            .apply_with_owned_metrics_and_derived_preflight_facts_and_hold_admission(
                                &mut lock,
                                &mut runtime,
                                &queue_view,
                                &tx_source,
                            )
                            .apply_result();
                        let (clear_attempts, clear_removed) = runtime.take_clear_ahead_effects();
                        tx_q.apply_try_clear_effects(
                            tx.get_account_id(get_field_by_symbol("sfAccount")),
                            &clear_attempts,
                            &clear_removed,
                        );

                        entry.result = Some(result.ter);
                        entry.applied = result.applied;
                        changed |= result.applied;
                    }
                    changed
                });
                changed
            },
            || {
                let _ = self.report_fee_change();
            },
            |tx, result| {
                let _ = self.publish_proposed_transaction(tx, result);
            },
            |_tx| {},
            |_tx| false,
            |tx| {
                // reference: hashRouter.shouldRelay(txID) → Optional<set<PeerId>>
                let tx_id = tx
                    .lock()
                    .expect("transaction mutex must not be poisoned")
                    .get_id();
                self.registry.hash_router.should_relay(tx_id)
            },
            |tx, deferred, to_skip| {
                // reference: overlay.relay(txID, tmTransaction, toSkip)
                let Some(overlay_rt) = self.overlay_runtime() else {
                    return;
                };
                let (tx_id, raw_bytes) = {
                    let guard = tx
                        .lock()
                        .expect("transaction mutex must not be poisoned");
                    let stx = guard.get_s_transaction();
                    (guard.get_id(), stx.get_serializer().data().to_vec())
                };
                let local_timestamp = self.shared_time_keeper().now().as_seconds() as u64;
                // `deferred` is produced locally by NetworkOps from the apply
                // result (`result == terQUEUED`). Never forward wire envelope
                // metadata retained from the peer that submitted this tx.
                overlay_rt.overlay().relay_transaction(
                    tx_id,
                    Some(queue_relay_envelope(raw_bytes, local_timestamp, deferred)),
                    &to_skip,
                );
            },
            move |transaction| {
                let tx = Arc::clone(
                    transaction
                        .lock()
                        .expect("transaction mutex must not be poisoned")
                        .get_s_transaction(),
                );
                let tx_source = AppQueueApplyTxSource::new(tx.as_ref());
                // Build a thin view over the current base ledger so that
                // `get_tx_required_fee_and_seq` reads `sfSequence` from the
                // same source rippled uses (`calculateBaseFee` on the open
                // ledger view) and calls `nextQueuableSeqImpl` to produce a
                // queue-aware `available_seq`. This matches rippled's
                // `NetworkOPsImp::apply` → `getTxRequiredFeeAndSeq` path.
                let fee_view =
                    AppRequiredFeeView::new(state_ledger.as_ref(), open_ledger_for_state.current().open_ledger_tx_count());
                let mut lock = AppTxQLock;
                let fee_and_seq = tx_q_for_state.get_tx_required_fee_and_seq(&mut lock, &fee_view, &tx_source);
                if fee_view.failure().is_some() {
                    return crate::NetworkOpsCurrentLedgerState {
                        fee: protocol::XRPAmount::from_drops(i64::MAX),
                        account_seq: 0,
                        available_seq: 0,
                    };
                }
                crate::NetworkOpsCurrentLedgerState {
                    fee: protocol::XRPAmount::from_drops(
                        fee_and_seq.required_fee_drops,
                    ),
                    account_seq: fee_and_seq.account_seq,
                    available_seq: fee_and_seq.available_seq,
                }
            },
        )
    }

    pub fn update_local_tx(
        &self,
        ledger: &Ledger,
    ) -> Result<bool, shamap::traversal::TraversalError> {
        let Some(runtime) = self.ledger_master_runtime.as_ref() else {
            return Ok(false);
        };

        runtime.update_local_tx(ledger)?;
        Ok(true)
    }

    pub fn local_tx_count(&self) -> Option<usize> {
        self.ledger_master_runtime
            .as_ref()
            .map(|runtime| runtime.get_local_tx_count())
    }

    pub fn add_held_transaction(&self, transaction: &Transaction) -> bool {
        let Some(runtime) = self.ledger_master_runtime.as_ref() else {
            return false;
        };

        runtime.add_held_transaction(transaction);
        true
    }

    pub fn held_transaction_count(&self) -> Option<usize> {
        self.ledger_master_runtime
            .as_ref()
            .map(|runtime| runtime.held_transaction_count())
    }

    pub fn pop_acct_transaction(&self, transaction: &Transaction) -> Option<Arc<protocol::STTx>> {
        self.ledger_master_runtime
            .as_ref()
            .and_then(|runtime| runtime.pop_acct_transaction_for(transaction))
    }

    pub fn apply_held_transactions<F>(
        &self,
        next_open_ledger_parent_hash: SHAMapHash,
        process_transaction_set: F,
    ) -> Option<usize>
    where
        F: FnMut(CanonicalTXSet),
    {
        self.ledger_master_runtime.as_ref().map(|runtime| {
            runtime.apply_held_transactions(next_open_ledger_parent_hash, process_transaction_set)
        })
    }

    pub fn transaction_master(&self) -> Arc<TransactionMaster> {
        Arc::clone(&self.transaction_master)
    }

    pub fn fetch_cached_transaction(&self, txn_id: &Uint256) -> Option<SharedTransaction> {
        self.transaction_master.fetch_from_cache(txn_id)
    }

    pub fn canonicalize_transaction(&self, txn: &mut SharedTransaction) {
        self.transaction_master.canonicalize(txn);
    }

    pub fn transaction_close_time_seconds(&self, ledger_seq: u32) -> Option<i64> {
        self.ledger_master_state
            .validated_ledger()
            .filter(|ledger| ledger.header().seq == ledger_seq)
            .or_else(|| {
                self.ledger_master_state
                    .published_ledger()
                    .filter(|ledger| ledger.header().seq == ledger_seq)
            })
            .or_else(|| {
                self.ledger_master_state
                    .closed_ledger()
                    .filter(|ledger| ledger.header().seq == ledger_seq)
            })
            .map(|ledger| i64::from(ledger.header().close_time))
    }

    pub fn transaction_json(
        &self,
        transaction: &Transaction,
        options: JsonOptions,
        binary: bool,
    ) -> JsonValue {
        transaction.get_json_with_close_time_source(options, binary, self)
    }

    pub fn validators(&self) -> Arc<ValidatorList> {
        Arc::clone(&self.validators)
    }

    /// Return the centralized validation requirement used by LedgerMaster
    /// acceptance paths. This is `0` only for standalone mode, matching
    /// rippled `LedgerMaster::getNeededValidations`.
    fn needed_validations(&self) -> usize {
        needed_validations(self.standalone(), self.validators().quorum())
    }

    /// Run the validation-set expiry portion of rippled `Application::doSweep`.
    /// Bootstrap invokes this at the configured application sweep interval.
    pub(crate) fn expire_validations(&self) {
        self.validations()
            .validations()
            .lock()
            .expect("validations mutex must not be poisoned")
            .expire();
    }

    /// Refresh NegativeUNL and trusted-validator state before every consensus
    /// round. This is the shared `NetworkOPs::beginConsensus` prelude: the
    /// selected LCL supplies both its NegativeUNL and its close time.
    pub(crate) fn refresh_validator_trust_for_consensus(
        &self,
        lcl: &Ledger,
    ) -> Result<(), shamap::traversal::TraversalError> {
        let negative_unl = lcl
            .try_negative_unl()?
            .into_iter()
            .map(PublicKey::from_bytes)
            .collect();
        self.validators.set_negative_unl(negative_unl);

        let current_node_ids = self
            .validations
            .validations()
            .lock()
            .expect("validations mutex must not be poisoned")
            .get_current_node_ids();
        let seen_validators = current_node_ids
            .iter()
            .map(|node_id| {
                AccountID::from_slice(node_id.data())
                    .expect("NodeID and AccountID have equal width")
            })
            .collect();
        let trust_changes = self
            .validators
            .update_trusted(&seen_validators, lcl.header().close_time);
        // Expiry and rotation can change UNL blocking without changing the
        // trusted key set, so synchronize before this early return.
        self.set_unl_blocked(self.validators.unl_blocked());
        if trust_changes.added.is_empty() && trust_changes.removed.is_empty() {
            return Ok(());
        }

        let added = trust_changes
            .added
            .iter()
            .map(|account_id| {
                NodeID::from_slice(account_id.data())
                    .expect("AccountID and NodeID have equal width")
            })
            .collect();
        let removed = trust_changes
            .removed
            .iter()
            .map(|account_id| {
                NodeID::from_slice(account_id.data())
                    .expect("AccountID and NodeID have equal width")
            })
            .collect();
        self.validations
            .validations()
            .lock()
            .expect("validations mutex must not be poisoned")
            .trust_changed(&added, &removed);
        self.amendment_status
            .set_trusted_validators(self.validators.get_quorum_keys().1);
        Ok(())
    }

    /// Apply a validator-list collection from an owned site or a peer-facing
    /// application path, then perform the app-owned side effects that must not
    /// be left to a one-shot bootstrap fetch.
    pub fn apply_validator_lists(
        &self,
        manifest: &str,
        version: u32,
        blobs: &[ValidatorBlobInfo],
        site_uri: String,
        hash: Uint256,
    ) -> PublisherListStats {
        let result = self
            .validators
            .apply_lists(manifest, version, blobs, site_uri, Some(hash));

        if result.best_disposition() <= ListDisposition::KnownSequence {
            self.broadcast_v1_validator_list(&result, hash);
        }
        if result.publisher_key.is_some()
            && let Err(error) = self.persist_manifest_caches()
        {
            // Runtime refreshes have no startup Result channel. Keep the
            // verified in-memory list, but make failed durable persistence
            // visible immediately rather than deferring it to shutdown.
            tracing::error!(target: "manifest", %error,
                "failed to persist trusted validator-list manifests");
        }
        result
    }

    /// Apply a v1 list received from a peer. The source peer is installed in
    /// HashRouter before rebroadcast selection, preventing an accepted list
    /// from being echoed straight back to its sender.
    pub fn apply_validator_lists_from_peer(
        &self,
        peer_id: overlay::PeerId,
        manifest: &str,
        version: u32,
        blobs: &[ValidatorBlobInfo],
        site_uri: String,
        hash: Uint256,
    ) -> PublisherListStats {
        self.registry
            .hash_router
            .add_suppression_peer(hash, peer_id);
        self.apply_validator_lists(manifest, version, blobs, site_uri, hash)
    }

    pub(crate) fn validator_list_relay_skip(
        &self,
        hash: Uint256,
    ) -> Option<std::collections::BTreeSet<overlay::PeerId>> {
        self.registry.hash_router.should_relay(hash)
    }

    pub(crate) fn add_validator_list_suppression_peer(
        &self,
        hash: Uint256,
        peer_id: overlay::PeerId,
    ) -> bool {
        self.registry
            .hash_router
            .add_suppression_peer(hash, peer_id)
    }

    fn broadcast_v1_validator_list(&self, result: &PublisherListStats, hash: Uint256) {
        use overlay::{Overlay, ProtocolFeature};

        let Some(publisher) = result.publisher_key else {
            return;
        };
        let Some(to_skip) = self.registry.hash_router.should_relay(hash) else {
            return;
        };
        let Some(serde_json::Value::Object(body)) =
            self.validators.get_available(&publisher.to_hex(), Some(1))
        else {
            return;
        };
        let Some(manifest) = body.get("manifest").and_then(serde_json::Value::as_str) else {
            return;
        };
        let Some(blob) = body.get("blob").and_then(serde_json::Value::as_str) else {
            return;
        };
        let Some(signature) = body.get("signature").and_then(serde_json::Value::as_str) else {
            return;
        };
        let Some(signature) = basics::string_utilities::str_unhex(signature) else {
            return;
        };
        let protocol = overlay::ProtocolMessage::new(overlay::ProtocolPayload::ValidatorList(
            overlay::TmValidatorList {
                manifest: basics::base64::base64_decode(manifest),
                blob: basics::base64::base64_decode(blob),
                signature,
                version: 1,
            },
        ));
        let Some(overlay_rt) = self.overlay_runtime() else {
            return;
        };
        for peer in overlay_rt.overlay().active_peers() {
            if to_skip.contains(&peer.id())
                || !peer.supports_feature(ProtocolFeature::ValidatorListPropagation)
                || peer.publisher_list_sequence(publisher).unwrap_or_default() >= result.sequence
            {
                continue;
            }
            peer.set_publisher_list_sequence(publisher, result.sequence);
            peer.send(overlay::Message::new(protocol.clone(), None));
            // Match v1 sendValidatorList: each successful outbound message is
            // recorded as a suppression peer before future rebroadcasts.
            self.registry
                .hash_router
                .add_suppression_peer(hash, peer.id());
        }
    }

    pub fn validator_sites(&self) -> Arc<ValidatorSite> {
        Arc::clone(&self.registry.validator_sites)
    }

    pub fn persist_manifest_caches(&self) -> Result<(), String> {
        self.registry.validator_manifest_cache.save_to_wallet(
            self.registry.wallet_db.as_ref(),
            "ValidatorManifests",
            |public_key| self.validators.listed(*public_key),
        )?;
        self.registry.publisher_manifest_cache.save_to_wallet(
            self.registry.wallet_db.as_ref(),
            "PublisherManifests",
            |public_key| self.validators.trusted_publisher(*public_key),
        )
    }

    pub fn manifest_cache(&self) -> &Arc<ManifestCache> {
        &self.registry.validator_manifest_cache
    }

    pub fn publisher_manifest_cache(&self) -> &Arc<ManifestCache> {
        &self.registry.publisher_manifest_cache
    }

    pub fn receive_validation_to_network_ops(
        &self,
        validation: &mut protocol::STValidation,
        source: &str,
    ) -> Option<AppNetworkOpsValidationReceiveReport> {
        if validation.get_seen_time() == 0 {
            validation.set_seen(self.shared_time_keeper().close_time().as_seconds());
        }
        self.network_ops_validation_runtime
            .as_ref()
            .map(|runtime| runtime.receive_validation(validation, source))
    }

    pub fn receive_validation_to_network_ops_with_accept(
        &self,
        validation: &mut protocol::STValidation,
        source: &str,
        accept_sink: &dyn crate::RclValidationAcceptanceSink,
    ) -> Option<AppNetworkOpsValidationReceiveReport> {
        if validation.get_seen_time() == 0 {
            validation.set_seen(self.shared_time_keeper().close_time().as_seconds());
        }
        self.network_ops_validation_runtime.as_ref().map(|runtime| {
            runtime.receive_validation_with_accept(validation, source, Some(accept_sink))
        })
    }

    pub fn status_rpc_state(&self) -> Arc<StatusRpcState> {
        Arc::clone(&self.status_rpc_state)
    }

    pub fn status_rpc_current_ledger_index(&self) -> Option<u32> {
        self.status_rpc_state.current_ledger_index()
    }

    pub fn set_status_rpc_current_ledger_index(
        &self,
        current_ledger_index: Option<u32>,
    ) -> Option<u32> {
        self.status_rpc_state
            .set_current_ledger_index(current_ledger_index)
    }

    pub fn status_rpc_queue_report(&self) -> Option<QueueTxQRpcReport> {
        self.status_rpc_state.queue_report()
    }

    pub fn set_status_rpc_queue_report(
        &self,
        queue_report: Option<QueueTxQRpcReport>,
    ) -> Option<QueueTxQRpcReport> {
        self.status_rpc_state.set_queue_report(queue_report)
    }

    pub fn status_rpc_peer_count(&self) -> Option<u32> {
        self.status_rpc_state.peer_count()
    }

    pub fn set_status_rpc_peer_count(&self, peer_count: Option<u32>) -> Option<u32> {
        self.status_rpc_state.set_peer_count(peer_count)
    }

    pub fn status_rpc_network_id(&self) -> Option<u32> {
        self.status_rpc_state.network_id()
    }

    pub fn set_status_rpc_network_id(&self, network_id: Option<u32>) -> Option<u32> {
        self.status_rpc_state.set_network_id(network_id)
    }

    pub fn status_rpc_last_close(&self) -> Option<StatusRpcLastClose> {
        self.status_rpc_state.last_close()
    }

    pub fn set_status_rpc_last_close(
        &self,
        last_close: Option<StatusRpcLastClose>,
    ) -> Option<StatusRpcLastClose> {
        self.status_rpc_state.set_last_close(last_close)
    }

    pub fn current_server_time_string(&self) -> String {
        basics::chrono::to_string(OffsetDateTime::now_utc())
    }

    pub fn current_close_time_seconds(&self) -> u32 {
        self.time_keeper.close_time().as_seconds()
    }

    pub fn current_network_time_seconds(&self) -> u32 {
        self.time_keeper.now().as_seconds()
    }

    pub fn close_time_offset_seconds(&self) -> i64 {
        self.time_keeper.close_offset().whole_seconds()
    }

    pub fn status_rpc_hostid(&self) -> Option<String> {
        self.status_rpc_state.hostid()
    }

    pub fn set_status_rpc_hostid(&self, hostid: Option<String>) -> Option<String> {
        self.status_rpc_state.set_hostid(hostid)
    }

    pub fn status_rpc_server_domain(&self) -> Option<String> {
        self.status_rpc_state.server_domain()
    }

    pub fn set_status_rpc_server_domain(&self, server_domain: Option<String>) -> Option<String> {
        self.status_rpc_state.set_server_domain(server_domain)
    }

    /// Start an RPC snapshot export under the application lifecycle owner.
    /// The state atomically records the worker and its owned cancellation
    /// token before this call returns; `MainRuntime::shutdown` requests
    /// cancellation and joins it before any storage component stops.
    pub fn start_snapshot_export(
        &self,
        output: String,
        ledger_seq: u32,
        spawn: impl FnOnce(
            Arc<SnapshotExportState>,
            nodestore::snapshot::SnapshotExportCancellation,
        ) -> Result<std::thread::JoinHandle<()>, String>,
    ) -> Result<(), String> {
        self.snapshot_export_state.start(output, ledger_seq, spawn)
    }

    /// Request cancellation of RPC snapshot work and join it before storage
    /// teardown, so no writer can retain a NodeStore backend after shutdown.
    pub fn quiesce_snapshot_export(&self) {
        self.snapshot_export_state.quiesce();
    }

    pub fn snapshot_export_status(&self) -> SnapshotExportStatus {
        self.snapshot_export_state.snapshot()
    }

    pub fn status_rpc_node_size(&self) -> Option<String> {
        self.status_rpc_state.node_size()
    }

    pub fn set_status_rpc_node_size(&self, node_size: Option<String>) -> Option<String> {
        self.status_rpc_state.set_node_size(node_size)
    }

    pub fn status_rpc_io_latency_ms(&self) -> Option<u64> {
        self.status_rpc_state.io_latency_ms()
    }

    pub fn set_status_rpc_io_latency_ms(&self, io_latency_ms: Option<u64>) -> Option<u64> {
        self.status_rpc_state.set_io_latency_ms(io_latency_ms)
    }

    pub fn admin_pubkey_validator(&self) -> String {
        self.validation_public_key
            .and(self.validators.local_public_key())
            .map(|public_key| public_key.to_node_public_base58())
            .unwrap_or_else(|| "none".to_owned())
    }

    pub fn status_rpc_complete_ledgers(&self) -> Option<String> {
        self.status_rpc_state.complete_ledgers()
    }

    pub fn set_status_rpc_complete_ledgers(
        &self,
        complete_ledgers: Option<String>,
    ) -> Option<String> {
        self.status_rpc_state.set_complete_ledgers(complete_ledgers)
    }

    pub fn status_rpc_fetch_pack(&self) -> Option<u32> {
        self.status_rpc_state.fetch_pack()
    }

    pub fn set_status_rpc_fetch_pack(&self, fetch_pack: Option<u32>) -> Option<u32> {
        self.status_rpc_state.set_fetch_pack(fetch_pack)
    }

    pub fn status_rpc_git_info(&self) -> Option<StatusRpcGitInfo> {
        self.status_rpc_state.git_info()
    }

    pub fn validator_list_status_snapshot(&self) -> ValidatorListStatusSnapshot {
        self.validators.status_snapshot()
    }

    pub fn set_status_rpc_git_info(
        &self,
        git_info: Option<StatusRpcGitInfo>,
    ) -> Option<StatusRpcGitInfo> {
        self.status_rpc_state.set_git_info(git_info)
    }

    pub fn set_network_ops_operating_mode(
        &self,
        operating_mode: NetworkOpsOperatingMode,
    ) -> NetworkOpsOperatingMode {
        self.set_network_ops_operating_mode_with_reason(operating_mode, "unspecified")
    }

    /// Set the operating mode through validated-ledger-age / blocked
    /// normalization, recording `reason` on the transition trace and metric.
    pub fn set_network_ops_operating_mode_with_reason(
        &self,
        operating_mode: NetworkOpsOperatingMode,
        reason: &'static str,
    ) -> NetworkOpsOperatingMode {
        let previous = self.network_ops_state.operating_mode();
        self.network_ops_state.set_operating_mode_with_reason(
            normalize_operating_mode_for_validated_age(
                operating_mode,
                self.validated_ledger_age(),
                self.network_ops_state.is_blocked(),
            ),
            reason,
        );
        let new_mode = self.network_ops_state.operating_mode();
        if previous != new_mode {
            tracing::info!(target: "app", from = %previous.as_str(), to = %new_mode.as_str(), "Operating mode changed");
            let fee_track = self.load_fee_track();
            let base_fee = self
                .closed_ledger()
                .or_else(|| self.validated_ledger())
                .map(|ledger| ledger.fees().base)
                .unwrap_or_default();
            let payload = JsonValue::Object(std::collections::BTreeMap::from([
                (
                    "type".to_owned(),
                    JsonValue::String("serverStatus".to_owned()),
                ),
                (
                    "server_status".to_owned(),
                    JsonValue::String(new_mode.as_str().to_owned()),
                ),
                (
                    "load_base".to_owned(),
                    JsonValue::Unsigned(u64::from(fee_track.load_base())),
                ),
                (
                    "load_factor".to_owned(),
                    JsonValue::Unsigned(u64::from(std::cmp::max(
                        fee_track.local_fee(),
                        fee_track.cluster_fee(),
                    ))),
                ),
                ("base_fee".to_owned(), JsonValue::Unsigned(base_fee)),
            ]));
            if let Ok(guard) = self.shared_subscription_manager.read()
                && let Some(publisher) = guard.as_ref()
            {
                publisher("server", payload);
            }
        }
        previous
    }

    pub fn network_ops_operating_mode(&self) -> NetworkOpsOperatingMode {
        self.network_ops_state.operating_mode()
    }

    pub fn network_ops_operating_mode_string(&self) -> &'static str {
        self.network_ops_operating_mode_string_for_admin(false)
    }

    /// Match rippled `NetworkOPsImp::strOperatingMode`: only an admin view of
    /// a full node whose consensus engine is actively proposing receives the
    /// `proposing` presentation. Non-validator observers always remain `full`.
    pub fn network_ops_operating_mode_string_for_admin(&self, admin: bool) -> &'static str {
        if admin
            && self.network_ops_state.operating_mode() == NetworkOpsOperatingMode::Full
            && self.network_ops_state.consensus_mode()
                == crate::network::network_ops::NetworkOpsConsensusMode::Proposing
        {
            return "proposing";
        }
        self.network_ops_state.str_operating_mode()
    }

    pub fn set_need_network_ledger(&self, need_network_ledger: bool) {
        self.network_ops_state
            .set_need_network_ledger(need_network_ledger);
    }

    pub fn set_completed_ledgers_rx(
        &self,
        rx: std::sync::mpsc::Receiver<crate::ledger::inbound_ledgers::CompletedInboundLedger>,
    ) {
        if let Some(lm_rt) = self.ledger_master_runtime() {
            *lm_rt
                .completed_ledgers_rx
                .lock()
                .expect("completed_ledgers_rx") = Some(rx);
        }
    }

    pub fn need_network_ledger(&self) -> bool {
        self.network_ops_state.need_network_ledger()
    }

    pub fn set_amendment_blocked(&self, amendment_blocked: bool) {
        self.network_ops_state
            .set_amendment_blocked(amendment_blocked);
    }

    pub fn amendment_blocked(&self) -> bool {
        self.network_ops_state.amendment_blocked()
    }

    pub fn set_unl_blocked(&self, unl_blocked: bool) {
        self.network_ops_state.set_unl_blocked(unl_blocked);
    }

    pub fn unl_blocked(&self) -> bool {
        self.network_ops_state.unl_blocked()
    }

    pub fn unsupported_majority_warning_details(
        &self,
    ) -> Option<UnsupportedMajorityWarningDetails> {
        self.amendment_status.unsupported_majority_warning_details()
    }

    pub fn amendment_status(&self) -> Arc<AmendmentStatus> {
        Arc::clone(&self.amendment_status)
    }

    pub fn unsupported_majority_warned(&self) -> bool {
        self.amendment_status.unsupported_majority_warned()
    }

    pub fn set_unsupported_majority_warning_details(
        &self,
        warning: Option<UnsupportedMajorityWarningDetails>,
    ) -> Option<UnsupportedMajorityWarningDetails> {
        self.amendment_status
            .set_unsupported_majority_warning_details(warning)
    }

    pub fn set_unsupported_majority_warned(&self, warned: bool) -> bool {
        self.amendment_status
            .set_unsupported_majority_warned(warned)
    }

    /// Attach the node-store fetcher to a backed `Ledger`.
    ///
    /// fetcher/writer plumbing or re-run state-map setup on every promotion.
    /// Once a ledger already has both seams attached, keep the owner path hot and
    /// return it unchanged.
    pub fn ledger_with_node_fetcher(&self, ledger: Arc<Ledger>) -> Arc<Ledger> {
        let has_shared_family = self.node_family().is_some();
        if (ledger.has_node_fetcher()
            && ledger.has_node_writer_result()
            && ledger.has_node_batch_writer_result())
            || (!ledger.state_map().backed() && !ledger.tx_map().backed())
        {
            return ledger;
        }

        let fetcher = self.node_fetcher_from_store();
        let writer = self.node_writer_from_store();
        let writer_result = self.node_writer_result_from_store();
        let batch_writer_result = self.node_batch_writer_result_from_store();
        if fetcher.is_none()
            && writer.is_none()
            && writer_result.is_none()
            && batch_writer_result.is_none()
        {
            tracing::warn!(target: "ledger",
                "[ledger_fetcher] WARNING: backed ledger seq={} stored without node fetcher/writer \
                 (node store not yet attached) — reads/writes will fail with MissingNode",
                ledger.header().seq
            );
            return ledger;
        }

        let mut ledger_with_fetcher = ledger.as_ref().clone();
        full_sync_debug!(
            "[full_debug][ledger_fetcher] normalize seq={} hash={} account_hash={} tx_hash={} had_fetcher={} had_writer={} shared_family={} backed_state={} backed_tx={}",
            ledger.header().seq,
            ledger.header().hash,
            ledger.header().account_hash,
            ledger.header().tx_hash,
            ledger.has_node_fetcher(),
            ledger.has_node_writer(),
            has_shared_family,
            ledger.state_map().backed(),
            ledger.tx_map().backed()
        );
        if let Some(fetcher) = fetcher {
            ledger_with_fetcher.set_node_fetcher(fetcher);
        }
        if let Some(writer) = writer
            && !ledger_with_fetcher.has_node_writer()
        {
            ledger_with_fetcher.set_node_writer(writer);
        }
        if let Some(writer) = writer_result
            && !ledger_with_fetcher.has_node_writer_result()
        {
            ledger_with_fetcher.set_node_writer_result(writer);
        }
        if let Some(writer) = batch_writer_result
            && !ledger_with_fetcher.has_node_batch_writer_result()
        {
            ledger_with_fetcher.set_node_batch_writer_result(writer);
        }
        match ledger_with_fetcher.setup_from_state_map(&feature_xrp_fees()) {
            Ok(true) => {
                full_sync_debug!(
                    "[full_debug][ledger_fetcher] setup seq={} result=loaded fees_base={} fees_reserve={} fees_inc={}",
                    ledger_with_fetcher.header().seq,
                    ledger_with_fetcher.fees().base,
                    ledger_with_fetcher.fees().reserve,
                    ledger_with_fetcher.fees().increment
                );
            }
            Ok(false)
                if ledger_with_fetcher.fees().base == 0
                    || ledger_with_fetcher.fees().reserve == 0
                    || ledger_with_fetcher.fees().increment == 0 =>
            {
                tracing::warn!(target: "ledger",
                    "[ledger_fetcher] WARNING: backed ledger seq={} setup incomplete after fetcher attach",
                    ledger_with_fetcher.header().seq
                );
                full_sync_debug!(
                    "[full_debug][ledger_fetcher] setup seq={} result=incomplete_zero_fee fees_base={} fees_reserve={} fees_inc={}",
                    ledger_with_fetcher.header().seq,
                    ledger_with_fetcher.fees().base,
                    ledger_with_fetcher.fees().reserve,
                    ledger_with_fetcher.fees().increment
                );
            }
            Ok(false) => {
                full_sync_debug!(
                    "[full_debug][ledger_fetcher] setup seq={} result=no_change fees_base={} fees_reserve={} fees_inc={}",
                    ledger_with_fetcher.header().seq,
                    ledger_with_fetcher.fees().base,
                    ledger_with_fetcher.fees().reserve,
                    ledger_with_fetcher.fees().increment
                );
            }
            Err(error) => {
                tracing::warn!(target: "ledger",
                    "[ledger_fetcher] WARNING: backed ledger seq={} setup failed after fetcher attach: {:?}",
                    ledger_with_fetcher.header().seq,
                    error
                );
                full_sync_debug!(
                    "[full_debug][ledger_fetcher] setup seq={} result=error error={:?}",
                    ledger_with_fetcher.header().seq,
                    error
                );
            }
        }
        Arc::new(ledger_with_fetcher)
    }

    pub fn on_closed_ledger(&self, ledger: Arc<Ledger>) {
        self.on_closed_ledger_inner(ledger, ClosedLedgerHistoryAction::Store)
            .expect("unconditional closed-ledger promotion cannot fail");
    }

    /// Mirrors rippled switchLCL after buildLCL has already called storeLedger:
    /// update only canonical closed-LCL side effects, without a second
    /// LedgerHistory insert or validation-adaptor registration.
    fn on_closed_ledger_after_store(&self, ledger: Arc<Ledger>) {
        self.on_closed_ledger_inner(ledger, ClosedLedgerHistoryAction::AlreadyStored)
            .expect("unconditional switchLCL cannot fail");
    }

    fn on_closed_ledger_inner(
        &self,
        ledger: Arc<Ledger>,
        history_action: ClosedLedgerHistoryAction,
    ) -> Result<(), String> {
        if self.inbound_ledger_is_provisional(*ledger.header().hash.as_uint256()) {
            tracing::debug!(target: "inbound_ledger", hash = %ledger.header().hash,
                "deferring LCL installation for resolver-visible provisional inbound ledger");
            return Ok(());
        }
        let _lcl_transition_guard = self.lcl_transition_gate.lock();
        // Diagnostic: check incoming tree state before clone
        {
            let mut loaded = 0u32;
            let mut non_empty = 0u32;
            for branch in 0..16 {
                if !ledger.state_map().root().is_empty_branch(branch) {
                    non_empty += 1;
                    if ledger.state_map().root().get_child(branch).is_some() {
                        loaded += 1;
                    }
                }
            }
            tracing::info!(
                target: "ledger",
                seq = ledger.header().seq,
                non_empty, loaded,
                backed = ledger.state_map().backed(),
                "on_closed_ledger: INCOMING tree state (before clone)"
            );
        }

        let normalized = self.ledger_with_node_fetcher(ledger);
        let closed_ledger_changed = self
            .closed_ledger()
            .is_none_or(|previous| previous.header().hash != normalized.header().hash);
        if closed_ledger_changed {
            tracing::info!(
                target: "lcl_trace",
                event = "closed_ledger_promotion_waiting_for_close_gate",
                seq = normalized.header().seq,
                "LCL trace: closed-ledger promotion waiting for close gate"
            );
            // A Sandbox owns its parent view. Reusing one after a LCL switch
            // makes submit preclaim read the old state and can turn an account
            // that is visible through validated RPC into a false terNO_ACCOUNT.
            // Serialize against direct submit application; consensus on_close
            // already uses this same gate while it captures its tx set.
            let _close_guard = self
                .close_gate
                .lock()
                .expect("close_gate mutex must not be poisoned");
            tracing::info!(
                target: "lcl_trace",
                event = "closed_ledger_promotion_acquired_close_gate",
                seq = normalized.header().seq,
                "LCL trace: closed-ledger promotion acquired close gate"
            );
            // This legacy per-account cache is not reconstructible from a
            // LocalTx replay, so every LCL transition invalidates it.
            if let Ok(mut seqs) = self.open_ledger_account_seqs.lock() {
                seqs.clear();
            }

            // `OpenLedger::accept` may already have rebuilt and published the
            // persistent OpenView for `normalized` before this closed-ledger
            // notification runs. Preserve that exact-parent view: it contains
            // the direct current-open effects that TransactionSign and TxQ
            // must both observe. Discard only a sandbox over a genuinely old
            // LCL. Unconditionally clearing here split signing from the
            // rebuilt OpenLedger and allowed server-side autofill to reuse a
            // sequence already occupied by a current-open transaction.
            let normalized_header = normalized.header();
            let mut sandbox = self
                .open_ledger_sandbox
                .lock()
                .expect("sandbox mutex must not be poisoned");
            tracing::info!(
                target: "lcl_trace",
                event = "closed_ledger_promotion_acquired_sandbox",
                seq = normalized.header().seq,
                "LCL trace: closed-ledger promotion acquired sandbox"
            );
            let sandbox_matches_new_lcl = sandbox.as_ref().is_some_and(|sandbox| {
                let header = sandbox.header();
                header.parent_hash == normalized_header.hash
                    && header.parent_close_time == normalized_header.close_time
            });
            if !sandbox_matches_new_lcl {
                *sandbox = None;
            }
        }
        self.ledger_master_state
            .note_closed_ledger(Arc::clone(&normalized));
        tracing::info!(
            target: "lcl_trace",
            event = "closed_ledger_promotion_noted",
            seq = normalized.header().seq,
            "LCL trace: closed-ledger promotion installed canonical closed ledger"
        );
        // A fresh standalone network may not yet advance through the
        // quorum-backed validated-ledger path, but its active closed LCL
        // already supplies the amendment rules used for the next open
        // ledger. Keep the feature RPC table synchronized with that LCL so
        // its enabled flags describe the rules the node is actually using.
        self.amendment_status
            .do_validated_ledger(normalized.as_ref());

        if let Some(overlay_runtime) = self.overlay_runtime() {
            overlay_runtime.overlay().set_handshake_ledgers(
                *normalized.header().hash.as_uint256(),
                *normalized.header().parent_hash.as_uint256(),
            );
        }

        // Keep the active LCL's SHAMaps resident through consensus. rippled
        // `LedgerMaster::switchLCL` installs `closedLedger_` and checks
        // validation; it does not evict the just-accepted state/transaction
        // maps. Evicting here clears shared nodes from the closed, open, and
        // consensus-held views, forcing their next reads through NuDB while
        // the next consensus round is still converging.
        // `SharedLedgerMasterState` (behind `ledger_master_state`) is this
        // node's SINGLE source of truth for "the closed ledger", matching
        // the reference's `LedgerMaster::closedLedger_` (exactly one
        // tracker, set only by `switchLCL`). Earlier in this session a
        // second, independent tracker was read from in several places
        // (`AppLedgerMasterRuntime`'s wrapped `ledger::LedgerMaster`,
        // accessed via `ledger_master_runtime().ledger_master()`), which
        // repeatedly went stale relative to this one and caused the
        // consensus loop to stall or lose sync. That second tracker's
        // `closed_ledger`/`set_closed_ledger` are no longer read or
        // written anywhere in the bootstrap loop -- `root.closed_ledger()`
        // (this tracker) is the only source of truth now, everywhere.
        if history_action == ClosedLedgerHistoryAction::Store
            && let Some(runtime) = self.ledger_master_runtime()
            && normalized.is_immutable()
        {
            // Still feed `ledger_history` (needed for by-hash/by-seq lookup
            // during consensus round parent resolution and tx-set
            // acquisition), but do NOT also call `set_closed_ledger` here
            // -- that would resurrect the second tracker as a write target
            // that nothing needs to read from anymore.
            runtime
                .ledger_master()
                .ledger_history()
                .insert(Arc::clone(&normalized), false);
            // Sweep stale entries to bound RAM — without this, every closed
            // ledger accumulates indefinitely in the cache (~240KB each).
            runtime.ledger_master().ledger_history().sweep();
            // NOTE: rippled does NOT sweep NodeFamily on every closed ledger.
            // NodeFamily::sweep() is called only from ApplicationImp::doSweep()
            // which runs on the configured SweepInterval (60s for medium).
            // See Application.cpp:982. Sweeping here caused premature eviction
            // of tree nodes during initial sync (every 3-4s vs correct 60s).
            // Matches rippled's Validations::onLedger: pre-populate the
            // validations adaptor's local cache so `updateTrie` →
            // `acquire` doesn't need the slower ledger_history fallback.
            self.validations().register_ledger(&normalized);
        }

        // A prior JtBatch may have found no base ledger and released its
        // dispatch state for retry. Now that this closed ledger is visible,
        // schedule existing async work through NetworkOps' guarded transition.
        let _ = self.schedule_network_ops_transaction_batch();
        Ok(())
    }

    pub fn closed_ledger(&self) -> Option<Arc<Ledger>> {
        self.ledger_master_state.closed_ledger()
    }

    pub fn closed_ledger_seq(&self) -> Option<u32> {
        self.ledger_master_state.closed_ledger_seq()
    }

    /// Match `LedgerMaster::getEarliestFetch` using the canonical closed-LCL
    /// owner. The wrapped `ledger::LedgerMaster` retains a compatibility
    /// closed-ledger slot for standalone/legacy callers, but live consensus
    /// deliberately does not write that second slot. Retention and serving
    /// floors must therefore advance with this application's single LCL.
    pub fn earliest_ledger_fetch(&self, fetch_depth: u32) -> u32 {
        self.closed_ledger_seq()
            .map(|seq| seq.saturating_sub(fetch_depth))
            .unwrap_or_default()
    }

    /// Return the next sequence that the current open ledger can accept for
    /// `tx`. This is the server-side signing source of truth: it mirrors
    /// rippled `TransactionSign.cpp`, which reads `OpenLedger::current()` and
    /// asks `TxQ::nextQueuableSeq` for the contiguous queued successor.
    ///
    /// The persistent submit sandbox is the Rust equivalent of that current
    /// OpenView. It is deliberately preferred over the legacy cache because
    /// an LCL rebase rebuilds the sandbox from LocalTxs without reconstructing
    /// the cache.
    pub fn network_ops_next_account_seq_for_tx(&self, tx: &STTx) -> Option<u32> {
        let tx_source = AppQueueApplyTxSource::new(tx);
        let open_tx_count = self.open_ledger().current().open_ledger_tx_count();

        if let Ok(sandbox_holder) = self.open_ledger_sandbox.lock()
            && let Some(sandbox) = sandbox_holder.as_ref()
        {
            let fee_view = AppRequiredFeeView::new(sandbox, open_tx_count);
            let mut lock = AppTxQLock;
            let fee_and_seq = self
                .registry
                .tx_q
                .get_tx_required_fee_and_seq(&mut lock, &fee_view, &tx_source);
            if fee_view.failure().is_some() {
                return None;
            }
            return (fee_and_seq.account_seq != 0).then_some(fee_and_seq.available_seq);
        }

        // Before a persistent open sandbox is first created, the closed LCL
        // is the best current view. Still use TxQ so queued contiguous
        // sequences are preserved if one exists at this boundary.
        let base = self.ledger_master_state.latest_ledger()?;
        let fee_view = AppRequiredFeeView::new(base.as_ref(), open_tx_count);
        let mut lock = AppTxQLock;
        let fee_and_seq = self
            .registry
            .tx_q
            .get_tx_required_fee_and_seq(&mut lock, &fee_view, &tx_source);
        if fee_view.failure().is_some() {
            return None;
        }
        (fee_and_seq.account_seq != 0).then_some(fee_and_seq.available_seq)
    }

    /// Get the account's current sequence from the network ops pending state.
    /// This cache remains available for callers that only have an AccountID;
    /// server-side signing must use `network_ops_next_account_seq_for_tx`.
    pub fn network_ops_current_account_seq(&self, account: &protocol::AccountID) -> Option<u32> {
        if let Ok(seqs) = self.open_ledger_account_seqs.lock() {
            if let Some(&seq) = seqs.get(account) {
                return Some(seq);
            }
        }
        let base = self.ledger_master_state.latest_ledger()?;
        let keylet =
            protocol::account_keylet(basics::base_uint::Uint160::from_void(account.data()));
        let sle = base.read(keylet).ok().flatten()?;
        Some(sle.get_field_u32(protocol::get_field_by_symbol("sfSequence")))
    }

    /// Record that a transaction from this account was successfully submitted to the open ledger.
    /// The next expected sequence is tx_seq + 1.
    pub fn note_open_ledger_tx(&self, account: &protocol::AccountID, tx_seq: u32) {
        if let Ok(mut seqs) = self.open_ledger_account_seqs.lock() {
            let next = tx_seq.saturating_add(1);
            let entry = seqs.entry(*account).or_insert(next);
            if next > *entry {
                *entry = next;
            }
        }
    }

    /// Clear the open ledger sequence tracker (called on ledger_accept/close).
    pub fn clear_open_ledger_account_seqs(&self) {
        if let Ok(mut seqs) = self.open_ledger_account_seqs.lock() {
            seqs.clear();
        }
        // Also reset the persistent sandbox so next submit starts fresh from new closed ledger
        if let Ok(mut sandbox) = self.open_ledger_sandbox.lock() {
            *sandbox = None;
        }
    }

    fn ledger_closed_notification(&self, ledger: &Ledger) -> protocol::JsonValue {
        let mut notification = std::collections::BTreeMap::from([
            (
                "type".to_owned(),
                protocol::JsonValue::String("ledgerClosed".to_owned()),
            ),
            (
                "ledger_index".to_owned(),
                protocol::JsonValue::Unsigned(u64::from(ledger.header().seq)),
            ),
            (
                "ledger_hash".to_owned(),
                protocol::JsonValue::String(ledger.header().hash.to_string()),
            ),
            (
                "ledger_time".to_owned(),
                protocol::JsonValue::Unsigned(u64::from(ledger.header().close_time)),
            ),
            (
                "network_id".to_owned(),
                protocol::JsonValue::Unsigned(u64::from(self.network_id())),
            ),
            (
                "fee_base".to_owned(),
                protocol::JsonValue::Unsigned(ledger.fees().base),
            ),
            (
                "reserve_base".to_owned(),
                protocol::JsonValue::Unsigned(ledger.fees().reserve),
            ),
            (
                "reserve_inc".to_owned(),
                protocol::JsonValue::Unsigned(ledger.fees().increment),
            ),
            (
                "txn_count".to_owned(),
                protocol::JsonValue::Unsigned(
                    ledger
                        .tx_snapshot()
                        .map(|transactions| transactions.len())
                        .unwrap_or_default() as u64,
                ),
            ),
        ]);
        if !ledger.rules().enabled(&feature_xrp_fees()) {
            notification.insert(
                "fee_ref".to_owned(),
                protocol::JsonValue::Unsigned(u64::from(REFERENCE_FEE_UNITS_DEPRECATED)),
            );
        }
        if self.network_ops_operating_mode() >= NetworkOpsOperatingMode::Syncing {
            if let Some(runtime) = self.ledger_master_runtime() {
                notification.insert(
                    "validated_ledgers".to_owned(),
                    protocol::JsonValue::String(
                        runtime.ledger_master().complete_ledgers().to_string(),
                    ),
                );
            }
        }
        protocol::JsonValue::Object(notification)
    }

    pub fn on_published_ledger(&self, ledger: Arc<Ledger>) {
        self.ledger_master_state
            .note_published_ledger(self.ledger_with_node_fetcher(Arc::clone(&ledger)));
        let notification = self.ledger_closed_notification(ledger.as_ref());
        if let Some(publisher) = self.ledger_close_publisher.as_ref() {
            publisher(notification.clone());
        }
        let publisher = self
            .shared_subscription_manager
            .read()
            .ok()
            .and_then(|guard| guard.as_ref().cloned());
        if let Some(publisher) = publisher.as_ref() {
            publisher("ledger", notification);
        }
        let Ok(transactions) = ledger.tx_snapshot() else {
            return;
        };
        let Some(publisher) = publisher.as_ref() else {
            return;
        };
        for (transaction, meta) in transactions {
            let event = crate::ledger_to_json::ledger_to_json_tx::transaction_subscription_event(
                ledger.as_ref(),
                transaction.as_ref(),
                &meta,
            );
            // `transactions` receives only accepted events. The distinct
            // real-time stream receives both proposed and the terminal
            // validated event, matching rippled's STransactions/SRtTransactions
            // split.
            publisher("transactions", event.clone());
            publisher("transactions_proposed", event);
        }
    }

    pub fn published_ledger(&self) -> Option<Arc<Ledger>> {
        self.ledger_master_state.published_ledger()
    }

    pub fn published_ledger_seq(&self) -> Option<u32> {
        self.ledger_master_state.published_ledger_seq()
    }

    fn retain_publication_provisional_deferral(
        &self,
        identity: crate::ledger::inbound_ledgers::ProvisionalLedgerIdentity,
    ) {
        let mut advance = self
            .publication_advance
            .lock()
            .expect("publication advance state lock");
        match advance.provisional_deferral.as_mut() {
            Some(existing) if existing.identity == identity => {
                if !existing.suppression_logged {
                    existing.suppression_logged = true;
                    tracing::debug!(
                        target: "ledger",
                        event = "publication_provisional_suppressed",
                        target_hash = %identity.target_hash,
                        ledger_hash = %identity.ledger_hash,
                        ledger_seq = identity.ledger_seq,
                        acquisition_id = identity.acquisition_id,
                        store_generation = identity.store_generation,
                        persistence_generation = identity.persistence_generation,
                        "publication remains coalesced behind exact provisional identity"
                    );
                }
            }
            _ => {
                advance.provisional_deferral = Some(PublicationDeferral {
                    identity,
                    suppression_logged: false,
                });
                tracing::debug!(
                    target: "ledger",
                    event = "publication_provisional_deferred",
                    target_hash = %identity.target_hash,
                    ledger_hash = %identity.ledger_hash,
                    ledger_seq = identity.ledger_seq,
                    acquisition_id = identity.acquisition_id,
                    store_generation = identity.store_generation,
                    persistence_generation = identity.persistence_generation,
                    "publication deferred behind exact provisional identity"
                );
            }
        }
    }

    /// Clear a retained publication deferral only when its exact Worker-2
    /// lifecycle is no longer visible. The durable callback merely requests
    /// this serialized pass; it never publishes directly.
    fn refresh_publication_provisional_deferral(&self) {
        let retained = self
            .publication_advance
            .lock()
            .expect("publication advance state lock")
            .provisional_deferral;
        let Some(retained) = retained else {
            return;
        };
        let observed = self.inbound_provisional_identity(retained.identity.target_hash);
        if observed == Some(retained.identity) {
            return;
        }
        let mut advance = self
            .publication_advance
            .lock()
            .expect("publication advance state lock");
        if advance
            .provisional_deferral
            .is_some_and(|current| current.identity == retained.identity)
        {
            advance.provisional_deferral = None;
            tracing::debug!(
                target: "ledger",
                event = "publication_provisional_woken",
                wake_reason = if observed.is_some() { "acquisition_replaced" } else { "durable_or_terminal_transition" },
                target_hash = %retained.identity.target_hash,
                ledger_hash = %retained.identity.ledger_hash,
                ledger_seq = retained.identity.ledger_seq,
                acquisition_id = retained.identity.acquisition_id,
                store_generation = retained.identity.store_generation,
                persistence_generation = retained.identity.persistence_generation,
                "publication deferral released after matching lifecycle transition"
            );
        }
    }

    fn publish_full_ledger(
        &self,
        lm: &crate::AppLedgerMaster,
        ledger: Arc<Ledger>,
    ) -> Result<Option<Arc<Ledger>>, String> {
        let hash = *ledger.header().hash.as_uint256();
        if let Some(identity) = self.inbound_provisional_identity(hash) {
            self.retain_publication_provisional_deferral(identity);
            return Ok(None);
        }
        if self.inbound_ledger_is_provisional(hash) {
            return Err(format!(
                "publication deferred for provisional inbound ledger {hash}"
            ));
        }
        let persistence = ledger::LedgerPersistence::new(self.build_ledger_persistence_runtime());
        let mut full = ledger;
        {
            let full_ledger = Arc::make_mut(&mut full);
            full_ledger.set_validated();
            full_ledger.set_full();
        }
        lm.set_full_ledger(&persistence, Arc::clone(&full), true, true, None, None)
            .map_err(|error| format!("publication setFullLedger failed: {error:?}"))?;
        lm.set_pub_ledger(Arc::clone(&full));
        // Match rippled LedgerMaster::doAdvance: the authoritative publication
        // commit clears the independent network-startup recovery latch. A
        // later maintenance snapshot cannot reliably infer this edge because
        // checkAccept may publish synchronously before that snapshot.
        self.set_need_network_ledger(false);
        // Publishing changes the owner-visible plan even when no validation
        // or inbound callback follows immediately.
        self.request_publication_advance();
        self.on_published_ledger(Arc::clone(&full));
        let _ = self.order_book_db().setup(
            Arc::clone(&full),
            Arc::new(NullOrderBookDBRuntime),
            Arc::new(NullOrderBookDBJournal),
        );
        Ok(Some(full))
    }

    /// Matches rippled's `tryAdvance()` → `doAdvance()` →
    /// `findNewLedgersToPublish()`. After a ledger is validated (via
    /// `check_accept_ledger` or the strand's tryAdvance burst), this
    /// publishes it so that `is_caught_up()` returns true and the
    /// operating mode can advance to FULL.
    ///
    /// The logic is:
    /// - If no published ledger exists (first time): publish validated directly
    /// - If gap > MAX_LEDGER_GAP (100): jump to validated directly
    /// - Otherwise: walk sequentially (handled by plan_advance_publication)
    pub fn try_advance_publication(&self) {
        let _advance_guard = self.validation_advance_gate.lock();
        self.try_advance_publication_serialized();
    }

    /// Request one coalesced publication planning pass. This function is safe
    /// for acquisition and replay callbacks: it does not inspect ledgers or
    /// acquire anything itself, and merely wakes the serialized strand owner.
    pub(crate) fn request_publication_advance(&self) {
        {
            let mut advance = self
                .publication_advance
                .lock()
                .expect("publication advance state lock");
            advance.requested_epoch = advance.requested_epoch.wrapping_add(1).max(1);
        }
        self.notify_consensus_event();
    }

    fn try_advance_publication_serialized(&self) {
        let Some(lm_rt) = self.ledger_master_runtime() else {
            return;
        };
        let lm = lm_rt.ledger_master();
        self.refresh_publication_provisional_deferral();
        let epoch = {
            let advance = self
                .publication_advance
                .lock()
                .expect("publication advance state lock");
            let heads = PublicationPlanIdentity::heads(lm.as_ref());
            if advance.planned_epoch == advance.requested_epoch
                && advance
                    .last_plan
                    .is_some_and(|last_plan| last_plan.matches_heads(heads))
            {
                // An ordinary NetworkOps heartbeat has no new owner event and
                // the validated/published heads are unchanged. In particular,
                // do not re-touch the same Generic candidates.
                return;
            }
            advance.requested_epoch
        };

        let mut report = lm_rt.plan_advance_publication();
        if let Some(missing) = report.missing
            && self
                .resolve_ledger_by_hash(SHAMapHash::new(missing.hash))
                .is_some()
        {
            // The provider load canonicalized the exact hash into LedgerHistory.
            // Re-plan so publication remains contiguous and never treats a
            // provider result as validated by itself.
            report = lm_rt.plan_advance_publication();
        }
        // `LedgerMaster.cpp::findNewLedgersToPublish` derives replay from the
        // publication plan, not directly from an arbitrary missing hash. Keep
        // that proof before publication mutates the owner's current pointer.
        let replay_range = lm_rt.plan_publication_replay(&report);
        let plan_identity = PublicationPlanIdentity::from_report(lm.as_ref(), &report);

        use crate::ledger::ledger_master_runtime::AppLedgerMasterPublishAdvance;
        match report.decision {
            AppLedgerMasterPublishAdvance::NothingToPublish => {}
            AppLedgerMasterPublishAdvance::FirstPublished => {
                if let Some(ledger) = report.published.last() {
                    tracing::info!(
                        target: "ledger",
                        seq = ledger.header().seq,
                        "tryAdvance: publishing first validated ledger"
                    );
                    match self
                        .publish_full_ledger(lm_rt.ledger_master().as_ref(), Arc::clone(ledger))
                    {
                        Ok(Some(_)) | Ok(None) => {}
                        Err(error) => tracing::error!(target: "ledger", %error,
                            "tryAdvance: failed to publish first full ledger"),
                    }
                }
            }
            AppLedgerMasterPublishAdvance::GapTooLarge => {
                if let Some(ledger) = report.published.last() {
                    tracing::info!(
                        target: "ledger",
                        seq = ledger.header().seq,
                        "tryAdvance: gap too large, jumping to validated ledger"
                    );
                    match self
                        .publish_full_ledger(lm_rt.ledger_master().as_ref(), Arc::clone(ledger))
                    {
                        Ok(Some(_)) | Ok(None) => {}
                        Err(error) => tracing::error!(target: "ledger", %error,
                            "tryAdvance: failed to publish gap ledger"),
                    }
                }
            }
            AppLedgerMasterPublishAdvance::Sequential => {
                for ledger in &report.published {
                    tracing::debug!(
                        target: "ledger",
                        seq = ledger.header().seq,
                        "tryAdvance: publishing sequential ledger"
                    );
                    match self
                        .publish_full_ledger(lm_rt.ledger_master().as_ref(), Arc::clone(ledger))
                    {
                        Ok(Some(_)) => {}
                        Ok(None) => break,
                        Err(error) => {
                            tracing::error!(target: "ledger", %error,
                                "tryAdvance: failed to publish sequential full ledger");
                            break;
                        }
                    }
                }
                // Match rippled findNewLedgersToPublish: start missing
                // validated-chain ledgers in ascending order with its strict
                // `++acqCount < ledgerFetchSize_` bound. The planner retains
                // the first missing item separately for replay proof.
                let generic_fetch_limit = crate::NodeSizeResourceProfile::for_node_size(
                    self.status_rpc_node_size().as_deref(),
                )
                .ledger_fetch_size
                .saturating_sub(1);
                if generic_fetch_limit != 0 {
                    if let Ok(guard) = lm_rt.inbound_ledgers.lock() {
                        if let Some(shared) = guard.as_ref() {
                            for missing in report
                                .generic_acquire_candidates
                                .iter()
                                .take(generic_fetch_limit as usize)
                            {
                                shared.acquire_async(
                                    missing.hash,
                                    missing.seq,
                                    crate::ledger::inbound_ledgers::AcquireReason::Generic,
                                );
                            }
                        }
                    }
                }
                if let Some(replay) = replay_range {
                    // `../rippled/src/xrpld/app/ledger/detail/LedgerMaster.cpp::
                    // findNewLedgersToPublish` requests this exact inclusive
                    // suffix through `LedgerReplayer::replay`. The planner has
                    // already proved nonzero, bounded input; the replayer owns
                    // duplicate-task and stopping checks.
                    if let Ok(mut replayer) = self.registry.ledger_replayer.lock() {
                        tracing::debug!(
                            target: "ledger",
                            finish_hash = %replay.finish_hash,
                            total_ledgers = replay.total_ledgers,
                            "tryAdvance: scheduling publication-gap ledger replay"
                        );
                        let root = self.clone();
                        let inbound_ledgers = Arc::clone(&lm_rt.inbound_ledgers);
                        let _ = replayer.replay_and_init(
                            ledger::InboundLedgerReason::Generic,
                            replay.finish_hash,
                            replay.total_ledgers,
                            1,
                            move |hash| root.resolve_ledger_by_hash(SHAMapHash::new(hash)),
                            move |hash, seq, _reason| {
                                if let Ok(guard) = inbound_ledgers.lock()
                                    && let Some(shared) = guard.as_ref()
                                {
                                    shared.acquire_async(
                                        hash,
                                        seq,
                                        crate::ledger::inbound_ledgers::AcquireReason::Generic,
                                    );
                                }
                            },
                        );
                    } else {
                        tracing::error!(target: "ledger",
                            "tryAdvance: ledger replayer lock poisoned; refusing publication-gap replay"
                        );
                    }
                }
            }
        }

        // Preserve a later event that raced this serialized pass: only the
        // epoch observed above is consumed. The next strand turn will plan
        // again when a completion, failure, sweep, replay event, or publish
        // arrived during this work.
        let mut advance = self
            .publication_advance
            .lock()
            .expect("publication advance state lock");
        advance.planned_epoch = epoch;
        advance.last_plan = Some(plan_identity);
    }

    /// Cheap scheduler predicate: while no replay owner is active, the
    /// managed timer does not enqueue empty `JtReplayTask` work. A contended
    /// replayer lock is treated as active so an admission transition cannot be
    /// missed; the next 25 ms poll will observe the exact owner state.
    pub(crate) fn has_active_ledger_replay_timers(&self) -> bool {
        self.registry
            .ledger_replayer
            .try_lock()
            .map_or(true, |replayer| {
                let timers = replayer.timer_status();
                timers.active_tasks != 0
                    || timers.active_skip_lists != 0
                    || timers.active_deltas != 0
            })
    }

    /// Execute due replay task/subtask timers from the app-owned
    /// `JtReplayTask` worker. The scheduler only queues this method; all
    /// ledger lookup, inbound fallback, persistence, and publication remain
    /// under the real application owners.
    pub(crate) fn drive_ledger_replay_timers(&self) {
        let Some(runtime) = self.ledger_master_runtime() else {
            return;
        };
        let root = self.clone();
        let inbound_ledgers = Arc::clone(&runtime.inbound_ledgers);
        let completed = match self.registry.ledger_replayer.lock() {
            Ok(mut replayer) => {
                let result = replayer.drive_timeouts(
                    std::time::Instant::now(),
                    &mut |hash| root.resolve_ledger_by_hash(SHAMapHash::new(hash)),
                    &mut |replay| {
                        crate::build_ledger_from_replay_delta_with_network_id(
                            replay,
                            root.registry.network_id_service.get_network_id(),
                        )
                    },
                    &mut |hash, seq, _reason| {
                        if let Ok(guard) = inbound_ledgers.lock()
                            && let Some(shared) = guard.as_ref()
                        {
                            shared.acquire_async(
                                hash,
                                seq,
                                crate::ledger::inbound_ledgers::AcquireReason::Generic,
                            );
                        }
                    },
                );
                replayer.sweep();
                result
            }
            Err(_) => {
                tracing::error!(target: "ledger", "ledger replayer lock poisoned; skipping replay timer");
                return;
            }
        };
        let completed = match completed {
            Ok(ledgers) => ledgers,
            Err(error) => {
                tracing::warn!(target: "ledger", ?error, "replay timer task failed while advancing delta");
                return;
            }
        };
        for ledger in completed {
            let ledger = self.store_consensus_ledger(ledger);
            self.check_accept_hash_seq(*ledger.header().hash.as_uint256(), ledger.header().seq);
        }
        // A replay timer can advance its owned task even when it produced no
        // complete ledger yet; make that progress a coalesced planning event.
        self.request_publication_advance();
        self.try_advance_publication();
    }

    pub fn validated_ledger_age(&self) -> std::time::Duration {
        self.ledger_master_state.validated_ledger_age()
    }

    /// Returns the validated ledger age in seconds (convenience for shouldAcquire gating).
    pub fn validated_ledger_age_seconds(&self) -> u64 {
        self.ledger_master_state.validated_ledger_age().as_secs()
    }

    /// Returns true if the local fee track reports the node is overloaded.
    /// Matches rippled's `app_.getFeeTrack().isLoadedLocal()`.
    pub fn load_fee_track_loaded_local(&self) -> bool {
        self.load_fee_track.is_loaded_local()
    }

    /// Evicts the node store's in-memory membership (Bloom) filter, if any.
    ///
    /// Intended to be called once history backfill has completed: for a single
    /// (non-rotating) store the filter was only a sync/backfill accelerator and
    /// provides negligible steady-state benefit, so freeing it reclaims RAM.
    /// Rotating stores keep their filters (the rotating store treats this as a
    /// no-op) because they still use them to skip cross-store probes. Safe when
    /// no node store or no filter is configured.
    pub fn evict_node_store_membership_filter(&self) {
        if let Some(node_store) = self.node_store().as_ref() {
            node_store.evict_membership_filter();
        }
    }

    /// Returns the active NodeStore write backlog. Before the store is
    /// attached there is no pending persistence work, so return zero.
    /// Matches rippled's `app_.getNodeStore().getWriteLoad()`.
    pub fn node_store_write_load(&self) -> i32 {
        self.node_store()
            .as_ref()
            .map_or(0, |node_store| match node_store {
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Single(database) => {
                    database.get_write_load()
                }
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Rotating(database) => {
                    database.get_write_load()
                }
            })
    }

    /// Returns the earliest persisted ledger sequence available through the
    /// configured node store, matching rippled's SHAMapStore online floor.
    ///
    /// `None` means no node store is configured, so callers retain the full
    /// validated range without imposing an unsupported floor.
    pub fn minimum_online_seq(&self) -> Option<u32> {
        self.node_store()
            .as_ref()
            .map(|node_store| match node_store {
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Single(database) => {
                    database.earliest_ledger_seq()
                }
                crate::shamap::shamap_store_backend::SHAMapStoreNodeStore::Rotating(database) => {
                    database.earliest_ledger_seq()
                }
            })
    }

    pub fn is_caught_up(&self) -> LedgerMasterCaughtUp {
        self.ledger_master_state.is_caught_up()
    }

    pub fn server_okay(&self) -> Result<(), &'static str> {
        server_okay(
            self.elb_support,
            &self.stop_tree,
            self.network_ops_state.as_ref(),
            self.is_caught_up(),
            self.load_fee_track.is_loaded_local(),
        )
    }

    pub fn elb_support_enabled(&self) -> bool {
        self.elb_support
    }

    pub fn set_node_identity(
        &mut self,
        node_identity: (PublicKey, SecretKey),
    ) -> Option<(PublicKey, SecretKey)> {
        self.node_identity.replace(node_identity)
    }

    pub fn set_validation_public_key(
        &mut self,
        validation_public_key: PublicKey,
    ) -> Option<PublicKey> {
        self.validation_public_key.replace(validation_public_key)
    }

    pub fn set_validation_seed(&mut self, seed: String) {
        self.registry.config.validation_seed = Some(seed);
    }

    pub fn set_validator_token(&mut self, token: Vec<String>) {
        self.registry.config.validator_token = Some(token);
    }

    pub fn runtime_bindings(&self) -> &RuntimeBindings {
        &self.runtime_bindings
    }

    pub fn set_runtime_bindings(&mut self, bindings: RuntimeBindings) {
        self.runtime_bindings = bindings;
    }

    pub fn shamap_store_service(&self) -> Option<Arc<SHAMapStoreService>> {
        self.shamap_store_service.as_ref().map(Arc::clone)
    }

    pub fn attach_shamap_store_service(
        &mut self,
        service: Arc<SHAMapStoreService>,
    ) -> Option<Arc<SHAMapStoreService>> {
        let handle: ManagedHandle = service.clone();
        self.runtime_bindings.shamap_store = Some(handle);
        self.shamap_store_service.replace(service)
    }

    pub fn attach_shamap_store_component(
        &mut self,
        component: Arc<SHAMapStoreComponent>,
    ) -> Arc<SHAMapStoreService> {
        let service = Arc::new(SHAMapStoreService::new(
            component,
            Arc::new(crate::SharedSHAMapStoreHealthState::new_with_app_state(
                self.time_keeper.clone(),
                self.network_ops_state(),
                self.ledger_master_state(),
            )),
        ));
        let _ = self.attach_shamap_store_service(Arc::clone(&service));
        service
    }

    pub fn bind_ledger(&mut self, component: ManagedHandle) -> Option<ManagedHandle> {
        self.runtime_bindings.ledger.replace(component)
    }

    pub fn bind_nodestore(&mut self, component: ManagedHandle) -> Option<ManagedHandle> {
        self.runtime_bindings.nodestore.replace(component)
    }

    pub fn bind_shamap_store(&mut self, component: ManagedHandle) -> Option<ManagedHandle> {
        self.shamap_store_service = None;
        self.runtime_bindings.shamap_store.replace(component)
    }

    pub fn bind_overlay(&mut self, component: ManagedHandle) -> Option<ManagedHandle> {
        self.overlay_runtime = None;
        self.runtime_bindings.overlay.replace(component)
    }

    pub fn bind_consensus(&mut self, component: ManagedHandle) -> Option<ManagedHandle> {
        self.runtime_bindings.consensus.replace(component)
    }

    pub fn bind_server(&mut self, component: ManagedHandle) -> Option<ManagedHandle> {
        self.runtime_bindings.server.replace(component)
    }

    pub fn bind_grpc(&mut self, component: ManagedHandle) {
        self.runtime_bindings.grpc = GrpcRuntime::Enabled(component);
    }

    pub fn disable_grpc(&mut self, reason: impl Into<String>) {
        self.runtime_bindings.grpc = GrpcRuntime::DisabledExplicit {
            reason: reason.into(),
        };
    }

    pub fn register_stop_callback(
        &self,
        name: impl Into<String>,
        callback: impl Fn() + Send + Sync + 'static,
    ) -> Arc<StopTreeNode> {
        self.stop_tree.register_callback(name, callback)
    }

    pub fn wire_node_family_reset(&self) -> Option<Arc<StopTreeNode>> {
        let node_family = self.node_family()?;
        Some(
            self.stop_tree
                .register_callback("node-family-reset", move || {
                    node_family.reset();
                }),
        )
    }

    pub fn set_shamap_store_operating_mode(
        &self,
        operating_mode: SHAMapStoreOperatingMode,
    ) -> bool {
        let Some(service) = self.shamap_store_service.as_ref() else {
            return false;
        };
        self.network_ops_state
            .set_operating_mode(match operating_mode {
                SHAMapStoreOperatingMode::Full => NetworkOpsOperatingMode::Full,
                SHAMapStoreOperatingMode::Other => NetworkOpsOperatingMode::Connected,
            });
        service.set_operating_mode(operating_mode);
        true
    }

    pub fn shamap_store_operating_mode(&self) -> Option<SHAMapStoreOperatingMode> {
        self.shamap_store_service
            .as_ref()
            .map(|service| service.operating_mode())
    }

    pub(crate) fn inbound_provisional_identity(
        &self,
        hash: basics::base_uint::Uint256,
    ) -> Option<crate::ledger::inbound_ledgers::ProvisionalLedgerIdentity> {
        self.ledger_master_runtime().and_then(|runtime| {
            runtime
                .inbound_ledgers
                .lock()
                .expect("inbound_ledgers mutex")
                .as_ref()
                .and_then(|inbound| inbound.provisional_identity(&hash))
        })
    }

    /// True only while Worker 2's exact inbound acquisition identity remains
    /// resolver-visible but has not crossed its durable completion fence.
    /// Consensus, LCL, validation, and publication owners must treat this as
    /// non-adoptable; the registry revokes the same identity on terminal
    /// failure so a replacement acquisition cannot be mistaken for it.
    pub(crate) fn inbound_ledger_is_provisional(&self, hash: basics::base_uint::Uint256) -> bool {
        self.ledger_master_runtime().is_some_and(|runtime| {
            runtime
                .inbound_ledgers
                .lock()
                .expect("inbound_ledgers mutex")
                .as_ref()
                .is_some_and(|inbound| inbound.is_provisional(&hash))
        })
    }

    /// Compensate an early resolver publication whose final NodeStore
    /// durability fence failed on the validation/publication owner. Every
    /// target is conditional on the exact acquisition, hash, and sequence.
    pub(crate) fn revoke_provisional_inbound_ledger(
        &self,
        identity: crate::ledger::inbound_ledgers::ProvisionalLedgerIdentity,
    ) {
        let _lcl_transition_guard = self.lcl_transition_gate.lock();
        let _advance_guard = self.validation_advance_gate.lock();
        let hash = basics::sha_map_hash::SHAMapHash::new(identity.ledger_hash);
        if identity.target_hash != identity.ledger_hash {
            return;
        }
        if let Some(runtime) = self.ledger_master_runtime() {
            runtime
                .ledger_master()
                .revoke_provisional_ledger(hash, identity.ledger_seq);
        }
        self.validations().unregister_ledger(identity.ledger_hash);
        self.ledger_master_state
            .revoke_ledger(hash, identity.ledger_seq);
        tracing::warn!(
            target: "inbound_ledger",
            hash = %identity.ledger_hash,
            seq = identity.ledger_seq,
            acquisition_id = identity.acquisition_id,
            "revoked provisional inbound ledger after NodeStore durability failure"
        );
    }

    /// Resolve an immutable ledger by its exact hash through the same
    /// cache-then-provider path used by ledger serving. A provider result is
    /// canonicalized as a nonvalidated history cache entry; callers must still
    /// apply compatibility, quorum, and publication policy themselves.
    pub(crate) fn resolve_ledger_by_hash(&self, hash: SHAMapHash) -> Option<Arc<Ledger>> {
        let cache_visible_before = self.ledger_master_runtime().is_some_and(|runtime| {
            runtime
                .ledger_master()
                .ledger_history()
                .get_cached_ledger_by_hash(hash)
                .is_some()
        });
        let Some(loaded) =
            crate::ledger::loaded_ledger_runtime::AppLoadedLedgerRuntime::from_root(self)
        else {
            tracing::warn!(
                target: "lcl_trace",
                event = "resolver_runtime_unavailable",
                %hash,
                cache_visible_before,
                "LCL trace: exact-hash resolver has no loaded-ledger runtime"
            );
            return None;
        };
        let resolved = match loaded.get_history_ledger_by_hash(hash) {
            Ok(ledger) => ledger,
            Err(error) => {
                tracing::warn!(target: "ledger", %hash, ?error,
                    "provider-backed exact-hash ledger lookup failed");
                None
            }
        };
        // LedgerHistory canonicalizes by hash, but unlike rippled's Ledger,
        // Quaxar's Ledger carries its durable fetch seam on the object.  Never
        // return a cache/provider object without restoring that seam: history
        // may retain it as `histLedger_`-equivalent or insert it back into the
        // same-hash cache after its weak SHAMap children have been released.
        let resolved = resolved.map(|ledger| self.ledger_with_node_fetcher(ledger));
        tracing::debug!(
            target: "lcl_trace",
            event = "resolver_lookup",
            %hash,
            cache_visible_before,
            resolved = resolved.is_some(),
            resolved_seq = resolved.as_ref().map(|ledger| ledger.header().seq),
            "LCL trace: exact-hash ledger resolver completed"
        );
        resolved
    }

    pub fn on_validated_ledger(&self, ledger: Arc<Ledger>) -> bool {
        if self.inbound_ledger_is_provisional(*ledger.header().hash.as_uint256()) {
            tracing::debug!(target: "inbound_ledger", hash = %ledger.header().hash,
                "deferring direct validated-ledger adoption until NodeStore fence succeeds");
            return false;
        }
        let ledger = self.ledger_with_node_fetcher(ledger);
        self.ledger_master_state
            .note_validated_ledger(Arc::clone(&ledger));
        // Matches the reference's `LedgerMaster::setFullLedger`: once a
        // ledger is fully validated (`ledger->setValidated()`), it calls
        // `ledgerHistory_.insert(ledger, true)` -- with `validated=true`,
        // unlike `on_closed_ledger`'s earlier `insert(..., false)` call
        // (matching `storeLedger`'s pre-validation insert, called before
        // this point in the same round). `LedgerHistory::insert` only
        // populates its by-SEQUENCE index (`ledgers_by_index`) when
        // `validated` is true -- passing `false` here would leave `--start`
        // mode's per-round accepted ledgers permanently unreachable via
        // `get_ledger_by_seq`/`ledger_index: <n>` RPC lookups (only the
        // single most-recent `ledger_master_state` pointer would remain
        // reachable), even though `ledger_history` is exactly the cache
        // `ledger_history`/`online_delete` config is meant to size.
        if let Some(runtime) = self.ledger_master_runtime()
            && ledger.is_immutable()
        {
            runtime
                .ledger_master()
                .ledger_history()
                .insert(Arc::clone(&ledger), true);
            // Matches rippled's Validations::onLedger: register in the
            // validations adaptor's local cache for fast trie lookups.
            self.validations().register_ledger(&ledger);
        }
        self.amendment_status.do_validated_ledger(ledger.as_ref());
        if !self.network_ops_state.is_blocked() {
            if self.amendment_status.has_unsupported_enabled() {
                self.set_amendment_blocked(true);
            } else {
                self.amendment_status
                    .sync_warning_state_for_validated_ledger(ledger.as_ref());
            }
        }
        let Some(service) = self.shamap_store_service.as_ref() else {
            return true;
        };
        service.on_ledger_closed(ledger);
        true
    }

    /// Count trusted, full validations for this exact ledger sequence after
    /// excluding validators in the current negative UNL. `ValidatorList`
    /// already calculates `quorum()` from the effective UNL, so callers must
    /// filter the votes but must not reduce the quorum again.
    fn trusted_validations_for_ledger(
        &self,
        hash: Uint256,
        seq: u32,
    ) -> Vec<protocol::STValidation> {
        self.validators().negative_unl_filter_validations(
            self.validations()
                .store()
                .trusted_for_ledger_by_sequence(hash, seq),
        )
    }

    pub fn trusted_validation_count_for_ledger(&self, hash: Uint256, seq: u32) -> usize {
        self.trusted_validations_for_ledger(hash, seq).len()
    }

    /// Mirrors `LedgerMaster::setValidLedger`: age the validated head from
    /// the sample median of quorum-backed trusted validation signing times.
    /// The fallback is the ledger close time when there is no usable quorum.
    fn trusted_validation_sign_time(&self, hash: Uint256, seq: u32, fallback: u32) -> u32 {
        let validations = self.trusted_validations_for_ledger(hash, seq);
        median_validation_sign_time(
            validations
                .into_iter()
                .map(|validation| validation.get_sign_time())
                .collect(),
            self.validators().quorum(),
            fallback,
        )
    }

    /// Matches rippled's `LedgerMaster::checkAccept(hash, seq)`
    /// (LedgerMaster.cpp:886-931): called synchronously whenever a new
    /// validation is received (`handleNewValidation` -> `checkAccept`).
    /// Checks whether the given ledger hash+seq has reached quorum among
    /// trusted validators; if so, tries to promote it as the validated
    /// ledger. If we don't have the ledger locally, actively dispatches
    /// an acquisition from peers (rippled's `InboundLedgers::acquire`)
    /// instead of passively waiting — this is the missing piece that
    /// enables fork recovery: without it, a node stuck on a minority
    /// fork never learns about (or fetches) the majority's ledger.
    pub fn check_accept_hash_seq(&self, hash: Uint256, seq: u32) {
        let Some(lm_rt) = self.ledger_master_runtime() else {
            return;
        };
        let lm = lm_rt.ledger_master();
        let validator_quorum = self.validators().quorum();
        let mut validation_count = 0usize;

        if seq != 0 {
            let current_valid_seq = lm.valid_ledger_seq();
            let validated_anchor = lm
                .validated_ledger()
                .map(|current| (*current.header().hash.as_uint256(), current.header().seq));
            let last_valid_before = lm.last_valid_ledger();
            if seq < current_valid_seq {
                tracing::debug!(
                target: "lcl_trace",
                event = "validation_observation_ignored_old",
                    observed_hash = %hash,
                    observed_seq = seq,
                    current_valid_seq,
                    ?validated_anchor,
                    ?last_valid_before,
                        "LCL trace: validation observation is older than the validated head"
                );
                tracing::debug!(
                    target: "lcl_audit",
                    observed_hash = %hash,
                    observed_seq = seq,
                    current_valid_seq,
                    ?validated_anchor,
                    ?last_valid_before,
                    "LCL_AUDIT validation ignored below current validated sequence"
                );
                return;
            }
            let val_count = self.trusted_validation_count_for_ledger(hash, seq);
            validation_count = val_count;
            let quorum = validator_quorum;
            if val_count >= quorum {
                // A validator's repeated vote for a quorum-backed ledger is
                // expected high-frequency traffic, not an operator event.
                // Keep the fields for opt-in diagnosis without writing every
                // duplicate observation to the production journal.
                tracing::debug!(
                    target: "lcl_trace",
                    event = "validation_quorum_observed",
                    observed_hash = %hash,
                    observed_seq = seq,
                    current_valid_seq,
                    val_count,
                    quorum,
                    ?validated_anchor,
                    ?last_valid_before,
                    "LCL trace: quorum reached for validation-backed ledger"
                );
            } else {
                tracing::debug!(
                    target: "lcl_trace",
                    event = "validation_observed",
                    observed_hash = %hash,
                    observed_seq = seq,
                    current_valid_seq,
                    val_count,
                    quorum,
                    quorum_reached = false,
                    ?validated_anchor,
                    ?last_valid_before,
                    "LCL trace: validation quorum not yet reached"
                );
            }
            tracing::debug!(
                target: "lcl_audit",
                observed_hash = %hash,
                observed_seq = seq,
                current_valid_seq,
                val_count,
                quorum,
                quorum_reached = val_count >= quorum,
                ?validated_anchor,
                ?last_valid_before,
                "LCL_AUDIT validation observed"
            );
            if val_count >= quorum {
                // Keep the quorum-backed hash/sequence even if its ledger is
                // not cached yet. `is_compatible` must reject a conflicting
                // preferred LCL after the asynchronous acquisition completes.
                lm.note_last_valid_ledger(hash, seq);
                tracing::debug!(
                    target: "lcl_audit",
                    observed_hash = %hash,
                    observed_seq = seq,
                    val_count,
                    quorum,
                    last_valid_after = ?lm.last_valid_ledger(),
                    "LCL_AUDIT quorum compatibility anchor recorded"
                );
            }
            let already_validated = seq == current_valid_seq;
            let building_same_seq = lm_rt
                .building_ledger()
                .is_some_and(|building| building == seq);
            if already_validated || building_same_seq {
                tracing::debug!(
                    target: "lcl_trace",
                    event = "validation_adoption_deferred",
                    observed_hash = %hash,
                    observed_seq = seq,
                    already_validated,
                    building_same_seq,
                    "LCL trace: validation-backed ledger adoption deferred"
                );
                tracing::debug!(
                    target: "lcl_audit",
                    observed_hash = %hash,
                    observed_seq = seq,
                    already_validated,
                    building_same_seq,
                    "LCL_AUDIT validation promotion deferred"
                );
                return;
            }
        }

        let ledger = self.resolve_ledger_by_hash(basics::sha_map_hash::SHAMapHash::new(hash));

        let ledger = match ledger {
            Some(l) => Some(l),
            None => {
                // `LedgerMaster::checkAccept` updates peer convergence before
                // its Generic acquire when a quorum-backed validation arrives
                // before any valid ledger exists.
                if should_check_tracking_on_validation_resolver_miss(
                    seq,
                    lm.valid_ledger_seq(),
                    validation_count,
                    validator_quorum,
                ) {
                    use overlay::Overlay;
                    if let Some(overlay_runtime) = self.overlay_runtime() {
                        overlay_runtime.overlay().check_tracking(seq);
                    }
                }

                // Matches rippled's `app_.getInboundLedgers().acquire(hash,
                // seq, InboundLedger::Reason::GENERIC)`: actively fetch the
                // ledger we don't have from peers rather than waiting.
                let mut acquisition_dispatched = false;
                if let Ok(guard) = lm_rt.inbound_ledgers.lock() {
                    if let Some(shared) = guard.as_ref() {
                        shared.acquire_check_accept_ledger_async(hash, seq);
                        acquisition_dispatched = true;
                    }
                }
                tracing::debug!(
                    target: "lcl_trace",
                    event = "validation_resolver_miss_acquire",
                    requested_hash = %hash,
                    requested_seq = seq,
                    acquisition_dispatched,
                    "LCL trace: validation-backed ledger unavailable; acquisition requested"
                );
                tracing::debug!(
                    target: "lcl_audit",
                    requested_hash = %hash,
                    requested_seq = seq,
                    acquisition_dispatched,
                    "LCL_AUDIT quorum-backed validation ledger unavailable locally"
                );
                None
            }
        };

        if let Some(ledger) = ledger {
            let val_count = self.trusted_validation_count_for_ledger(
                *ledger.header().hash.as_uint256(),
                ledger.header().seq,
            );
            let quorum = self.validators().quorum();
            tracing::debug!(
                target: "lcl_trace",
                event = "validation_resolver_hit",
                candidate_hash = %ledger.header().hash,
                candidate_seq = ledger.header().seq,
                candidate_parent_hash = %ledger.header().parent_hash,
                val_count,
                quorum,
                "LCL trace: validation-backed ledger resolved before adoption"
            );
            tracing::debug!(target: "lcl_audit",
                candidate_hash = %ledger.header().hash,
                candidate_seq = ledger.header().seq,
                candidate_parent_hash = %ledger.header().parent_hash,
                val_count,
                quorum,
                "LCL_AUDIT quorum-backed validation ledger resolved locally"
            );
            self.check_accept_ledger(ledger);
        }
    }

    /// Source-equivalent `InboundLedger::AcqDone` acceptance path. Completed
    /// inbound ledgers bypass the validation-receipt building-sequence guard
    /// and are evaluated directly by LedgerMaster's ledger overload.
    pub(crate) fn check_accept_completed_inbound_ledger(&self, ledger: Arc<Ledger>) {
        self.check_accept_ledger(ledger);
    }

    /// Matches the non-standalone `LedgerMaster::switchLCL` branch: after a
    /// recovery LCL is installed, evaluate that exact closed ledger against
    /// current validation quorum. Normal consensus-child installation already
    /// performs this through `install_consensus_child`; this entry point is
    /// deliberately limited to the NetworkOPs recovery-switch path.
    pub(crate) fn check_accept_after_lcl_switch(&self, ledger: Arc<Ledger>) {
        self.check_accept_ledger(ledger);
    }

    /// Matches rippled's `LedgerMaster::checkAccept(ledger)`
    /// (LedgerMaster.cpp:946-1000): promotes `ledger` to validated if it
    /// has reached quorum among trusted validators.
    fn check_accept_ledger(&self, ledger: Arc<Ledger>) {
        if self.inbound_ledger_is_provisional(*ledger.header().hash.as_uint256()) {
            tracing::debug!(target: "inbound_ledger", hash = %ledger.header().hash,
                "deferring validation and publication adoption until NodeStore fence succeeds");
            return;
        }
        let Some(lm_rt) = self.ledger_master_runtime() else {
            return;
        };
        // Keep sequence observation, quorum admission, validated promotion and
        // tryAdvance publication in one critical section. Without this, two
        // different-sequence validation callbacks can both plan from the same
        // pre-published state and later publish/overwrite out of order.
        let _advance_guard = self.validation_advance_gate.lock();
        let lm = lm_rt.ledger_master();

        let current_valid_seq = lm.valid_ledger_seq();
        if ledger.header().seq <= current_valid_seq {
            tracing::debug!(
                target: "lcl_trace",
                event = "validation_adoption_skipped_nonadvancing",
                candidate_hash = %ledger.header().hash,
                candidate_seq = ledger.header().seq,
                current_valid_seq,
                "LCL trace: resolved validation ledger cannot advance the validated head"
            );
            tracing::debug!(
                target: "lcl_audit",
                candidate_hash = %ledger.header().hash,
                candidate_seq = ledger.header().seq,
                current_valid_seq,
                "LCL_AUDIT validation promotion skipped for non-advancing candidate"
            );
            return;
        }

        let quorum = self.needed_validations();
        let val_count = self.trusted_validation_count_for_ledger(
            *ledger.header().hash.as_uint256(),
            ledger.header().seq,
        );
        let validated_sign_time = self.trusted_validation_sign_time(
            *ledger.header().hash.as_uint256(),
            ledger.header().seq,
            ledger.header().close_time,
        );
        let can_be_current = lm.can_be_current(ledger.as_ref(), self.current_close_time_seconds());
        let accepted = lm.check_accept_ledger(
            ledger.as_ref(),
            val_count,
            quorum,
            self.current_close_time_seconds(),
        );
        if !accepted {
            if val_count >= quorum || !can_be_current {
                tracing::info!(
                    target: "lcl_trace",
                    event = "validation_adoption_rejected",
                    candidate_hash = %ledger.header().hash,
                    candidate_seq = ledger.header().seq,
                    current_valid_seq,
                    val_count,
                    quorum,
                    can_be_current,
                    sequence_advances = ledger.header().seq > current_valid_seq,
                    quorum_reached = val_count >= quorum,
                    "LCL trace: validation-backed ledger failed a meaningful adoption gate"
                );
            } else {
                tracing::debug!(
                    target: "lcl_trace",
                    event = "validation_adoption_rejected",
                    candidate_hash = %ledger.header().hash,
                    candidate_seq = ledger.header().seq,
                    current_valid_seq,
                    val_count,
                    quorum,
                    can_be_current,
                    sequence_advances = ledger.header().seq > current_valid_seq,
                    quorum_reached = false,
                    "LCL trace: validation-backed ledger lacks quorum"
                );
            }
            tracing::debug!(
                target: "lcl_audit",
                candidate_hash = %ledger.header().hash,
                candidate_seq = ledger.header().seq,
                current_valid_seq,
                val_count,
                quorum,
                can_be_current,
                sequence_advances = ledger.header().seq > current_valid_seq,
                quorum_reached = val_count >= quorum,
                "LCL_AUDIT validation promotion rejected"
            );
            return;
        }
        tracing::info!(
            target: "lcl_audit",
            candidate_hash = %ledger.header().hash,
            candidate_seq = ledger.header().seq,
            val_count,
            quorum,
            can_be_current,
            "LCL_AUDIT validation promotion admitted"
        );

        let mut l = (*ledger).clone();
        l.set_validated();
        l.set_full();
        let validated = Arc::new(l);

        lm.set_valid_ledger_no_sweep(Arc::clone(&validated), None, Some(validated_sign_time));
        // Validated-head movement is the primary `advanceWork_` source.
        self.request_publication_advance();
        tracing::info!(
            target: "lcl_trace",
            event = "validation_adoption_committed",
            validated_hash = %validated.header().hash,
            validated_seq = validated.header().seq,
            validated_sign_time,
            previous_valid_seq = current_valid_seq,
            "LCL trace: validation-backed ledger committed as validated"
        );
        // `set_valid_ledger_no_sweep` is necessary for partially acquired
        // catch-up ledgers, but this quorum-backed full ledger follows the
        // normal `setValidLedger` path and must sweep LocalTxs now.
        if let Err(error) = self.update_local_tx(validated.as_ref()) {
            tracing::warn!(target: "ledger", seq = validated.header().seq, ?error,
                "check_accept: unable to sweep local transactions for validated ledger");
        }
        // `setFullLedger` in rippled indexes validated ledgers in
        // LedgerHistory. The history scheduler needs this by-sequence entry
        // to retrieve the parent hash for its first predecessor request.
        lm.ledger_history().insert(Arc::clone(&validated), true);
        // Rippled's getLedgerByHash has a closed-ledger fallback that Quaxar
        // lacks. Without registering here, the exact validator-backed hash
        // becomes invisible to check_acquired once ledger_history sweeps it.
        // This ensures the validation trie can always resolve quorum-backed
        // ledgers via the adaptor's local HashMap (never swept).
        self.validations().register_ledger(&validated);
        lm.mark_ledger_complete(validated.header().seq);
        // Mirrors LedgerMaster::setValidLedger, which invokes both
        // SHAMapStore::onLedgerClosed and AmendmentTable::doValidatedLedger.
        // A lightweight pointer update leaves retention health and amendment
        // state stale after validation-driven acquisition.
        let _ = self.on_validated_ledger(Arc::clone(&validated));
        // `on_validated_ledger` records the ledger close time for generic
        // callers. Restore the quorum-backed signing-time median required by
        // `LedgerMaster::setValidLedger` for validated-age/caught-up checks.
        self.ledger_master_state
            .set_validated_close_time(validated_sign_time);

        // Matches rippled's `LedgerMaster::checkAccept`: visibility is
        // promoted first (above: `setValidLedger` equivalent), then
        // persistence is dispatched via `pendSaveValidated(app_, ledger,
        // true, true)` (LedgerMaster.cpp:976). `is_synchronous=true` here
        // matches that call exactly -- rippled's `pendSaveValidated` still
        // prefers `should_work`/dedup short-circuits over inline execution,
        // and never gates visibility on the save regardless of the flag.
        let persistence_rt = self.build_ledger_persistence_runtime();
        ledger::LedgerPersistence::new(persistence_rt).pend_save_validated(
            Arc::clone(&validated),
            true,
            true,
        );

        // Persistence is dispatched above, after this ledger became visible
        // as validated (matching rippled's setValidLedger-then-
        // pendSaveValidated ordering). The remaining work updates in-memory
        // indexes and runtime mirrors only.

        // Mirror LedgerMaster::checkAccept: median trusted sfLoadFee values
        // for the accepted ledger and its parent, defaulting to the local load
        // base when no validator supplied a load fee. This is remote fee
        // consensus, distinct from the validated ledger base fee below.
        let load_base = self.load_fee_track.load_base();
        let mut validation_fees = self.validations().fees_for_ledger(
            *validated.header().hash.as_uint256(),
            validated.header().seq,
            load_base,
        );
        validation_fees.extend(self.validations().fees_for_ledger(
            *validated.header().parent_hash.as_uint256(),
            validated.header().seq.saturating_sub(1),
            load_base,
        ));
        validation_fees.sort_unstable();
        let remote_fee = validation_fees
            .get(validation_fees.len() / 2)
            .copied()
            .unwrap_or(load_base);
        self.load_fee_track.set_remote_fee(remote_fee);

        // Record the accepted ledger's base fee separately for cluster/base
        // fee tracking and RPC presentation.
        self.load_fee_track
            .update_from_validated_ledger(validated.fees().base);

        // Keep completed inbound entries until the normal InboundLedgers
        // sweep. Rippled leaves completed InboundLedger objects in its map,
        // allowing direct acquire(hash) recovery to return the completed
        // ledger during the remaining sweep lifetime. The registry's
        // acknowledgement flag suppresses duplicate persistence work.

        // Rippled does NOT release ledger maps in checkAccept. The ledger
        // stays in memory with its full SHAMap so that:
        // 1. The validation trie adaptor can build ancestor chains via
        //    hash_of_seq (which walks the state map skip-list)
        // 2. getPreferredLCL can advance past minSeq once the trie is
        //    populated with the new validated ledger
        // Memory is reclaimed by the normal TreeNodeCache/LedgerHistory
        // sweep cycle, matching rippled's nodeFamily_.sweep() cadence.

        tracing::info!(
            target: "consensus",
            seq = validated.header().seq, val_count, quorum,
            "check_accept: validated ledger advanced (synchronous, on validation receipt)"
        );
        tracing::info!(
            target: "lcl_audit",
            validated_hash = %validated.header().hash,
            validated_seq = validated.header().seq,
            last_valid_anchor = ?lm.last_valid_ledger(),
            "LCL_AUDIT validation promotion committed"
        );

        // `checkAccept` advances only validated/publication state. It must not
        // install this ledger as the closed LCL, rebuild the open ledger,
        // change operating mode, or emit a switched-ledger StatusChange;
        // NetworkOpsStrand owns those actions after preferred-LCL selection.
        self.try_advance_publication_serialized();

        // Consensus advancement after validating a new ledger.
        //
        // Rippled parity: checkAccept NEVER touches consensus state or calls
        // startRound/beginConsensus. It promotes the validated ledger in
        // LedgerMaster and calls tryAdvance() to publish it. The consensus
        // state machine is exclusively driven by the timer thread (via
        // timerEntry → checkLedger → handleWrongLedger).
        //
        // In rippled (LedgerMaster.cpp:946), checkAccept:
        //   1. Validates quorum
        //   2. Sets validated ledger (setValidLedger)
        //   3. Calls tryAdvance() (publishes ledgers) ← done above
        //   4. NEVER calls startRound or beginConsensus
        //
        // The consensus timer's `checkLedger` (inside timerEntry, every 1s)
        // detects that the validation trie prefers a newer ledger and triggers
        // handleWrongLedger → SwitchedLedger mode, which advances the round.
        // This is the ONLY correct path for consensus advancement.
        //
        // Previously this code called start_next_round here, which raced with
        // execute_accept's own start_round on the timer thread, causing
        // double-starts and skipped ledgers.
        if let Some(crt) = self.consensus_runtime.as_ref() {
            let current_phase = crt.phase();
            let current_prev = crt.prev_ledger_id();
            let validated_hash = *validated.header().hash.as_uint256();
            tracing::debug!(
                target: "consensus",
                seq = validated.header().seq,
                %validated_hash,
                %current_prev,
                ?current_phase,
                "check_accept: validated ledger promoted (no round restart — timer drives consensus)"
            );
        }
    }

    /// Records the app-visible validated ledger without running heavier
    /// validated-ledger side effects.
    ///
    /// before it can publish available ledgers. The full `on_validated_ledger`
    /// path remains the parity target for those hooks once they are safe to run
    /// outside the catchup hot path.
    pub fn note_validated_ledger_for_sync(&self, ledger: Arc<Ledger>) {
        self.ledger_master_state
            .note_validated_ledger(self.ledger_with_node_fetcher(ledger));
    }

    /// Promotes `NetworkOpsOperatingMode` only after the caller's
    /// NetworkOps-strand reconciliation has committed the accepted LCL. This
    /// method consumes the strand-owned recovery visibility bit; it does not
    /// independently evaluate a preferred-LCL policy.
    pub fn promote_operating_mode_after_accepted_ledger(&self, ledger: &Ledger) {
        let Some(published) = self.published_ledger() else {
            return;
        };
        if published.header().hash != ledger.header().hash {
            return;
        }
        let current_mode = self.network_ops_operating_mode();
        let need_network_ledger = self.need_network_ledger();

        let now_close_time = self.current_close_time_seconds();
        let last_closed_close_time = ledger.header().close_time;
        let close_time_resolution = u32::from(ledger.header().close_time_resolution);
        let current_ledger_fresh = now_close_time
            <= last_closed_close_time.saturating_add(close_time_resolution.saturating_mul(2));

        tracing::debug!(target: "app",
            ?current_mode, need_network_ledger, current_ledger_fresh,
            now_close_time, last_closed_close_time, close_time_resolution,
            "promote_operating_mode: evaluating"
        );

        let mut next_mode = current_mode;
        if matches!(
            next_mode,
            NetworkOpsOperatingMode::Connected | NetworkOpsOperatingMode::Syncing
        ) && !need_network_ledger
        {
            next_mode = NetworkOpsOperatingMode::Tracking;
        }
        if matches!(
            next_mode,
            NetworkOpsOperatingMode::Connected | NetworkOpsOperatingMode::Tracking
        ) && !need_network_ledger
            && current_ledger_fresh
        {
            next_mode = NetworkOpsOperatingMode::Full;
        }

        if next_mode != current_mode {
            let _ = self.set_network_ops_operating_mode_with_reason(next_mode, "accept_promotion");
        }
    }

    pub fn validated_ledger(&self) -> Option<Arc<Ledger>> {
        self.ledger_master_state.validated_ledger()
    }

    pub fn validated_ledger_seq(&self) -> Option<u32> {
        self.ledger_master_state.validated_ledger_seq()
    }

    pub fn accept_standalone_ledger(&self) -> Result<u32, String> {
        if !self.standalone() {
            return Err("ledger_accept requires standalone mode".to_owned());
        }

        let current = self.open_ledger().current();
        let current_idx = current.ledger_current_index;
        let closed_s = self.closed_ledger_seq().unwrap_or(0);
        let validated_s = self.validated_ledger_seq().unwrap_or(0);
        let closed_seq = current_idx
            .max(closed_s.saturating_add(1))
            .max(validated_s.saturating_add(1))
            .max(1);
        let close_time = self.current_close_time_seconds();

        // In standalone mode, transactions are already applied to the open ledger
        // during submit. We take those transactions and re-apply them against the
        // parent ledger to build the closed ledger (matching rippled's standalone
        // acceptLedger which promotes open ledger state directly).
        let parent_ledger = self.closed_ledger().or_else(|| self.validated_ledger());
        let parent = parent_ledger
            .clone()
            .unwrap_or_else(|| Arc::new(Ledger::from_ledger_seq_and_close_time(1, 0, false)));

        // rippled only enters the synchronous NetworkOps batch from ledger
        // close when LedgerMaster has a held transaction set to process.
        let parent_hash = parent.header().hash;
        let mut run_sync_batch = false;
        let _ = self.apply_held_transactions_to_network_ops(parent_hash, |_| {
            run_sync_batch = true;
        });
        if run_sync_batch {
            let _ = self.apply_network_ops_pending_to_open_ledger();
        }

        // Re-read open ledger txs after held transactions were applied.
        use crate::consensus::rcl_consensus::RclConsensusOpenLedgerSource;
        let open_txs: Vec<Arc<protocol::STTx>> = self.open_ledger().current_open_transactions();

        // If no transactions are pending, still advance the ledger (matching rippled)
        // but skip the state rebuild to avoid state map corruption from empty applies.
        if open_txs.is_empty() {
            let closed = {
                let mut ledger = Ledger::from_previous(&parent, close_time);
                ledger.set_accepted(close_time, 0, true);
                Arc::new(ledger)
            };
            tracing::debug!(target: "app", seq = closed_seq, "Standalone ledger closed (empty)");
            let _ = self.process_closed_ledger_txq(closed.as_ref(), false);
            self.on_closed_ledger(Arc::clone(&closed));
            self.on_published_ledger(Arc::clone(&closed));
            // In standalone mode, validate immediately (quorum=0).
            // This matches rippled's standalone acceptLedger which
            // unconditionally validates since there's no network quorum.
            self.on_validated_ledger(Arc::clone(&closed));
            // on_published_ledger above emits the canonical ledgerClosed
            // subscription event for both standalone and normal publication.
            self.promote_operating_mode_after_accepted_ledger(closed.as_ref());
            // Visibility (on_closed_ledger/on_validated_ledger above) already
            // promoted before persistence dispatch. `is_current=true` matches
            // the visibility layer above: `on_validated_ledger` unconditionally
            // inserts into ledger_history with `validated=true` (see its own
            // comment on `--start` mode reachability), so this call must agree
            // with that already-established "current" status.
            ledger::LedgerPersistence::new(self.build_ledger_persistence_runtime())
                .pend_save_validated(Arc::clone(&closed), true, true);
            let next_open_index = closed_seq.saturating_add(1);
            self.clear_open_ledger_account_seqs();
            self.rebuild_open_ledger_after_close(Arc::clone(&closed));
            self.set_status_rpc_current_ledger_index(Some(next_open_index));
            self.set_status_rpc_queue_report(Some(self.tx_q_rpc_report()));
            return Ok(next_open_index);
        }

        // Sequence continuity: `closed_seq` was captured when consensus
        // decided to close this round, but this job runs asynchronously on
        // a JobQueue worker and a concurrent ledger-acquisition/catchup
        // jump can advance `parent` past that point before this job runs.
        // rippled's `doAccept`/`buildLCL` never re-validates against a live
        // "current" parent -- it just builds on the `prevLedger` snapshot
        // it was given. Match that: derive the sequence from `parent`
        // itself instead of hard-failing (and thereby permanently dropping
        // this node out of active consensus) on a stale `closed_seq`.
        let closed_seq = parent.header().seq.saturating_add(1);

        // Apply against the parent's state while exposing the child ledger
        // header. rippled's closed OpenView has this split: SLE reads come
        // from the parent, but transaction code observes the ledger currently
        // being built.
        let application_header = Ledger::from_previous(&parent, close_time).header();
        let mut state_view = ledger::ApplyViewImpl::new_with_header(
            Arc::clone(&parent),
            application_header,
            protocol::ApplyFlags::NONE,
        );

        let mut accepted_entries = Vec::new();
        for st_tx in &open_txs {
            let txn_type = st_tx.get_txn_type();
            // `../rippled/src/xrpld/app/ledger/detail/BuildLedger.cpp::buildLedger`
            // replays through `applyTransaction`, which runs the shared
            // semantic preflight and immutable `invokePreclaim` before any
            // `doApply` mutation. Keep the standalone open-ledger replay on
            // that exact admission boundary; a rejected transaction must not
            // consume a sequence, fee, or tx-map slot in `state_view`.
            let rules = state_view.rules();
            let preflight = transaction_preflight_ter_with_network_id(
                st_tx,
                &rules,
                self.registry.network_id_service.get_network_id(),
            );
            let preclaim = if is_tes_success(preflight) {
                queue_apply_preclaim_ter(&state_view, st_tx, closed_seq, ApplyFlags::NONE)
            } else {
                preflight
            };
            if !is_tes_success(preclaim) && !is_tec_claim(preclaim) {
                tracing::debug!(
                    target: "ledger",
                    closed_seq,
                    tx_id = %st_tx.get_transaction_id(),
                    ?txn_type,
                    ?preclaim,
                    "standalone replay rejected transaction before shell mutation"
                );
                continue;
            }

            let mut attempt_view =
                ledger::FlowSandbox::new_with_flags(&mut state_view, ApplyFlags::NONE);
            let SubmitApplyOutcome {
                result,
                applied,
                delivered_amount,
                prebuilt_outer_metadata,
                applied_batch_inner_transactions,
            } = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim_and_network_id(
                &mut attempt_view,
                st_tx,
                txn_type,
                ApplyFlags::NONE,
                preclaim,
                self.registry.network_id_service.get_network_id(),
            );
            if applied {
                // Keep replay's metadata boundary identical to consensus:
                // build from this transaction's FlowSandbox before its delta
                // is consumed into the ledger accumulator.
                let mut meta = if let Some(metadata) = prebuilt_outer_metadata {
                    attempt_view.apply().map_err(|error| {
                        format!(
                            "standalone accepted Batch {} state commit failed: {error:?}",
                            st_tx.get_transaction_id()
                        )
                    })?;
                    metadata
                } else {
                    attempt_view
                        .apply_with_tx_meta(
                            st_tx.get_transaction_id(),
                            closed_seq,
                            delivered_amount,
                            None,
                            &rules,
                        )
                        .map_err(|error| {
                            format!(
                                "standalone accepted transaction {} metadata failed: {error:?}",
                                st_tx.get_transaction_id()
                            )
                        })?
                };
                let delta_meta_nodes = meta.get_nodes().json(protocol::JsonOptions::NONE);
                let mut serializer = protocol::Serializer::default();
                meta.add_raw(&mut serializer, result, accepted_entries.len() as u32);

                accepted_entries.push(StandaloneAcceptedTx {
                    transaction_id: st_tx.get_transaction_id(),
                    txn: Arc::new(protocol::Serializer::from_bytes(
                        st_tx.get_serializer().data(),
                    )),
                    metadata: Arc::new(serializer),
                    delta_meta_nodes,
                });
                stage_accepted_batch_inner_transactions(
                    &mut accepted_entries,
                    applied_batch_inner_transactions,
                    closed_seq,
                );
            }
        }

        // Build the closed ledger from the parent with accumulated state.
        // from_previous creates a new ledger sharing the parent's state map (CoW).
        let closed = {
            let mut ledger = Ledger::from_previous(&parent, close_time);
            // `OpenView::apply` is the final state commit before publication.
            // Do not expose a ledger whose state table or transaction map was
            // only partially committed. Parity:
            // ../rippled/src/xrpld/app/ledger/detail/BuildLedger.cpp::
            // buildLedgerImpl applies the accumulator before setAccepted.
            state_view
                .table()
                .apply(&mut ledger)
                .map_err(|error| format!("standalone accepted state commit failed: {error:?}"))?;
            for entry in &accepted_entries {
                ledger
                    .raw_tx_insert(
                        entry.transaction_id,
                        Arc::clone(&entry.txn),
                        Some(Arc::clone(&entry.metadata)),
                    )
                    .map_err(|error| {
                        format!(
                            "standalone accepted transaction {} insert failed: {error:?}",
                            entry.transaction_id
                        )
                    })?;
            }
            ledger.set_accepted(close_time, 0, true);
            // Mark state_map unbacked: all nodes are in memory (never flushed to NuDB
            // in standalone mode). Without this, subsequent reads from child ledgers
            // would try to fetch nodes from NuDB (which doesn't have them) and fail.
            ledger.state_map_mut().set_unbacked();
            Arc::new(ledger)
        };

        // Parity: ../rippled/src/xrpld/app/ledger/detail/TransactionMaster.cpp::
        // TransactionMaster::inLedger is a post-commit observation. Every
        // state-table and raw transaction-map commit above is fallible, so do
        // not promote a transaction or publish an accepted ledger prefix until
        // the closed ledger has been completely materialized.
        for (index, entry) in accepted_entries.iter().enumerate() {
            let _ = self.transaction_master.in_ledger(
                entry.transaction_id,
                closed_seq,
                Some(index as u32),
                Some(self.registry.network_id_service.get_network_id()),
            );
        }

        let tx_count = accepted_entries.len();
        tracing::info!(target: "app", seq = closed_seq, tx_count, close_time, "Standalone ledger closed");

        let _ = self.process_closed_ledger_txq(closed.as_ref(), false);
        self.on_closed_ledger(Arc::clone(&closed));
        self.on_published_ledger(Arc::clone(&closed));
        let _ = self.on_validated_ledger(Arc::clone(&closed));
        self.promote_operating_mode_after_accepted_ledger(closed.as_ref());

        // Sweep local_txs: remove transactions that are now in the closed ledger.
        // Without this, rebuild_open_ledger_after_close would re-add them to the
        // next open ledger causing duplicate application on subsequent accepts.
        let _ = self.update_local_tx(closed.as_ref());

        // Visibility (on_closed_ledger/on_validated_ledger above) already
        // promoted before persistence dispatch, matching rippled's
        // setValidLedger-before-pendSaveValidated ordering. `is_current=true`
        // matches the visibility layer above: `on_validated_ledger`
        // unconditionally inserts with `validated=true` (see its own comment
        // on why `--start` mode reachability requires this), so this call
        // must agree with that already-established "current" status rather
        // than diverge from it -- unlike rippled, where a single `isCurrent`
        // parameter drives both the history insert and this dispatch
        // together (LedgerMaster.cpp:828-841), Quaxar's `on_validated_ledger`
        // always inserts as current regardless of caller context.
        ledger::LedgerPersistence::new(self.build_ledger_persistence_runtime())
            .pend_save_validated(Arc::clone(&closed), true, true);

        let next_open_index = closed_seq.saturating_add(1);
        self.clear_open_ledger_account_seqs();
        self.rebuild_open_ledger_after_close(Arc::clone(&closed));
        self.set_status_rpc_current_ledger_index(Some(next_open_index));
        self.set_status_rpc_queue_report(Some(self.tx_q_rpc_report()));

        Ok(next_open_index)
    }

    pub fn accept_ledger(
        &self,
        closed_seq: u32,
        close_time: u32,
        base_fee_drops: u64,
    ) -> Result<u32, String> {
        // Standalone/test call sites have no separate consensus round with
        // an already-captured transaction set, so read the open ledger's
        // current contents directly -- there is no concurrent reset racing
        // this synchronous call the way there is for the real `--start`
        // mode consensus path (see `accept_ledger_with_txns`). Unlike that
        // real path, there is no multi-node determinism concern here (this
        // is a single-node helper), so the close-resolution schedule is
        // simply pinned at the reference's `kLedgerDefaultTimeResolution`
        // (30s) with `closeTimeCorrect = true`, matching this function's
        // previous (hardcoded) behavior exactly.
        let txns = self.registry.open_ledger.current_open_transactions();
        self.accept_ledger_with_txns(closed_seq, close_time, 30, true, base_fee_drops, txns)
    }

    /// Builds and persists the real accepted ledger from `txns` -- the
    /// exact transaction set that should be applied, matching the
    /// reference's `RCLConsensus::Adaptor::doAccept` building
    /// `retriableTxs` from `result.txns` (itself captured earlier, in
    /// `onClose`, from `app_.getOpenLedger().current()->txs`). Callers
    /// driven by live consensus MUST pass the transaction set captured at
    /// `on_close` time, NOT a fresh read of the open ledger's current
    /// contents -- by the time this runs asynchronously on a JobQueue worker,
    /// new local transactions may already have been added. The caller must
    /// therefore apply exactly the captured set. Live consensus callers use
    /// `accept_ledger_with_txns_outcome` and rebuild the shared open ledger
    /// only after filtering completed transactions and carrying retries.
    ///
    /// Matches rippled's `doAccept` → `buildLCL` → `stateMap().flushDirty()`
    /// which persists all dirty SHAMap nodes to the node store after building.
    pub fn accept_ledger_with_txns(
        &self,
        closed_seq: u32,
        close_time: u32,
        close_resolution: u8,
        correct_close_time: bool,
        base_fee_drops: u64,
        txns: Vec<Arc<protocol::STTx>>,
    ) -> Result<u32, String> {
        let outcome = self.accept_ledger_with_txns_outcome(
            closed_seq,
            close_time,
            close_resolution,
            correct_close_time,
            base_fee_drops,
            txns,
        )?;
        let closed = self
            .closed_ledger()
            .ok_or_else(|| "accepted ledger missing after build".to_owned())?;
        self.rebuild_open_ledger_after_close(Arc::clone(&closed));
        self.set_status_rpc_current_ledger_index(Some(outcome.next_open_index));
        self.set_status_rpc_queue_report(Some(self.tx_q_rpc_report()));
        Ok(outcome.next_open_index)
    }

    pub(crate) fn accept_ledger_with_txns_outcome(
        &self,
        closed_seq: u32,
        close_time: u32,
        close_resolution: u8,
        correct_close_time: bool,
        base_fee_drops: u64,
        txns: Vec<Arc<protocol::STTx>>,
    ) -> Result<AcceptedLedgerOutcome, String> {
        self.accept_ledger_with_txns_outcome_on_parent(
            self.closed_ledger().or_else(|| self.validated_ledger()),
            AcceptedLedgerLclInstall::Unconditional,
            closed_seq,
            close_time,
            close_resolution,
            correct_close_time,
            base_fee_drops,
            txns,
        )
        .map_err(|error| format!("accepted ledger build failed: {error:?}"))
    }

    /// Builds a consensus result on the exact parent captured by `on_accept`.
    ///
    /// Rippled `doAccept` builds on generic Consensus's captured `prevLedger`
    /// even when it differs from the global closed slot during legitimate
    /// WrongLedger/SwitchedLedger recovery. The child is deliberately not
    /// installed here: `RCLConsensus` performs `consensusBuilt`, accepts the
    /// new open ledger, then switches the closed LCL, matching the reference
    /// ordering.
    pub(crate) fn accept_ledger_with_txns_outcome_from_consensus_parent(
        &self,
        parent_ledger: Arc<Ledger>,
        closed_seq: u32,
        close_time: u32,
        close_resolution: u8,
        correct_close_time: bool,
        base_fee_drops: u64,
        txns: Vec<Arc<protocol::STTx>>,
    ) -> Result<AcceptedLedgerOutcome, crate::bootstrap::build_ledger::BuildLedgerError> {
        self.accept_ledger_with_txns_outcome_on_parent(
            Some(parent_ledger),
            AcceptedLedgerLclInstall::Deferred,
            closed_seq,
            close_time,
            close_resolution,
            correct_close_time,
            base_fee_drops,
            txns,
        )
    }

    /// Install a consensus-built child after the rippled-equivalent
    /// `consensusBuilt` and `OpenLedger::accept` steps. Mirrors
    /// `LedgerMaster::switchLCL` in `doAccept` without a separate
    /// global-parent rejection.
    pub(crate) fn install_consensus_child(&self, child: Arc<Ledger>) {
        // Mirrors LedgerMaster::switchLCL from rippled `doAccept`: reject an
        // invalid LCL object, then install the captured generic Consensus
        // child without a separate global-parent rejection gate and run the
        // immediate post-switch checkAccept.
        assert!(
            child.is_immutable(),
            "xrpl::LedgerMaster::switchLCL : mutable consensus child"
        );
        assert!(
            !child.open(),
            "xrpl::LedgerMaster::switchLCL : open consensus child"
        );
        self.on_closed_ledger_after_store(Arc::clone(&child));
        if let Some(runtime) = self.ledger_master_runtime() {
            let ledger_master = runtime.ledger_master();
            if self.standalone() {
                // Mirrors LedgerMaster::switchLCL standalone branch:
                // setFullLedger(lastClosed, true, false); tryAdvance().
                let persistence =
                    ledger::LedgerPersistence::new(self.build_ledger_persistence_runtime());
                let _ = ledger_master.set_full_ledger(
                    &persistence,
                    Arc::clone(&child),
                    true,
                    false,
                    None,
                    None,
                );
                if ledger_master.try_advance() {
                    let _ = ledger_master.do_advance();
                }
                if let Some(published) = ledger_master.published_ledger() {
                    self.on_published_ledger(published);
                }
            } else {
                // Non-standalone switchLCL immediately checks validations
                // for the newly relevant LCL.
                self.check_accept_ledger(child);
            }
        }
    }

    fn accept_ledger_with_txns_outcome_on_parent(
        &self,
        parent_ledger: Option<Arc<Ledger>>,
        lcl_install: AcceptedLedgerLclInstall,
        closed_seq: u32,
        close_time: u32,
        close_resolution: u8,
        correct_close_time: bool,
        _base_fee_drops: u64,
        txns: Vec<Arc<protocol::STTx>>,
    ) -> Result<AcceptedLedgerOutcome, crate::bootstrap::build_ledger::BuildLedgerError> {
        // Ensure the parent ledger has a node_fetcher attached. The
        // closed_ledger slot may hold a ledger whose fetcher was not set
        // (e.g. when check_accept_ledger promotes an acquired ledger via
        // on_closed_ledger but ledger_with_node_fetcher skips re-attaching
        // the store fetcher due to the existing acquisition-time fetcher
        // being dropped). Without a fetcher, build_ledger_from_view's
        // update_skip_list fails with MissingNode on the first traversal
        // into a released subtree.
        let parent_ledger = parent_ledger.map(|l| self.ledger_with_node_fetcher(l));

        // Diagnostic: log parent state before building child ledger
        if let Some(ref parent) = parent_ledger {
            let mut loaded = 0u32;
            let mut non_empty = 0u32;
            for branch in 0..16 {
                if !parent.state_map().root().is_empty_branch(branch) {
                    non_empty += 1;
                    if parent.state_map().root().get_child(branch).is_some() {
                        loaded += 1;
                    }
                }
            }
            tracing::info!(
                target: "ledger",
                parent_seq = parent.header().seq,
                parent_hash = %parent.header().hash,
                backed = parent.state_map().backed(),
                has_fetcher = parent.has_node_fetcher(),
                has_writer = parent.has_node_writer(),
                root_non_empty_branches = non_empty,
                root_loaded_children = loaded,
                "[accept] parent ledger state before build"
            );
        } else {
            tracing::info!(target: "ledger", "[accept] NO parent ledger — building genesis");
        }

        let closed_seq = parent_ledger
            .as_ref()
            .map(|parent| parent.header().seq.saturating_add(1))
            .unwrap_or(closed_seq);
        let accept_journal = self.registry.logs.journal("accept_ledger");
        let next_open_parent_hash = self
            .closed_ledger()
            .or_else(|| self.validated_ledger())
            .map(|ledger| ledger.header().hash)
            .unwrap_or_default();

        let _ = self.apply_held_transactions_to_network_ops(next_open_parent_hash, |_sync| {});
        let mut accepted_entries = Vec::new();
        // rippled BuildLedger retries once while progress is possible, then
        // performs a final non-retry pass that classifies remaining TERs as
        // failures. Use the shared OpenLedger/BuildLedger parity constants.
        let mut pending_txs = txns;
        let mut certain_retry = true;
        let mut completed_transaction_ids = std::collections::HashSet::new();
        let mut failed_txns: Vec<(Uint256, protocol::Ter)> = Vec::new();

        // Create a mutable view on the parent ledger to accumulate state changes
        let state_view_base = parent_ledger
            .clone()
            .unwrap_or_else(|| Arc::new(Ledger::from_ledger_seq_and_close_time(1, 0, false)));
        let application_header = parent_ledger
            .as_ref()
            .map(|parent| Ledger::from_previous(parent, close_time).header())
            .unwrap_or_else(|| {
                Ledger::from_ledger_seq_and_close_time(closed_seq, close_time, false).header()
            });
        let state_view = std::sync::Mutex::new(ledger::ApplyViewImpl::new_with_header(
            Arc::clone(&state_view_base),
            application_header,
            protocol::ApplyFlags::NONE,
        ));

        // Matches the reference's `RCLConsensus::Adaptor::doAccept`: the real
        // ledger build applies `result.txns` -- the SAME transaction set
        // `onClose` captured from `app_.getOpenLedger().current()->txs` --
        // NOT a separately-drained submission queue. `pending_transactions`
        // (this port's equivalent of `NetworkOPsImp::transactions_`) is
        // purely a submission-batching buffer that RPC submit already
        // applies non-destructively onto `self.registry.open_ledger`
        // (matching `NetworkOPsImp::apply`'s `getOpenLedger().modify(...)`);
        // it is NOT the source of what gets built into a real ledger. Using
        // it here (as an earlier version of this function did, via
        // `apply_network_ops_pending_with`) raced the RPC submit path's own
        // drain of that same queue -- whichever caller ran first each round
        // won, and since RPC submit runs synchronously on every single
        // submit call, it almost always won, silently starving every
        // accept_ledger call of the transactions it needed to persist.
        for pass in 0..crate::LEDGER_TOTAL_PASSES {
            if pending_txs.is_empty() {
                break;
            }

            tracing::debug!(
                target: "ledger",
                closed_seq,
                pass,
                certain_retry,
                transaction_count = pending_txs.len(),
                "consensus ledger application pass started"
            );
            let mut changes = 0usize;
            let mut retry_txs = Vec::new();
            let open_txs = std::mem::take(&mut pending_txs);
            for (input_position, sttx) in open_txs.into_iter().enumerate() {
                let transaction_id = sttx.get_hash(protocol::HashPrefix::TransactionId);
                let parent_has_transaction = parent_ledger
                    .as_ref()
                    .map(|parent| {
                        parent.try_tx_exists(transaction_id).map_err(|error| {
                            crate::bootstrap::build_ledger::BuildLedgerError::View(format!(
                                "cannot admit consensus transaction {transaction_id}: captured parent transaction map is unreadable: {error:?}"
                            ))
                        })
                    })
                    .transpose()?;
                if pass == 0 && parent_has_transaction == Some(true) {
                    emit_candidate_admission_diagnostic(
                        CandidateAdmissionDiagnostic::skipped_existing(
                            transaction_id,
                            closed_seq,
                            sttx.get_seq_proxy().value(),
                            pass,
                        ),
                    );
                    completed_transaction_ids.insert(transaction_id);
                    continue;
                }
                let mut view = state_view
                    .lock()
                    .expect("state view mutex must not be poisoned");
                let txn_type = sttx.get_txn_type();
                // `apply_submit_transactor_shell` (not the bare
                // `handle_real_dispatch`) is required here: it implements the
                // reference's `Transactor::apply` generic preamble --
                // `consumeSeqProxy` (incrementing the SOURCE account's own
                // `sfSequence`, which no per-transaction-type handler does on
                // its own) and `payFee` (deducting the fee from the source's
                // balance) -- BEFORE dispatching to the transaction-type
                // handler. Calling `handle_real_dispatch` directly here (as an
                // earlier version of this function did) skipped that preamble
                // entirely, so successfully-applied transactions never
                // incremented their sender's sequence number.
                let retry_flags =
                    crate::bootstrap::build_ledger::canonical_retry_flags(certain_retry);
                let rules = view.rules();
                let preflight = transaction_preflight_ter_with_flags_and_network_id(
                    &sttx,
                    &rules,
                    retry_flags,
                    self.registry.network_id_service.get_network_id(),
                );
                let preclaim = is_tes_success(preflight).then(|| {
                    queue_apply_preclaim_ter_with_load_fee(
                        &*view,
                        &sttx,
                        closed_seq,
                        retry_flags,
                        self.load_fee_track.as_ref(),
                    )
                });
                // `doApply` admits every tes/tec PreclaimResult. Ordinary tec
                // remains unapplied under TapRetry, while persistent cleanup
                // tec values may still commit their reset/deletion state.
                let preclaim_admitted =
                    preclaim.is_some_and(|ter| is_tes_success(ter) || is_tec_claim(ter));
                let (
                    result,
                    applied,
                    applied_batch_inner_transactions,
                    transaction_meta,
                    replayed_threaded_entry,
                ) = if preclaim_admitted {
                    let mut attempt_view =
                        ledger::FlowSandbox::new_with_flags(&mut *view, retry_flags);
                    let SubmitApplyOutcome {
                        result,
                        applied,
                        delivered_amount,
                        prebuilt_outer_metadata,
                        applied_batch_inner_transactions,
                    } = apply_submit_transactor_shell_with_flags_batch_outcome_and_preclaim_and_network_id(
                        &mut attempt_view,
                        &sttx,
                        txn_type,
                        retry_flags,
                        preclaim.expect("preclaim-admitted transaction has a preclaim result"),
                        self.registry.network_id_service.get_network_id(),
                    );
                    let replayed_threaded_entry = applied
                        .then(|| {
                            attempt_view.replayed_threaded_entry(transaction_id, closed_seq, &rules)
                        })
                        .flatten();
                    let transaction_meta = if replayed_threaded_entry.is_none() && applied {
                        // rippled's ApplyStateTable::apply builds TxMeta from
                        // this transaction's state-table delta before it
                        // serializes rawTxInsert and commits the delta. Do
                        // not rebuild an empty TxMeta after this consuming
                        // FlowSandbox commit.
                        let meta = if let Some(metadata) = prebuilt_outer_metadata {
                            // The Batch outer and each applied inner already
                            // crossed their own ApplyStateTable threading
                            // boundary. Only consume the aggregate sandbox;
                            // threading it with the outer ID here would erase
                            // the canonical inner transaction chain.
                            attempt_view.apply().map_err(|error| {
                                crate::bootstrap::build_ledger::BuildLedgerError::View(format!(
                                    "failed to commit accepted Batch {transaction_id}: {error:?}"
                                ))
                            })?;
                            metadata
                        } else {
                            attempt_view
                                .apply_with_tx_meta(
                                    transaction_id,
                                    closed_seq,
                                    delivered_amount,
                                    None,
                                    &rules,
                                )
                                .map_err(|error| {
                                    crate::bootstrap::build_ledger::BuildLedgerError::View(format!(
                                        "failed to build accepted transaction metadata {transaction_id}: {error:?}"
                                    ))
                                })?
                        };
                        Some(meta)
                    } else {
                        None
                    };
                    (
                        result,
                        applied,
                        applied_batch_inner_transactions,
                        transaction_meta,
                        replayed_threaded_entry,
                    )
                } else {
                    (preclaim.unwrap_or(preflight), false, Vec::new(), None, None)
                };
                let apply_ter = preclaim_admitted.then_some(result);
                drop(view);
                if let Some((entry_key, prior_seq)) = replayed_threaded_entry {
                    completed_transaction_ids.insert(transaction_id);
                    emit_candidate_admission_diagnostic(
                        CandidateAdmissionDiagnostic::skipped_existing(
                            transaction_id,
                            closed_seq,
                            sttx.get_seq_proxy().value(),
                            pass,
                        ),
                    );
                    tracing::warn!(
                        target: "ledger",
                        closed_seq,
                        pass,
                        tx_id = %transaction_id,
                        entry_key = %entry_key,
                        prior_seq,
                        "discarded replay whose state entry was already threaded in parent history"
                    );
                    continue;
                }
                if !applied {
                    let retryable = matches!(
                        crate::bootstrap::build_ledger::canonical_retry_disposition(
                            ApplyResult::new(result, false, false)
                        ),
                        crate::bootstrap::build_ledger::CanonicalRetryDisposition::Retry
                    );
                    let decision = if retryable {
                        CandidateDiagnosticDecision::Retry
                    } else {
                        CandidateDiagnosticDecision::Terminal
                    };
                    emit_candidate_admission_diagnostic(CandidateAdmissionDiagnostic::attempted(
                        transaction_id,
                        closed_seq,
                        sttx.get_seq_proxy().value(),
                        pass,
                        preflight,
                        preclaim,
                        apply_ter,
                        decision,
                        None,
                    ));
                    tracing::debug!(
                        target: "lcl_audit",
                        closed_seq,
                        pass,
                        input_position,
                        tx_id = %transaction_id,
                        account = %sttx.get_account_id(protocol::get_field_by_symbol("sfAccount")),
                        seq_proxy = sttx.get_seq_proxy().value(),
                        seq_proxy_is_ticket = sttx.get_seq_proxy().is_ticket(),
                        txn_type = ?txn_type,
                        preflight = ?preflight,
                        preclaim = ?preclaim,
                        apply_ter = ?apply_ter,
                        result = ?result,
                        decision = ?decision,
                        "LCL_AUDIT consensus transaction application result"
                    );
                    if retryable {
                        // rippled::applyTransaction retries an unapplied `tec`
                        // from a TapRetry pass; it becomes fee-claiming only in
                        // the final non-retry pass.
                        retry_txs.push(sttx);
                    } else {
                        completed_transaction_ids.insert(transaction_id);
                        failed_txns.push((transaction_id, result));
                        tracing::warn!(
                            target: "ledger",
                            closed_seq,
                            pass,
                            tx_id = %transaction_id,
                            account = %sttx.get_account_id(protocol::get_field_by_symbol("sfAccount")),
                            seq = sttx.get_seq_proxy().value(),
                            ?txn_type,
                            ?result,
                            "consensus transaction failed"
                        );
                    }
                    continue;
                }
                changes += 1;
                completed_transaction_ids.insert(transaction_id);

                let index = accepted_entries.len();
                tracing::debug!(
                    target: "lcl_audit",
                    closed_seq,
                    pass,
                    input_position,
                    transaction_index = index,
                    tx_id = %transaction_id,
                    account = %sttx.get_account_id(protocol::get_field_by_symbol("sfAccount")),
                    seq_proxy = sttx.get_seq_proxy().value(),
                    seq_proxy_is_ticket = sttx.get_seq_proxy().is_ticket(),
                    txn_type = ?txn_type,
                    preflight = ?preflight,
                    preclaim = ?preclaim,
                    apply_ter = ?apply_ter,
                    result = ?result,
                    "LCL_AUDIT consensus transaction application accepted"
                );
                emit_candidate_admission_diagnostic(CandidateAdmissionDiagnostic::attempted(
                    transaction_id,
                    closed_seq,
                    sttx.get_seq_proxy().value(),
                    pass,
                    preflight,
                    preclaim,
                    apply_ter,
                    CandidateDiagnosticDecision::Accepted,
                    Some(index as u32),
                ));
                let mut meta = transaction_meta.expect(
                    "accepted consensus transaction must retain its pre-commit state delta",
                );
                let delta_meta_nodes = meta.get_nodes().json(protocol::JsonOptions::NONE);
                let mut serializer = protocol::Serializer::default();
                meta.add_raw(&mut serializer, result, index as u32);

                accepted_entries.push(StandaloneAcceptedTx {
                    transaction_id,
                    txn: Arc::new(protocol::Serializer::from_bytes(
                        sttx.get_serializer().data(),
                    )),
                    metadata: Arc::new(serializer),
                    delta_meta_nodes,
                });
                stage_accepted_batch_inner_transactions(
                    &mut accepted_entries,
                    applied_batch_inner_transactions,
                    closed_seq,
                );
            }

            tracing::debug!(
                target: "ledger",
                closed_seq,
                pass,
                changes,
                retries = retry_txs.len(),
                "consensus ledger application pass completed"
            );
            pending_txs = retry_txs;
            if !crate::bootstrap::build_ledger::advance_canonical_retry_pass(
                changes,
                pass,
                &mut certain_retry,
            ) {
                break;
            }
        }

        debug_assert!(pending_txs.is_empty() || !certain_retry);

        if !failed_txns.is_empty() {
            tracing::warn!(
                target: "ledger",
                closed_seq,
                failed_count = failed_txns.len(),
                "consensus ledger application discarded failed transactions"
            );
        }

        let state_table = state_view
            .into_inner()
            .expect("state view mutex must not be poisoned")
            .into_table();
        let mut state_table = Some(state_table);
        let needs_durable_persistence = self.node_store().is_some()
            || self
                .shared_consensus_node_store
                .read()
                .ok()
                .is_some_and(|guard| guard.is_some());
        let closed = match parent_ledger {
            Some(parent) => crate::build_ledger_from_view(
                Arc::clone(&parent),
                close_time,
                correct_close_time,
                close_resolution,
                accept_journal.as_ref(),
                |built| {
                    StandaloneLedgerBuildView::from_base(
                        Arc::new(built.clone()),
                        &accepted_entries,
                        state_table.take(),
                    )
                },
                move |ledger| {
                    if !ledger.has_node_fetcher() {
                        if let Some(fetcher) = self.node_fetcher_from_store() {
                            ledger.set_node_fetcher(fetcher);
                        }
                    }
                    if needs_durable_persistence {
                        if !ledger.has_node_writer_result() {
                            let writer = self.node_writer_result_from_store().ok_or_else(|| {
                                crate::bootstrap::build_ledger::BuildLedgerError::Persist(
                                    "missing fallible node writer for consensus ledger".to_owned(),
                                )
                            })?;
                            ledger.set_node_writer_result(writer);
                        }
                        if !ledger.has_node_batch_writer_result() {
                            let writer =
                                self.node_batch_writer_result_from_store().ok_or_else(|| {
                                    crate::bootstrap::build_ledger::BuildLedgerError::Persist(
                                        "missing fallible node batch writer for consensus ledger"
                                            .to_owned(),
                                    )
                                })?;
                            ledger.set_node_batch_writer_result(writer);
                        }
                        ledger.state_map_mut().set_backed();
                        ledger.tx_map_mut().set_backed();
                        ledger
                            .persist_dirty_nodes_to_store_result(self.shared_tree_cache())
                            .map_err(crate::bootstrap::build_ledger::BuildLedgerError::Persist)?;
                    }
                    Ok(0)
                },
                |_ledger| Ok(0),
                |_ledger| {},
            )?,
            None => {
                let mut closed =
                    Ledger::from_ledger_seq_and_close_time(closed_seq, close_time, false);
                crate::BuildLedgerView::apply_to_ledger(
                    StandaloneLedgerBuildView::from_base(
                        Arc::new(closed.clone()),
                        &accepted_entries,
                        state_table.take(),
                    ),
                    &mut closed,
                )?;
                closed.set_accepted(close_time, close_resolution, correct_close_time);
                Arc::new(closed)
            }
        };

        for (index, entry) in accepted_entries.iter().enumerate() {
            let _ = self.transaction_master.in_ledger(
                entry.transaction_id,
                closed_seq,
                Some(index as u32),
                Some(self.registry.network_id_service.get_network_id()),
            );

            if let Some(publisher) = &self.ledger_delta_publisher {
                let mut tx_json = protocol::JsonValue::Object(std::collections::BTreeMap::new());
                if let protocol::JsonValue::Object(map) = &mut tx_json {
                    map.insert(
                        "transaction".to_string(),
                        protocol::JsonValue::String(entry.transaction_id.to_string()),
                    );
                    map.insert("meta".to_string(), entry.delta_meta_nodes.clone());
                }
                let mut delta_msg = protocol::JsonValue::Object(std::collections::BTreeMap::new());
                if let protocol::JsonValue::Object(map) = &mut delta_msg {
                    map.insert(
                        "type".to_string(),
                        protocol::JsonValue::String("ledgerDelta".to_string()),
                    );
                    map.insert(
                        "ledger_index".to_string(),
                        protocol::JsonValue::Unsigned(closed_seq as u64),
                    );
                    map.insert("transaction".to_string(), tx_json);
                }
                if let Err(payload) =
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| publisher(delta_msg)))
                {
                    let message = payload
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| {
                            payload
                                .downcast_ref::<&str>()
                                .map(|message| (*message).to_owned())
                        })
                        .unwrap_or_else(|| "non-string panic payload".to_owned());
                    tracing::error!(
                        target: "ledger",
                        closed_seq,
                        tx_id = %entry.transaction_id,
                        %message,
                        "ledger delta publisher panicked after candidate ledger materialization"
                    );
                }
            }
        }

        let tx_count = accepted_entries.len();
        tracing::info!(target: "app", seq = closed_seq, tx_count, close_time, "Ledger closed");

        let _ = self.process_closed_ledger_txq(closed.as_ref(), false);

        // Register the built ledger in ledger_history so that
        // get_cached_ledger_by_hash / get_cached_ledger_by_seq can find it.
        // The live consensus owner calls `record_consensus_built_ledger`
        // immediately after construction, where the insert and built-ledger
        // bookkeeping occur atomically with the required checkAccept scan.

        // A locally accepted consensus result is an LCL candidate, not proof
        // that this exact ledger has network quorum. The active consensus path
        // defers installation until after `consensusBuilt` and open-ledger
        // acceptance, matching rippled `doAccept`. Legacy callers retain the
        // historical unconditional promotion behavior.
        if lcl_install == AcceptedLedgerLclInstall::Unconditional {
            self.on_closed_ledger(Arc::clone(&closed));
        }

        // Sweep local_txs: remove transactions that are now in the closed ledger.
        // Without this, rebuild_open_ledger_after_close would re-add them to the
        // next open ledger causing duplicate application on subsequent accepts.
        let _ = self.update_local_tx(closed.as_ref());

        // In deferred consensus acceptance, rippled switchLCL's standalone
        // branch performs the only setFullLedger/tryAdvance persistence after
        // the child is installed. Persisting here first would mark the hash
        // saved while still unvalidated and suppress that authoritative save.
        if self.standalone() && lcl_install == AcceptedLedgerLclInstall::Unconditional {
            // Visibility (on_closed_ledger above) already promoted before
            // persistence dispatch here. `is_current=false` matches this
            // path's actual visibility state: unlike the accept_standalone_
            // ledger call site, this function never calls on_validated_ledger
            // -- record_consensus_built_ledger (called earlier by this same
            // build) inserts into ledger_history with `validated=false`
            // (pre-validation insert), matching rippled's storeLedger
            // pattern. Passing `is_current=true` here would misrepresent
            // this ledger as already validated when it is not.
            ledger::LedgerPersistence::new(self.build_ledger_persistence_runtime())
                .pend_save_validated(Arc::clone(&closed), true, false);
        }

        let next_open_index = closed_seq.saturating_add(1);
        // The live consensus caller rebuilds the shared open ledger exactly
        // once, after it receives these completed and retry outcomes. Doing
        // so here would discard peer-sourced retry candidates before they
        // can be retained for the next open ledger.

        Ok(AcceptedLedgerOutcome {
            closed,
            next_open_index,
            completed_transaction_ids,
            retry_transactions: pending_txs,
        })
    }

    pub fn is_shamap_store_stopping(&self) -> Option<bool> {
        self.shamap_store_service
            .as_ref()
            .map(|service| service.is_stopping())
    }

    pub fn signal_stop(&self, reason: impl Into<String>) -> bool {
        tracing::info!(target: "app", "Node shutting down");
        self.stop_tree.signal_stop(reason)
    }

    pub fn is_stopping(&self) -> bool {
        self.stop_tree.is_stopping()
    }

    pub fn stop_reason(&self) -> Option<String> {
        self.stop_tree.reason()
    }
}

impl crate::RclValidationAcceptanceSink for ApplicationRoot {
    /// Matches rippled's `NetworkOPsImp::recvValidation` calling
    /// `app_.getLedgerMaster().checkAccept(ledgerHash, ledgerSeq)`
    /// synchronously on every accepted validation.
    fn check_accept(&self, ledger_hash: Uint256, ledger_seq: u32) {
        self.check_accept_hash_seq(ledger_hash, ledger_seq);
    }
}

impl TransactionCloseTimeSource for ApplicationRoot {
    fn close_time_for_ledger_seq(&self, ledger_seq: u32) -> Option<i64> {
        self.transaction_close_time_seconds(ledger_seq)
    }
}

impl QueueTxQClosedLedgerAppSource<AppClosedLedgerTxQView<'_>> for ApplicationRoot {
    fn validated_fee_levels(&self, view: &AppClosedLedgerTxQView<'_>) -> Vec<u64> {
        self.validated_fee_levels_for_closed_ledger(view.ledger)
    }
}

impl ServiceRegistry for ApplicationRoot {
    type CollectorManager = CollectorManager;
    type NodeFamily = Option<Arc<dyn NodeFamilyRuntime>>;
    type TimeKeeper = Arc<TimeKeeper<SystemTimeKeeperClock>>;
    type JobQueue = JobQueue;
    type TempNodeCache = Arc<shamap::tree_node_cache::TreeNodeCache>;
    type CachedSles = Arc<ledger::CachedSles>;
    type NetworkIdService = FixedNetworkIdService;
    type AmendmentTable = Arc<AmendmentStatus>;
    type HashRouter = Arc<HashRouter>;
    type LoadFeeTrack = Arc<SharedLoadFeeTrack>;
    type LoadManager = LoadManager;
    type Validations = SharedAppValidations<SystemTimeKeeperClock>;
    type ValidatorList = Arc<ValidatorList>;
    type ValidatorSite = ValidatorSite;
    type ManifestCache = ManifestCache;
    type Overlay = Option<Arc<dyn OverlayStatusSource>>;
    type Cluster = Cluster;
    type PeerReservationTable = PeerReservationTable<PublicKey>;
    type ResourceManager = Arc<resource::ResourceManager>;
    type NodeStore = Option<crate::shamap::shamap_store_backend::SHAMapStoreNodeStore>;
    type ShamapStore = Option<Arc<SHAMapStoreService>>;
    type RelationalDatabase =
        Option<Arc<crate::shamap::shamap_store_relational::SqliteSHAMapStoreRelational>>;
    type InboundLedgers = AppInboundLedgers;
    type InboundTransactions = AppInboundTransactions;
    type AcceptedLedgerCache = AppAcceptedLedgerCache;
    type LedgerMaster = Arc<SharedLedgerMasterState>;
    type LedgerCleaner = Arc<ledger::LedgerCleaner>;
    type LedgerReplayer = Arc<Mutex<ledger::LedgerReplayer>>;
    type PendingSaves = Arc<ledger::PendingSaves>;
    type OpenLedger = SharedAppOpenLedger;
    type NetworkOps = Arc<SharedNetworkOpsState>;
    type OrderBookDb = Arc<ledger::OrderBookDB>;
    type TransactionMaster = Arc<TransactionMaster>;
    type TxQ = SharedAppTxQ;
    type PathRequestManager = Arc<crate::paths::PathRequestManager>;
    type ServerHandler = Arc<AppServerHandler>;
    type PerfLog = Arc<PerfLogImp>;
    type Journal = Arc<crate::state::app_registry::AppJournal>;
    type IoContext = RuntimeBindings;
    type Config = AppConfig;
    type Logs = Arc<AppLogs>;
    type TrapTxId = Uint256;
    type WalletDb = Arc<DatabaseCon>;
    type Application = ApplicationRoot;

    fn get_collector_manager(&self) -> &Self::CollectorManager {
        &self.collector_manager
    }

    fn get_node_family(&self) -> &Self::NodeFamily {
        &self.node_family
    }

    fn get_time_keeper(&self) -> &Self::TimeKeeper {
        &self.time_keeper
    }

    fn get_job_queue(&self) -> &Self::JobQueue {
        &self.job_queue
    }

    fn get_temp_node_cache(&self) -> &Self::TempNodeCache {
        &self.registry.temp_node_cache
    }

    fn get_cached_sles(&self) -> &Self::CachedSles {
        &self.registry.cached_sles
    }

    fn get_network_id_service(&self) -> &Self::NetworkIdService {
        &self.registry.network_id_service
    }

    fn get_amendment_table(&self) -> &Self::AmendmentTable {
        &self.amendment_status
    }

    fn get_hash_router(&self) -> &Self::HashRouter {
        &self.registry.hash_router
    }

    fn get_fee_track(&self) -> &Self::LoadFeeTrack {
        &self.load_fee_track
    }

    fn get_load_manager(&self) -> &Self::LoadManager {
        &self.load_manager
    }

    fn get_validations(&self) -> &Self::Validations {
        &self.validations
    }

    fn get_validators(&self) -> &Self::ValidatorList {
        &self.validators
    }

    fn get_validator_sites(&self) -> &Self::ValidatorSite {
        &self.registry.validator_sites
    }

    fn get_validator_manifests(&self) -> &Self::ManifestCache {
        &self.registry.validator_manifest_cache
    }

    fn get_publisher_manifests(&self) -> &Self::ManifestCache {
        &self.registry.publisher_manifest_cache
    }

    fn get_overlay(&self) -> &Self::Overlay {
        &self.overlay_status
    }

    fn get_cluster(&self) -> &Self::Cluster {
        self.registry.cluster.as_ref()
    }

    fn get_peer_reservations(&self) -> &Self::PeerReservationTable {
        self.registry.peer_reservations.as_ref()
    }

    fn get_resource_manager(&self) -> &Self::ResourceManager {
        &self.registry.resource_manager
    }

    fn get_node_store(&self) -> &Self::NodeStore {
        &self.registry.node_store
    }

    fn get_shamap_store(&self) -> &Self::ShamapStore {
        &self.shamap_store_service
    }

    fn get_relational_database(&self) -> &Self::RelationalDatabase {
        &self.registry.relational_database
    }

    fn get_inbound_ledgers(&self) -> &Self::InboundLedgers {
        &self.registry.inbound_ledgers
    }

    fn get_inbound_transactions(&self) -> &Self::InboundTransactions {
        &self.registry.inbound_transactions
    }

    fn get_accepted_ledger_cache(&self) -> &Self::AcceptedLedgerCache {
        &self.registry.accepted_ledger_cache
    }

    fn get_ledger_master(&self) -> &Self::LedgerMaster {
        &self.ledger_master_state
    }

    fn get_ledger_cleaner(&self) -> &Self::LedgerCleaner {
        &self.registry.ledger_cleaner
    }

    fn get_ledger_replayer(&self) -> &Self::LedgerReplayer {
        &self.registry.ledger_replayer
    }

    fn get_pending_saves(&self) -> &Self::PendingSaves {
        &self.registry.pending_saves
    }

    fn get_open_ledger(&self) -> &Self::OpenLedger {
        &self.registry.open_ledger
    }

    fn get_open_ledger_const(&self) -> &Self::OpenLedger {
        &self.registry.open_ledger
    }

    fn get_ops(&self) -> &Self::NetworkOps {
        &self.network_ops_state
    }

    fn get_order_book_db(&self) -> &Self::OrderBookDb {
        &self.registry.order_book_db
    }

    fn get_master_transaction(&self) -> &Self::TransactionMaster {
        &self.transaction_master
    }

    fn get_tx_q(&self) -> &Self::TxQ {
        &self.registry.tx_q
    }

    fn get_path_request_manager(&self) -> &Self::PathRequestManager {
        &self.registry.path_request_manager
    }

    fn get_server_handler(&self) -> &Self::ServerHandler {
        &self.registry.server_handler
    }

    fn get_perf_log(&self) -> &Self::PerfLog {
        self.registry
            .perf_log
            .as_ref()
            .expect("application root must own a perf log")
    }

    fn is_stopping(&self) -> bool {
        self.stop_tree.is_stopping()
    }

    fn get_journal(&self, name: &str) -> Self::Journal {
        self.registry.logs.journal(name)
    }

    fn get_io_context(&self) -> &Self::IoContext {
        &self.runtime_bindings
    }

    fn get_config(&self) -> &Self::Config {
        &self.registry.config
    }

    fn get_logs(&self) -> &Self::Logs {
        &self.registry.logs
    }

    fn get_trap_tx_id(&self) -> &Option<Self::TrapTxId> {
        &self.registry.trap_tx_id
    }

    fn get_wallet_db(&self) -> &Self::WalletDb {
        &self.registry.wallet_db
    }

    fn get_app(&self) -> &Self::Application {
        self
    }
}

#[cfg(test)]
mod tests;
