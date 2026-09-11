//! Global inbound ledger registry — matching rippled's InboundLedgersImp.
//!
//! ONE global registry: HashMap<Uint256, Entry>. A single Mutex protects
//! the map. Each entry holds an Arc<AcquisitionState> for the per-ledger
//! state machine.

use basics::base_uint::Uint256;
use basics::hardened_hash::HardenedHashBuilder;
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::MonotonicClock;
use ledger::{FetchPackCache, InboundLedgerPacket, Ledger};
use overlay::{Overlay, Peer};
use protocol::JsonValue;
use shamap::family::FullBelowCacheImpl;
use shamap::tree_node_cache::TreeNodeCache;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::SyncSender;
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

use acquisition::{
    AcquisitionEffect, BudgetState, CoordinatorRunner, DurableHandoffId, RunEpoch, RunnerSnapshot,
    SessionRef,
};

use crate::network::network_ops::AppNetworkOpsModeOwner;
use crate::runtime::overlay_runtime::AppOverlayRuntime;
use crate::shamap::shamap_store_backend::SHAMapStoreNodeStore;

use super::acquisition::{
    AcquisitionBuilder, AcquisitionCompletionRecorder, AcquisitionDurableCompletionRecorder,
    AcquisitionFailureRecorder, AcquisitionLedgerStore, AcquisitionPeerProvider,
    AcquisitionSequencePromoter, AcquisitionSnapshot, AcquisitionState,
    InboundPacketAdmissionLease, PacketAdmissionReservation, PacketEnqueue,
    ProvisionalLedgerIdentity,
};
use super::coordinator_adapter::{
    BrokerTicketState, CoordinatorIngress, LedgerDataIngressDisposition,
};
use super::coordinator_engine::{CoordinatorPlanSeed, CoordinatorSessionOrigins};
use super::coordinator_ports::{
    CoordinatorPortResources, ProductionAdapter, build_coordinator_adapter,
};
use super::read_broker::{NodeReadBroker, ReadBrokerConfig};
use super::scheduler::{AcquisitionKey, AcquisitionReadyScheduler, ReadyCause};
use super::worker_pool::WorkerPool;

// ─── Constants ───────────────────────────────────────────────────────────────

/// How long a failed hash stays in recent_failures (prevents retry storms).
const FAILURE_COOLDOWN: Duration = Duration::from_secs(5 * 60);

/// Entries idle longer than this are swept. rippled removes an inbound ledger
/// once its last action is more than one minute old; its separate failure cache
/// retains failed hashes for five minutes.
const SWEEP_IDLE_TIMEOUT: Duration = Duration::from_secs(60);

/// `fetch_info` must remain diagnostic-only and bounded even during a recovery
/// flood. Operators can use the aggregate fields to see work beyond this set.
const FETCH_INFO_MAX_ACQUISITIONS: usize = 16;

pub(crate) fn response_sequence_matches_request(expected_seq: u32, response_seq: u32) -> bool {
    expected_seq == 0 || response_seq == 0 || expected_seq == response_seq
}

/// The outcome of a coordinator-owned acquisition request: the minted session
/// identity, the registry acquisition id (for `CompletedInboundLedger` origin
/// correlation), and the effects the coordinator emitted so callers can trace
/// peer requests, timer arming, and phase transitions without reading
/// coordinator internals. The current caller logs the outcome and discards it;
/// fields feed the M6/M7 trace contract.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub(crate) struct CoordinatorAcquireOutcome {
    pub(crate) session: SessionRef,
    pub(crate) acquisition_id: u64,
    pub(crate) effects: Vec<AcquisitionEffect>,
}

/// rippled's `JtLedgerData` JobType permits at most three running jobs.
/// This bounds packet processing while leaving the inbound registry free to
/// track any number of hash-deduplicated acquisitions.
const WORKER_COUNT: usize = 3;

/// Acquire the registry `inner` mutex, recording the time spent blocked on the
/// lock. High percentiles of `quaxar_acq_registry_lock_wait_seconds` signal
/// ingress/lifecycle lock contention across the registry boundary.
fn timed_inner_lock(inner: &Arc<Mutex<RegistryInner>>) -> std::sync::MutexGuard<'_, RegistryInner> {
    let start = Instant::now();
    let guard = inner.lock().expect("inbound_ledgers lock");
    quaxar_metrics::acquisition::record_registry_lock_wait(start.elapsed().as_secs_f64());
    guard
}

/// Cumulative, process-lifetime counters covering every inbound-ledger
/// lifecycle boundary. They are sampled by NetworkOPs at most once every five
/// seconds, avoiding per-packet journal traffic during recovery pressure.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct AcquisitionLifecycleSnapshot {
    pub acquisition_starts: u64,
    pub acquisition_existing: u64,
    pub wire_ledger_data: u64,
    pub wire_relayed: u64,
    pub wire_invalid_hash: u64,
    pub wire_nodes: u64,
    pub route_attempts: u64,
    pub route_accepted: u64,
    pub route_misses: u64,
    pub route_terminal: u64,
    pub route_sequence_mismatch: u64,
    pub stale_packet_attempts: u64,
    pub stale_packets_stored: u64,
    pub initialization_jobs: u64,
    pub request_triggers: u64,
    pub request_messages: u64,
    pub requests_suppressed_local_probe: u64,
    pub local_probe_deferred_network_fallbacks: u64,
    pub header_sequences_promoted: u64,
    pub reply_headers_received: u64,
    pub peer_candidates_eligible: u64,
    pub tree_plans_completed: u64,
    pub peers_added: u64,
    pub data_jobs_submitted: u64,
    pub data_jobs_coalesced: u64,
    pub data_jobs_started: u64,
    pub packet_steps: u64,
    pub packet_step_errors: u64,
    pub packet_steps_completed: u64,
    pub timeout_jobs: u64,
    pub timeout_no_progress: u64,
    pub timeout_retries: u64,
    pub terminal_completed: u64,
    pub terminal_failed: u64,
}

#[derive(Default)]
pub(crate) struct AcquisitionLifecycleCounters {
    pub acquisition_starts: AtomicU64,
    pub acquisition_existing: AtomicU64,
    pub wire_ledger_data: AtomicU64,
    pub wire_relayed: AtomicU64,
    pub wire_invalid_hash: AtomicU64,
    pub wire_nodes: AtomicU64,
    pub route_attempts: AtomicU64,
    pub route_accepted: AtomicU64,
    pub route_misses: AtomicU64,
    pub route_terminal: AtomicU64,
    pub route_sequence_mismatch: AtomicU64,
    pub stale_packet_attempts: AtomicU64,
    pub stale_packets_stored: AtomicU64,
    pub initialization_jobs: AtomicU64,
    pub request_triggers: AtomicU64,
    pub request_messages: AtomicU64,
    pub requests_suppressed_local_probe: AtomicU64,
    pub local_probe_deferred_network_fallbacks: AtomicU64,
    pub header_sequences_promoted: AtomicU64,
    pub reply_headers_received: AtomicU64,
    pub peer_candidates_eligible: AtomicU64,
    pub tree_plans_completed: AtomicU64,
    pub peers_added: AtomicU64,
    pub data_jobs_submitted: AtomicU64,
    pub data_jobs_coalesced: AtomicU64,
    pub data_jobs_started: AtomicU64,
    pub packet_steps: AtomicU64,
    pub packet_step_errors: AtomicU64,
    pub packet_steps_completed: AtomicU64,
    pub timeout_jobs: AtomicU64,
    pub timeout_no_progress: AtomicU64,
    pub timeout_retries: AtomicU64,
    pub terminal_completed: AtomicU64,
    pub terminal_failed: AtomicU64,
}

impl AcquisitionLifecycleCounters {
    fn snapshot(&self) -> AcquisitionLifecycleSnapshot {
        macro_rules! load {
            ($field:ident) => {
                self.$field.load(Ordering::Relaxed)
            };
        }
        AcquisitionLifecycleSnapshot {
            acquisition_starts: load!(acquisition_starts),
            acquisition_existing: load!(acquisition_existing),
            wire_ledger_data: load!(wire_ledger_data),
            wire_relayed: load!(wire_relayed),
            wire_invalid_hash: load!(wire_invalid_hash),
            wire_nodes: load!(wire_nodes),
            route_attempts: load!(route_attempts),
            route_accepted: load!(route_accepted),
            route_misses: load!(route_misses),
            route_terminal: load!(route_terminal),
            route_sequence_mismatch: load!(route_sequence_mismatch),
            stale_packet_attempts: load!(stale_packet_attempts),
            stale_packets_stored: load!(stale_packets_stored),
            initialization_jobs: load!(initialization_jobs),
            request_triggers: load!(request_triggers),
            request_messages: load!(request_messages),
            requests_suppressed_local_probe: load!(requests_suppressed_local_probe),
            local_probe_deferred_network_fallbacks: load!(local_probe_deferred_network_fallbacks),
            header_sequences_promoted: load!(header_sequences_promoted),
            reply_headers_received: load!(reply_headers_received),
            peer_candidates_eligible: load!(peer_candidates_eligible),
            tree_plans_completed: load!(tree_plans_completed),
            peers_added: load!(peers_added),
            data_jobs_submitted: load!(data_jobs_submitted),
            data_jobs_coalesced: load!(data_jobs_coalesced),
            data_jobs_started: load!(data_jobs_started),
            packet_steps: load!(packet_steps),
            packet_step_errors: load!(packet_step_errors),
            packet_steps_completed: load!(packet_steps_completed),
            timeout_jobs: load!(timeout_jobs),
            timeout_no_progress: load!(timeout_no_progress),
            timeout_retries: load!(timeout_retries),
            terminal_completed: load!(terminal_completed),
            terminal_failed: load!(terminal_failed),
        }
    }
}

// ─── Reason enum ─────────────────────────────────────────────────────────────

/// Why a ledger is being acquired.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AcquireReason {
    /// Consensus / validation path.
    Consensus,
    /// LedgerMaster, catchup, publication.
    Generic,
    /// History fill, sequential catchup.
    History,
}

/// A completed acquisition retains its origin until LedgerMaster consumes it.
/// This distinguishes rippled's non-validating `storeLedger` paths from its
/// history-only `setFullLedger` path.
///
/// `from_coordinator` marks items published by the coordinator durable handoff
/// (M4.2-C3). The strand consumes those authoritatively because no registry
/// ready-queue entry exists for a coordinator session; legacy items are merely
/// wakeups for the registry's authoritative ready queue.
#[derive(Debug, Clone)]
pub struct CompletedInboundLedger {
    pub ledger: Arc<Ledger>,
    pub reason: AcquireReason,
    pub acquisition_id: u64,
    pub from_coordinator: bool,
    /// Present only for a coordinator durable handoff. Legacy registry wakeups
    /// retain `None` and follow their existing ready-queue acknowledgement.
    pub durable_handoff: Option<DurableHandoffId>,
    /// The complete coordinator session reference paired with
    /// `durable_handoff`. It prevents a target hash or `SessionId` alone from
    /// authorizing recipient acknowledgement.
    pub coordinator_session: Option<SessionRef>,
}

impl CompletedInboundLedger {
    /// Returns the exact durable coordinator identity only when this is a
    /// complete coordinator handoff. Incomplete coordinator-shaped records are
    /// intentionally not processed or acknowledged by the recipient.
    pub(crate) const fn coordinator_handoff(&self) -> Option<(DurableHandoffId, SessionRef)> {
        if !self.from_coordinator {
            return None;
        }
        match (self.durable_handoff, self.coordinator_session) {
            (Some(handoff), Some(session)) => Some((handoff, session)),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LedgerDataRouteDisposition {
    Accepted,
    Unmatched,
    Terminal,
    SequenceMismatch,
    /// Legacy direct routing observed actor pressure after decode. Worker 1
    /// must use `reserve_response_admission` and `route_admitted_response_with_seq`
    /// instead, so a matching decoded reply is transport-deferred before this
    /// disposition can occur.
    MailboxFull,
    AdmissionLeaseInvalid,
}

/// Actor-side pre-routing admission result. `Deferred` retains no decoded
/// packet in this registry; Worker 1 owns one peer-scoped decoder frame and
/// pauses/defer transport until it can retry reservation or reaches terminal.
pub enum LedgerDataAdmission {
    Admitted(InboundPacketAdmissionLease),
    Unmatched,
    Terminal,
    Deferred,
}

impl LedgerDataRouteDisposition {
    pub const fn may_stash_as_stale(self) -> bool {
        matches!(
            self,
            Self::Unmatched | Self::Terminal | Self::SequenceMismatch
        )
    }
}

struct Entry {
    id: u64,
    /// Non-authoritative requested/verified sequence snapshot maintained for
    /// registry bookkeeping. The state sequence gate invokes its exact
    /// `(hash, acquisition_id)` callback before a routed packet can pass the
    /// corresponding validation-and-enqueue boundary.
    seq: u32,
    #[allow(dead_code)]
    reason: AcquireReason,
    state: Arc<AcquisitionState>,
    last_touched: Instant,
    #[allow(dead_code)]
    started_at: Instant,
    completed_ledger: Option<Arc<Ledger>>,
    /// Exact identity of the resolver-visible provisional ledger. This stays
    /// with the registry entry until durable completion or failure revokes it.
    provisional_identity: Option<ProvisionalLedgerIdentity>,
    /// Completion has been durably consumed by the app layer. Keep the
    /// completed object in the registry until the normal sweep, matching
    /// rippled's InboundLedgers map, while suppressing duplicate handoffs.
    completion_acknowledged: bool,
    failed: bool,
}

// ─── RegistryInner ───────────────────────────────────────────────────────────

struct RegistryInner {
    entries: BTreeMap<Uint256, Entry>,
    recent_failures: HashMap<Uint256, Instant>,
    /// Successful terminal completions in exact completion order. Each item
    /// remains queued until acknowledged, and polling rotates unacknowledged
    /// items fairly so a failed persistence attempt cannot block later work.
    /// This is the direct equivalent of rippled's `InboundLedger::done()`
    /// dispatching `AcqDone`; it avoids discovering a ready acquisition by
    /// scanning an arbitrary bounded slice of the full registry.
    completed_ready: VecDeque<(Uint256, u64)>,
}

fn failure_matches_entry(acquisition_id: Option<u64>, entry_id: u64) -> bool {
    acquisition_id.is_none_or(|id| entry_id == id)
}

fn record_recent_failure_at(
    inner: &mut RegistryInner,
    hash: Uint256,
    _acquisition_id: Option<u64>,
    now: Instant,
) {
    // Match InboundLedgersImp::logFailure: AcqDone records a hash-wide
    // cooldown even if the failed object has already been swept. Admission
    // policy decides where that cooldown is consulted (History only).

    inner.recent_failures.entry(hash).or_insert(now);
    if let Some(entry) = inner.entries.get_mut(&hash)
        && failure_matches_entry(_acquisition_id, entry.id)
        && !entry.failed
    {
        // InboundLedger::done touches the acquisition before queued AcqDone
        // records the failure. Preserve that terminal sweep lifetime without
        // extending it on later poll passes.
        entry.failed = true;
        entry.last_touched = now;
    }
}

fn record_recent_failure(inner: &mut RegistryInner, hash: Uint256, acquisition_id: Option<u64>) {
    record_recent_failure_at(inner, hash, acquisition_id, Instant::now());
}

#[derive(Clone)]
struct RecoveryLclDecision {
    recorded_at: Instant,
    preferred_hash: Uint256,
    candidate_hash: Option<Uint256>,
    candidate_seq: Option<u32>,
    source: String,
    decision: String,
}

fn acquire_reason_name(reason: AcquireReason) -> &'static str {
    match reason {
        AcquireReason::Consensus => "consensus",
        AcquireReason::Generic => "generic",
        AcquireReason::History => "history",
    }
}

fn acquisition_snapshot_json(
    hash: Uint256,
    requested_seq: u32,
    reason: AcquireReason,
    idle_ms: u64,
    complete: bool,
    failed: bool,
    snapshot: AcquisitionSnapshot,
) -> JsonValue {
    let lookup_total = snapshot
        .node_store_fetch_hits
        .saturating_add(snapshot.node_store_fetch_misses);
    let lookup_hit_rate_ppm = (lookup_total != 0).then(|| {
        snapshot
            .node_store_fetch_hits
            .saturating_mul(1_000_000)
            .saturating_div(lookup_total)
    });
    let average_worker_queue_wait_us = (snapshot.worker_jobs != 0).then(|| {
        snapshot
            .worker_queue_wait_us
            .saturating_div(snapshot.worker_jobs)
    });
    let mut values = BTreeMap::from([
        ("hash".to_owned(), JsonValue::String(hash.to_string())),
        (
            "requested_seq".to_owned(),
            JsonValue::Unsigned(requested_seq as u64),
        ),
        ("seq".to_owned(), JsonValue::Unsigned(snapshot.seq as u64)),
        (
            "reason".to_owned(),
            JsonValue::String(acquire_reason_name(reason).to_owned()),
        ),
        ("age_ms".to_owned(), JsonValue::Unsigned(snapshot.age_ms)),
        ("idle_ms".to_owned(), JsonValue::Unsigned(idle_ms)),
        ("complete".to_owned(), JsonValue::Bool(complete)),
        ("failed".to_owned(), JsonValue::Bool(failed)),
        (
            "have_header".to_owned(),
            JsonValue::Bool(snapshot.have_header),
        ),
        (
            "have_state".to_owned(),
            JsonValue::Bool(snapshot.have_state),
        ),
        (
            "have_transactions".to_owned(),
            JsonValue::Bool(snapshot.have_transactions),
        ),
        (
            "timeouts".to_owned(),
            JsonValue::Unsigned(snapshot.timeouts as u64),
        ),
        ("packets".to_owned(), JsonValue::Unsigned(snapshot.packets)),
        (
            "useful_packets".to_owned(),
            JsonValue::Unsigned(snapshot.useful_packets),
        ),
        (
            "useful_nodes".to_owned(),
            JsonValue::Unsigned(snapshot.useful_nodes),
        ),
        (
            "state_packets".to_owned(),
            JsonValue::Unsigned(snapshot.state_packets),
        ),
        (
            "state_useful_nodes".to_owned(),
            JsonValue::Unsigned(snapshot.state_useful_nodes),
        ),
        (
            "state_duplicate_nodes".to_owned(),
            JsonValue::Unsigned(snapshot.state_duplicate_nodes),
        ),
        (
            "malformed_packets".to_owned(),
            JsonValue::Unsigned(snapshot.malformed_packets),
        ),
        (
            "state_scan_runs".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_runs),
        ),
        (
            "state_missing_nodes".to_owned(),
            JsonValue::Unsigned(snapshot.state_missing_nodes),
        ),
        (
            "tx_missing_nodes".to_owned(),
            JsonValue::Unsigned(snapshot.tx_missing_nodes),
        ),
        (
            "state_scan_us".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_us),
        ),
        (
            "state_scan_branch_steps".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_branch_steps),
        ),
        (
            "state_scan_branches_seen".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_branches_seen),
        ),
        (
            "state_scan_missing_nodes_recorded".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_missing_nodes_recorded),
        ),
        (
            "state_scan_positive_progress_slices".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_positive_progress_slices),
        ),
        (
            "state_scan_branch_budget_yields".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_branch_budget_yields),
        ),
        (
            "state_scan_deferred_read_budget_yields".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_deferred_read_budget_yields),
        ),
        (
            "state_scan_deferred_read_resume_yields".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_deferred_read_resume_yields),
        ),
        (
            "state_scan_missing_node_limit_yields".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_missing_node_limit_yields),
        ),
        (
            "state_scan_completed_slices".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_completed_slices),
        ),
        (
            "state_scan_last_yield".to_owned(),
            JsonValue::String(snapshot.state_scan_last_yield.to_owned()),
        ),
        (
            "state_scan_last_branch_steps".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_last_branch_steps),
        ),
        (
            "state_scan_last_deferred_reads".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_last_deferred_reads),
        ),
        (
            "state_scan_last_deferred_resumes".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_last_deferred_resumes),
        ),
        (
            "state_scan_last_missing_nodes".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_last_missing_nodes),
        ),
        (
            "state_scan_duplicate_missing_hashes".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_duplicate_missing_hashes),
        ),
        (
            "state_scan_full_below_hits".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_full_below_hits),
        ),
        (
            "state_scan_loaded_or_cached_children".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_loaded_or_cached_children),
        ),
        (
            "state_scan_pending_reads".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_pending_reads),
        ),
        (
            "state_scan_read_slot_full".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_read_slot_full),
        ),
        (
            "state_scan_read_admission_accepted".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_read_admission_accepted),
        ),
        (
            "state_scan_read_admission_deferred".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_read_admission_deferred),
        ),
        (
            "state_scan_read_admission_attached".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_read_admission_attached),
        ),
        (
            "state_scan_read_broker_rejected".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_read_broker_rejected),
        ),
        (
            "state_scan_max_pending_reads".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_max_pending_reads),
        ),
        (
            "state_scan_pending_hits".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_pending_hits),
        ),
        (
            "state_scan_pending_misses".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_pending_misses),
        ),
        (
            "state_scan_deferred_resumes".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_deferred_resumes),
        ),
        (
            "state_scan_yields".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_yields),
        ),
        (
            "state_scan_continuations".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_continuations),
        ),
        (
            "timeout_dispatches".to_owned(),
            JsonValue::Unsigned(snapshot.timeout_dispatches),
        ),
        (
            "state_scan_max_buffered_packets".to_owned(),
            JsonValue::Unsigned(snapshot.state_scan_max_buffered_packets),
        ),
        (
            "data_drain_runs".to_owned(),
            JsonValue::Unsigned(snapshot.data_drain_runs),
        ),
        (
            "data_drain_us".to_owned(),
            JsonValue::Unsigned(snapshot.data_drain_us),
        ),
        (
            "data_drain_max_us".to_owned(),
            JsonValue::Unsigned(snapshot.data_drain_max_us),
        ),
        (
            "data_drain_max_packets".to_owned(),
            JsonValue::Unsigned(snapshot.data_drain_max_packets),
        ),
        (
            "tx_scan_us".to_owned(),
            JsonValue::Unsigned(snapshot.tx_scan_us),
        ),
        (
            "worker_jobs".to_owned(),
            JsonValue::Unsigned(snapshot.worker_jobs),
        ),
        (
            "worker_queue_wait_us".to_owned(),
            JsonValue::Unsigned(snapshot.worker_queue_wait_us),
        ),
        (
            "node_store_lookup_hits".to_owned(),
            JsonValue::Unsigned(snapshot.node_store_fetch_hits),
        ),
        (
            "node_store_lookup_misses".to_owned(),
            JsonValue::Unsigned(snapshot.node_store_fetch_misses),
        ),
        (
            "tracked_peers".to_owned(),
            JsonValue::Unsigned(snapshot.tracked_peers as u64),
        ),
        (
            "buffered_packets".to_owned(),
            JsonValue::Unsigned(snapshot.buffered_packets as u64),
        ),
        (
            "buffered_packets_high_water".to_owned(),
            JsonValue::Unsigned(snapshot.buffered_packets_high_water as u64),
        ),
        (
            "mailbox_token".to_owned(),
            JsonValue::String(snapshot.mailbox_token.to_owned()),
        ),
        (
            "scan_continuation_pending".to_owned(),
            JsonValue::Bool(snapshot.scan_continuation_pending),
        ),
        (
            "pending_admitted_timeouts".to_owned(),
            JsonValue::Unsigned(snapshot.pending_admitted_timeouts as u64),
        ),
    ]);
    values.insert(
        "header_after_ms".to_owned(),
        snapshot
            .header_after_ms
            .map(JsonValue::Unsigned)
            .unwrap_or(JsonValue::Null),
    );
    values.insert(
        "node_store_lookup_hit_rate_ppm".to_owned(),
        lookup_hit_rate_ppm
            .map(JsonValue::Unsigned)
            .unwrap_or(JsonValue::Null),
    );
    values.insert(
        "average_worker_queue_wait_us".to_owned(),
        average_worker_queue_wait_us
            .map(JsonValue::Unsigned)
            .unwrap_or(JsonValue::Null),
    );
    JsonValue::Object(values)
}

fn recovery_lcl_decision_json(decision: Option<RecoveryLclDecision>) -> JsonValue {
    let Some(decision) = decision else {
        return JsonValue::Null;
    };
    let mut value = BTreeMap::from([
        (
            "age_ms".to_owned(),
            JsonValue::Unsigned(decision.recorded_at.elapsed().as_millis() as u64),
        ),
        (
            "preferred_hash".to_owned(),
            JsonValue::String(decision.preferred_hash.to_string()),
        ),
        ("source".to_owned(), JsonValue::String(decision.source)),
        ("decision".to_owned(), JsonValue::String(decision.decision)),
    ]);
    value.insert(
        "candidate_hash".to_owned(),
        decision
            .candidate_hash
            .map(|hash| JsonValue::String(hash.to_string()))
            .unwrap_or(JsonValue::Null),
    );
    value.insert(
        "candidate_seq".to_owned(),
        decision
            .candidate_seq
            .map(|seq| JsonValue::Unsigned(seq as u64))
            .unwrap_or(JsonValue::Null),
    );
    JsonValue::Object(value)
}

/// Thread-safe global service for inbound ledger acquisition.
///
/// Matches rippled's InboundLedgers: one entry per hash, touch-on-access,
/// sweep idle entries, route peer responses, fixed worker pool.
struct FetchPackWakeState {
    next_generation: u64,
    pending_hashes: BTreeSet<Uint256>,
}

type AcquisitionLedgerRevoker = Arc<dyn Fn(ProvisionalLedgerIdentity) + Send + Sync + 'static>;
type AcquisitionAdvanceNotifier = Arc<dyn Fn() + Send + Sync + 'static>;

pub struct InboundLedgers {
    inner: Arc<Mutex<RegistryInner>>,
    worker_pool: Arc<WorkerPool>,
    scheduler: Arc<AcquisitionReadyScheduler>,
    read_broker: NodeReadBroker,
    // Shared resources for creating acquisitions
    node_store: Arc<RwLock<Option<SHAMapStoreNodeStore>>>,
    tree_cache: Arc<TreeNodeCache<MonotonicClock>>,
    full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
    fetch_pack: Arc<FetchPackCache>,
    fetch_pack_wakes: Mutex<FetchPackWakeState>,
    overlay_rt: Arc<RwLock<Option<Arc<AppOverlayRuntime>>>>,
    completed_ledgers_tx: SyncSender<CompletedInboundLedger>,
    completed_ledger_store: Arc<RwLock<Option<AcquisitionLedgerStore>>>,
    completed_ledger_revoker: Arc<RwLock<Option<AcquisitionLedgerRevoker>>>,
    /// App-owned publication planner wakeup. It records no ledger policy in
    /// this registry; terminal lifecycle transitions only request one
    /// serialized owner pass.
    publication_advance_notifier: Arc<RwLock<Option<AcquisitionAdvanceNotifier>>>,
    stopping: AtomicBool,
    need_network_ledger: Arc<AtomicBool>,
    pending_acquires: Arc<Mutex<HashSet<Uint256>>>,
    next_acquisition_id: AtomicU64,
    /// Last preferred-LCL selection outcome, retained solely for bounded
    /// operator diagnostics.
    recovery_lcl_decision: Mutex<Option<RecoveryLclDecision>>,
    /// Shared lifecycle counters incremented at request, wire, worker, retry,
    /// and terminal boundaries. The sampled snapshot never mutates state.
    lifecycle: Arc<AcquisitionLifecycleCounters>,
    /// Coordinator-owned session lifecycle. Installed once the NodeStore and
    /// the NetworkOps phase state are configured; when installed it is the
    /// single session lifecycle owner for every target it creates. `None`
    /// preserves the legacy `AcquisitionState` path behind the M4.2-C3
    /// switchover, so the rollback feature flag is "never install". A mutex
    /// (not `RwLock`) is required because the adapter's event receiver is not
    /// `Sync`; ingress/owner calls serialize through this short lock.
    /// Mutable owner for coordinator lifecycle transitions and effect dispatch.
    /// Overlay ingress intentionally does not use this lock; it holds the
    /// separately published immutable [`CoordinatorIngress`] capability.
    coordinator: Mutex<Option<ProductionAdapter>>,
    /// Immutable route/admission capability for overlay `TmLedgerData` ingress.
    /// It is published before any request effect can synchronously yield a
    /// reply, so ingress never re-enters the mutable coordinator lock.
    coordinator_ingress: RwLock<Option<CoordinatorIngress>>,
    /// Per-session `(sequence, reason)` origins the coordinator plan seed
    /// resolves when a Base/header packet arrives. Registered exactly once per
    /// requested session.
    coordinator_origins: CoordinatorSessionOrigins,
    /// Node-size-derived cap installed into the production coordinator.
    coordinator_budget: BudgetState,
    /// Newest NodeStore generation published by the online-delete worker.
    /// Only the serialized coordinator owner consumes and applies this fact.
    pending_store_generation: AtomicU64,
    /// The NetworkOps state the coordinator phase port publishes to. Wired by
    /// ApplicationRoot before coordinator installation; the coordinator is the
    /// single production mode writer for the sessions it owns.
    coordinator_phase: RwLock<Option<AppNetworkOpsModeOwner>>,
}

impl InboundLedgers {
    /// Create a new InboundLedgers service.
    pub fn new(
        tree_cache: Arc<TreeNodeCache<MonotonicClock>>,
        full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
        fetch_pack: Arc<FetchPackCache>,
        completed_ledgers_tx: SyncSender<CompletedInboundLedger>,
        need_network_ledger: Arc<AtomicBool>,
    ) -> Self {
        Self::new_with_budget(
            tree_cache,
            full_below,
            fetch_pack,
            completed_ledgers_tx,
            need_network_ledger,
            BudgetState::default(),
        )
    }

    /// Construct the production registry with an explicit node-size-derived
    /// coordinator budget. Existing callers retain the medium default above.
    pub fn new_with_budget(
        tree_cache: Arc<TreeNodeCache<MonotonicClock>>,
        full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
        fetch_pack: Arc<FetchPackCache>,
        completed_ledgers_tx: SyncSender<CompletedInboundLedger>,
        need_network_ledger: Arc<AtomicBool>,
        coordinator_budget: BudgetState,
    ) -> Self {
        Self::with_worker_pool_and_budget(
            tree_cache,
            full_below,
            fetch_pack,
            completed_ledgers_tx,
            need_network_ledger,
            Arc::new(WorkerPool::new(WORKER_COUNT)),
            coordinator_budget,
        )
    }

    /// Construct the registry around its worker queue. Production always uses
    /// the fixed-size pool above; tests provide a zero-worker pool so they can
    /// prove real ingress scheduling and draining without timing races.
    #[cfg(test)]
    fn with_worker_pool(
        tree_cache: Arc<TreeNodeCache<MonotonicClock>>,
        full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
        fetch_pack: Arc<FetchPackCache>,
        completed_ledgers_tx: SyncSender<CompletedInboundLedger>,
        need_network_ledger: Arc<AtomicBool>,
        worker_pool: Arc<WorkerPool>,
    ) -> Self {
        Self::with_worker_pool_and_budget(
            tree_cache,
            full_below,
            fetch_pack,
            completed_ledgers_tx,
            need_network_ledger,
            worker_pool,
            BudgetState::default(),
        )
    }

    fn with_worker_pool_and_budget(
        tree_cache: Arc<TreeNodeCache<MonotonicClock>>,
        full_below: Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>>,
        fetch_pack: Arc<FetchPackCache>,
        completed_ledgers_tx: SyncSender<CompletedInboundLedger>,
        need_network_ledger: Arc<AtomicBool>,
        worker_pool: Arc<WorkerPool>,
        coordinator_budget: BudgetState,
    ) -> Self {
        let scheduler = AcquisitionReadyScheduler::new(Arc::clone(&worker_pool));
        Self {
            inner: Arc::new(Mutex::new(RegistryInner {
                entries: BTreeMap::new(),
                recent_failures: HashMap::new(),
                completed_ready: VecDeque::new(),
            })),
            worker_pool,
            scheduler,
            read_broker: NodeReadBroker::new(ReadBrokerConfig::default())
                .expect("default inbound read broker bounds are valid"),
            node_store: Arc::new(RwLock::new(None)),
            tree_cache,
            full_below,
            fetch_pack,
            fetch_pack_wakes: Mutex::new(FetchPackWakeState {
                next_generation: 0,
                pending_hashes: BTreeSet::new(),
            }),
            overlay_rt: Arc::new(RwLock::new(None)),
            completed_ledgers_tx,
            completed_ledger_store: Arc::new(RwLock::new(None)),
            completed_ledger_revoker: Arc::new(RwLock::new(None)),
            publication_advance_notifier: Arc::new(RwLock::new(None)),
            stopping: AtomicBool::new(false),
            need_network_ledger,
            pending_acquires: Arc::new(Mutex::new(HashSet::new())),
            next_acquisition_id: AtomicU64::new(1),
            recovery_lcl_decision: Mutex::new(None),
            lifecycle: Arc::new(AcquisitionLifecycleCounters::default()),
            coordinator: Mutex::new(None),
            coordinator_ingress: RwLock::new(None),
            coordinator_origins: CoordinatorSessionOrigins::default(),
            coordinator_budget,
            pending_store_generation: AtomicU64::new(0),
            coordinator_phase: RwLock::new(None),
        }
    }

    // ─── Configuration setters (called during app startup) ───────────────

    /// Returns the shared full-below cache Arc for metrics attachment.
    pub fn full_below_cache(
        &self,
    ) -> &Arc<FullBelowCacheImpl<MonotonicClock, HardenedHashBuilder>> {
        &self.full_below
    }

    pub fn set_overlay_rt(&self, rt: Arc<AppOverlayRuntime>) {
        let mut guard = self.overlay_rt.write().expect("overlay_rt write");
        *guard = Some(rt);
    }

    pub fn set_node_store(&self, ns: SHAMapStoreNodeStore) {
        let mut guard = self.node_store.write().expect("node_store write");
        *guard = Some(ns);
    }

    // ─── Coordinator-owned session lifecycle (M4.2-C2/C3) ───────────────

    /// Wire the NetworkOps phase state the coordinator publishes to. The
    /// coordinator is the single production mode writer for the sessions it
    /// owns; it never reads a mode back from this state.
    pub(crate) fn set_phase_mode_owner(&self, owner: AppNetworkOpsModeOwner) {
        *self
            .coordinator_phase
            .write()
            .expect("coordinator phase write") = Some(owner);
    }

    #[cfg(test)]
    fn set_phase_state(&self, state: Arc<crate::network::network_ops::SharedNetworkOpsState>) {
        let age_state = Arc::clone(&state);
        self.set_phase_mode_owner(AppNetworkOpsModeOwner::new(
            state,
            Arc::new(move || {
                if age_state.operating_mode()
                    == crate::network::network_ops::NetworkOpsOperatingMode::Tracking
                {
                    Duration::ZERO
                } else {
                    Duration::from_secs(60)
                }
            }),
        ));
    }

    /// Whether the coordinator owns session lifecycle. When false, `acquire`
    /// uses the legacy `AcquisitionState` path (M4.2-C3 rollback flag).
    pub fn coordinator_installed(&self) -> bool {
        self.coordinator.lock().expect("coordinator lock").is_some()
    }

    /// The active overlay peers the coordinator request port may deliver to.
    /// The overlay owns sockets; this only mirrors its availability fact.
    fn coordinator_peer_snapshot(&self) -> Vec<Arc<dyn Peer>> {
        let guard = self.overlay_rt.read().expect("overlay_rt read");
        match guard.as_ref() {
            Some(rt) => rt.overlay().active_peers(),
            None => Vec::new(),
        }
    }

    /// Build and install the production coordinator adapter. Idempotent: the
    /// first successful install wins and later calls return `false` without
    /// replacing the live owner. Installation is rejected while a legacy actor
    /// is live: those actors retain independent mailbox, scheduler, timer, and
    /// tree-plan ownership and cannot coexist with coordinator sessions.
    /// Bootstrap installs before any acquisition can begin; keeping the
    /// coordinator absent is the explicit compatibility fallback. Requires
    /// the NodeStore, the phase state, and (optionally) the overlay runtime to
    /// be configured first.
    pub fn install_coordinator(&self) -> bool {
        if self.coordinator_installed() {
            return true;
        }
        let legacy_lifecycle_live = {
            let inner = timed_inner_lock(&self.inner);
            inner.entries.values().any(|entry| {
                let completed = entry.completed_ledger.is_some()
                    || entry.state.completed.load(Ordering::Acquire);
                let active_actor = !entry.state.stopped.load(Ordering::Acquire) && !completed;
                // A completed legacy actor retains ownership until its exact
                // ready-queue handoff is acknowledged. Installing the
                // coordinator before that acknowledgement would leave the
                // NetworkOps registry poll as a second terminal owner.
                let terminal_handoff_pending = completed && !entry.completion_acknowledged;
                !entry.failed
                    && !entry.state.failed.load(Ordering::Acquire)
                    && (active_actor || terminal_handoff_pending)
            })
        };
        if legacy_lifecycle_live {
            tracing::warn!(
                target: "inbound_ledger",
                "coordinator installation rejected while a legacy acquisition lifecycle is live"
            );
            return false;
        }
        let node_store = match self.node_store.read().expect("node_store read").clone() {
            Some(node_store) => node_store,
            None => return false,
        };
        let phase_mode_owner = match self
            .coordinator_phase
            .read()
            .expect("coordinator phase read")
            .clone()
        {
            Some(state) => state,
            None => return false,
        };
        let origins = self.coordinator_origins.clone();
        let seed = CoordinatorPlanSeed::new(
            origins,
            Arc::clone(&self.fetch_pack),
            Arc::clone(&self.tree_cache),
            Arc::clone(&self.full_below),
        );
        let runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            self.coordinator_budget,
            Box::new(seed),
        );
        let adapter = build_coordinator_adapter(CoordinatorPortResources {
            runner,
            peers: overlay::SimplePeerSet::new(self.coordinator_peer_snapshot()),
            broker: self.read_broker.clone(),
            tickets: BrokerTicketState::default(),
            fetch_pack: Arc::clone(&self.fetch_pack),
            node_store,
            completed_ledgers_tx: self.completed_ledgers_tx.clone(),
            timer_pool: Arc::clone(&self.worker_pool),
            phase_mode_owner,
        });
        let ingress = adapter.ingress();
        let mut guard = self.coordinator.lock().expect("coordinator lock");
        if guard.is_none() {
            // Publish before the adapter can dispatch any future peer request.
            // A local/loopback overlay may reply inline from that dispatch.
            *self
                .coordinator_ingress
                .write()
                .expect("coordinator ingress write") = Some(ingress);
            *guard = Some(adapter);
            true
        } else {
            false
        }
    }

    /// Record coordinator-owned terminal failures after releasing the
    /// coordinator lock. This restores rippled `InboundLedgers::logFailure`
    /// ownership without letting the registry inspect or mutate a live
    /// coordinator session.
    fn record_coordinator_failures(&self, hashes: Vec<Uint256>) {
        if hashes.is_empty() {
            return;
        }
        {
            let mut inner = timed_inner_lock(&self.inner);
            for hash in hashes {
                record_recent_failure(&mut inner, hash, None);
            }
        }
        self.notify_publication_advance();
    }

    /// Drain the coordinator owner loop: process every queued event and
    /// dispatch its effects. Returns the number of events handled.
    pub fn coordinator_drain(&self) -> usize {
        self.coordinator_drain_with_status().0
    }

    /// Drain one bounded coordinator burst and report whether the owner hit a
    /// work boundary. The NetworkOps strand uses the second value solely to
    /// suppress its idle wait; all lifecycle mutation remains in `drain`.
    pub fn coordinator_drain_with_status(&self) -> (usize, bool) {
        let (handled, failures) = {
            let mut guard = self.coordinator.lock().expect("coordinator lock");
            let Some(coordinator) = guard.as_mut() else {
                return (0, false);
            };
            // Apply rotation before queued completions or acquires can observe
            // a generation which the rotating backend has already retired.
            let generation = self.pending_store_generation.swap(0, Ordering::AcqRel);
            let mut handled = 0;
            if generation != 0 {
                coordinator.handle_fact(acquisition::AcquisitionEvent::StoreRotated(
                    acquisition::StoreGeneration::new(generation),
                ));
                handled += 1;
            }
            handled += coordinator.drain();
            let has_more = coordinator.drain_has_more();
            let failures = coordinator.take_terminal_failures();
            ((handled, has_more), failures)
        };
        self.record_coordinator_failures(failures);
        handled
    }

    /// Publish a completed NodeStore rotation without mutating acquisition
    /// state from the online-delete worker. Bursts coalesce to the newest
    /// generation and remain retained until the owner drains them.
    pub(crate) fn note_store_rotated(&self, generation: u64) {
        if generation != 0 {
            self.pending_store_generation
                .fetch_max(generation, Ordering::Release);
        }
    }

    /// Feed the current peer-availability fact to the coordinator owner.
    /// Empty peers mean no usable peer capability. The coordinator publishes
    /// `Disconnected`/`Connected` and cancels sessions on peer loss. Returns
    /// false when the coordinator is not installed (the legacy strand writer
    /// remains authoritative).
    pub fn coordinator_report_peer_availability(&self, peers: &[overlay::PeerId]) -> bool {
        let failures = {
            let mut guard = self.coordinator.lock().expect("coordinator lock");
            let Some(coordinator) = guard.as_mut() else {
                return false;
            };
            coordinator.refresh_peers(self.coordinator_peer_snapshot());
            coordinator.connectivity(peers);
            coordinator.drain();
            coordinator.take_terminal_failures()
        };
        self.record_coordinator_failures(failures);
        true
    }

    /// Feed acquisition transport membership without changing the coordinator
    /// operating phase (rippled start-valid zero-threshold behavior).
    pub fn coordinator_report_transport_availability(&self, peers: &[overlay::PeerId]) -> bool {
        let failures = {
            let mut guard = self.coordinator.lock().expect("coordinator lock");
            let Some(coordinator) = guard.as_mut() else {
                return false;
            };
            coordinator.refresh_peers(self.coordinator_peer_snapshot());
            coordinator.transport_connectivity(peers);
            coordinator.drain();
            coordinator.take_terminal_failures()
        };
        self.record_coordinator_failures(failures);
        true
    }

    /// Report the configured consensus-peer threshold independently of ledger
    /// acquisition transport availability.
    pub fn coordinator_report_consensus_quorum(&self, available: bool) -> bool {
        let failures = {
            let mut guard = self.coordinator.lock().expect("coordinator lock");
            let Some(coordinator) = guard.as_mut() else {
                return false;
            };
            if available {
                coordinator.consensus_quorum_available();
            } else {
                coordinator.consensus_quorum_lost();
            }
            coordinator.drain();
            coordinator.take_terminal_failures()
        };
        self.record_coordinator_failures(failures);
        true
    }

    /// Feed the bootstrap startup-mode fact so the coordinator seeds and
    /// publishes the initial phase from the moment it installs (M6-D). The
    /// coordinator owns the mode write from here on; the legacy bootstrap
    /// startup write remains only as the pre-install seed. Returns false unless
    /// installed.
    pub fn coordinator_startup(&self, phase: acquisition::SyncPhase) -> bool {
        let mut guard = self.coordinator.lock().expect("coordinator lock");
        let Some(coordinator) = guard.as_mut() else {
            return false;
        };
        coordinator.handle_fact(acquisition::AcquisitionEvent::StartupMode { phase });
        true
    }

    /// Feed a coordinator heartbeat so the phase port re-applies
    /// validated-ledger-age normalization on `Connected`/`Syncing` (rippled
    /// `processHeartbeatTimer` parity). Returns false unless installed.
    pub fn coordinator_heartbeat(&self) -> bool {
        let mut guard = self.coordinator.lock().expect("coordinator lock");
        let Some(coordinator) = guard.as_mut() else {
            return false;
        };
        coordinator.handle_fact(acquisition::AcquisitionEvent::Heartbeat);
        true
    }

    /// Feed an LCL-install fact so the coordinator can transition
    /// `Syncing -> Tracking` when the acquired target is installed as the last
    /// closed ledger. Returns false unless installed.
    pub fn coordinator_lcl_installed(&self, identity: acquisition::LedgerIdentity) -> bool {
        let mut guard = self.coordinator.lock().expect("coordinator lock");
        let Some(coordinator) = guard.as_mut() else {
            return false;
        };
        coordinator.handle_fact(acquisition::AcquisitionEvent::LclInstalled(identity));
        true
    }

    /// Feed NetworkOps' authoritative preferred-LCL selection. Register the
    /// app plan/handoff origin before the fact can mint a session and dispatch
    /// its first request. Ordinary `acquire(..., Consensus)` then coalesces as
    /// demand-only work and cannot replace this exact active permit.
    pub fn coordinator_consensus_target(&self, target: acquisition::LedgerTarget) -> bool {
        if target.hash().is_zero() || self.stopping.load(Ordering::Acquire) {
            return false;
        }
        let failures = {
            let mut guard = self.coordinator.lock().expect("coordinator lock");
            let Some(coordinator) = guard.as_mut() else {
                return false;
            };
            let acquisition_id = self.next_acquisition_id.fetch_add(1, Ordering::Relaxed);
            self.coordinator_origins.register(
                target.hash(),
                target.sequence().unwrap_or_default(),
                ledger::InboundLedgerReason::Consensus,
            );
            coordinator.refresh_peers(self.coordinator_peer_snapshot());
            let peers = self
                .coordinator_peer_snapshot()
                .iter()
                .map(|peer| peer.id())
                .collect::<Vec<_>>();
            let peerless = peers.is_empty();
            coordinator.connectivity(&peers);
            coordinator.register_pending_handoff_origin(
                target.hash(),
                AcquireReason::Consensus,
                acquisition_id,
                true,
            );
            let effects = coordinator.consensus_target(target);
            let started = effects.iter().any(|effect| {
                matches!(effect, AcquisitionEffect::SessionStarted(session) if session.target_hash() == target.hash())
            });
            if !peerless && !started && !coordinator.has_deferred_consensus_target(target) {
                coordinator.clear_pending_handoff_origin(
                    target.hash(),
                    AcquireReason::Consensus,
                    acquisition_id,
                    true,
                );
            }
            coordinator.drain();
            coordinator.take_terminal_failures()
        };
        self.record_coordinator_failures(failures);
        true
    }

    /// Feed the accepted-boundary validation-recovery candidate. The first
    /// exact target remains the phase-neutral acquisition owner until its
    /// terminal boundary; `None` withdraws only a candidate waiting behind it.
    pub fn coordinator_validation_recovery_target(&self, target: Option<(Uint256, u32)>) -> bool {
        if self.stopping.load(Ordering::Acquire) {
            return false;
        }
        let failures = {
            let mut guard = self.coordinator.lock().expect("coordinator lock");
            let Some(coordinator) = guard.as_mut() else {
                return false;
            };
            coordinator.refresh_peers(self.coordinator_peer_snapshot());
            let peers = self
                .coordinator_peer_snapshot()
                .iter()
                .map(|peer| peer.id())
                .collect::<Vec<_>>();
            coordinator.transport_connectivity(&peers);

            let target = target.and_then(|(hash, seq)| {
                (!hash.is_zero()).then_some(acquisition::LedgerTarget::new(
                    hash,
                    (seq != 0).then_some(seq),
                ))
            });
            if target.is_none() {
                coordinator.clear_pending_validation_recovery_candidates();
            }
            let prior_candidate = coordinator.current_validation_recovery_candidate();
            let origin = target.map(|target| {
                let anchor = coordinator
                    .current_validation_recovery_target()
                    .is_none_or(|current| current.hash() == target.hash());
                let acquisition_id = self.next_acquisition_id.fetch_add(1, Ordering::Relaxed);
                let seq = target.sequence().unwrap_or_default();
                self.coordinator_origins.register(
                    target.hash(),
                    seq,
                    ledger::InboundLedgerReason::Consensus,
                );
                coordinator.register_pending_validation_recovery_origin(
                    target.hash(),
                    AcquireReason::Consensus,
                    acquisition_id,
                    anchor,
                );
                (target, acquisition_id, anchor)
            });
            let effects = coordinator.validation_recovery_target(target);
            if let Some(prior) = prior_candidate {
                let retained_as_anchor = coordinator
                    .current_validation_recovery_target()
                    .is_some_and(|current| current.hash() == prior.hash());
                let retained_as_candidate = coordinator
                    .current_validation_recovery_candidate()
                    .is_some_and(|current| current.hash() == prior.hash());
                if !retained_as_anchor
                    && !retained_as_candidate
                    && !coordinator.retains_session_origin_for_hash(prior.hash())
                {
                    self.coordinator_origins.remove(prior.hash());
                }
            }
            if let Some((target, acquisition_id, anchor)) = origin {
                let started = effects.iter().any(|effect| {
                    matches!(effect, AcquisitionEffect::SessionStarted(session) if session.target_hash() == target.hash())
                });
                let retained = if anchor {
                    coordinator.has_unbound_validation_recovery_target(target)
                } else {
                    coordinator.has_validation_recovery_candidate(target)
                };
                if !started && !retained {
                    coordinator.clear_pending_validation_recovery_origin(
                        target.hash(),
                        AcquireReason::Consensus,
                        acquisition_id,
                        anchor,
                    );
                }
                if !started && !coordinator.retains_session_origin_for_hash(target.hash()) {
                    self.coordinator_origins.remove(target.hash());
                }
            }
            coordinator.drain();
            coordinator.take_terminal_failures()
        };
        self.record_coordinator_failures(failures);
        true
    }

    /// Feed rippled's mode-only `consensusViewChange` fact. Demotes
    /// `Tracking/Full -> Connected` without selecting or pinning an acquisition
    /// target. Returns false unless the coordinator is installed.
    pub fn coordinator_consensus_view_change(&self) -> bool {
        let failures = {
            let mut guard = self.coordinator.lock().expect("coordinator lock");
            let Some(coordinator) = guard.as_mut() else {
                return false;
            };
            coordinator.consensus_view_change();
            coordinator.drain();
            coordinator.take_terminal_failures()
        };
        self.record_coordinator_failures(failures);
        true
    }

    /// Feed a target-bearing preferred-LCL divergence fact from the serialized
    /// `checkLastClosedLedger` path. Demotes `Connected/Tracking/Full -> Syncing { target }` without
    /// minting a session. Returns false unless installed, so the legacy strand
    /// writer remains authoritative when the coordinator is absent.
    pub fn coordinator_preferred_lcl_divergence(&self, target: acquisition::LedgerTarget) -> bool {
        let failures = {
            let mut guard = self.coordinator.lock().expect("coordinator lock");
            let Some(coordinator) = guard.as_mut() else {
                return false;
            };
            coordinator.preferred_lcl_divergence(target);
            coordinator.drain();
            coordinator.take_terminal_failures()
        };
        self.record_coordinator_failures(failures);
        true
    }

    /// Report that an accepted-boundary preferred-LCL check selected the
    /// current local LCL. This retires obsolete Syncing policy without
    /// loosening the exact target-install gate.
    pub fn coordinator_preferred_lcl_reconciled(&self, lcl: acquisition::LedgerIdentity) -> bool {
        let mut guard = self.coordinator.lock().expect("coordinator lock");
        let Some(coordinator) = guard.as_mut() else {
            return false;
        };
        coordinator.handle_fact(acquisition::AcquisitionEvent::PreferredLclReconciled { lcl });
        true
    }

    /// Feed a no-consensus-positions fact (Quaxar-specific). Demotes
    /// `Full -> Connected` when consensus accepted a round with no usable peer
    /// positions. Returns false unless installed.
    pub fn coordinator_blocked_with_no_target(&self) -> bool {
        let failures = {
            let mut guard = self.coordinator.lock().expect("coordinator lock");
            let Some(coordinator) = guard.as_mut() else {
                return false;
            };
            coordinator.blocked_with_no_target();
            coordinator.drain();
            coordinator.take_terminal_failures()
        };
        self.record_coordinator_failures(failures);
        true
    }

    /// Feed a publication-committed fact. `fresh` is the adapter's
    /// validated-chain freshness observation; the coordinator owns the rule
    /// that `Tracking -> Full` requires a matching, fresh publication. Returns
    /// false unless installed.
    pub fn coordinator_publication_committed(
        &self,
        identity: acquisition::LedgerIdentity,
        fresh: bool,
    ) -> bool {
        let mut guard = self.coordinator.lock().expect("coordinator lock");
        let Some(coordinator) = guard.as_mut() else {
            return false;
        };
        coordinator
            .handle_fact(acquisition::AcquisitionEvent::PublicationCommitted { identity, fresh });
        true
    }

    /// Submit a durable-handoff acknowledgement after the NetworkOps recipient
    /// has processed the exact completed-ledger item. This bridge owns no
    /// lifecycle decision: it retains the typed acknowledgement in the
    /// adapter's bounded priority lane. The strand processes that lane before
    /// completion producers can refill shared control slots, while still
    /// deferring all runner mutation to the next owner drain.
    pub(crate) fn acknowledge_coordinator_durable_handoff(
        &self,
        handoff: DurableHandoffId,
        session: SessionRef,
    ) -> bool {
        let mut guard = self.coordinator.lock().expect("coordinator lock");
        let Some(coordinator) = guard.as_mut() else {
            return false;
        };
        coordinator.retain_durable_handoff_ack(handoff, session)
    }

    /// True only while the coordinator still awaits this exact recipient ack.
    /// This filters delayed duplicate completed-ledger deliveries after the
    /// original session has already transitioned to `Complete`.
    pub(crate) fn coordinator_durable_handoff_is_pending(
        &self,
        handoff: DurableHandoffId,
        session: SessionRef,
    ) -> bool {
        self.coordinator
            .lock()
            .expect("coordinator lock")
            .as_ref()
            .is_some_and(|coordinator| coordinator.durable_handoff_is_pending(handoff, session))
    }

    /// Drain exact acknowledgements that the coordinator owner has already
    /// consumed. A successful control-queue enqueue never appears here until
    /// the matching runner session transitions to `Complete`.
    pub(crate) fn take_processed_coordinator_durable_acks(
        &self,
    ) -> Vec<(DurableHandoffId, SessionRef)> {
        self.coordinator
            .lock()
            .expect("coordinator lock")
            .as_mut()
            .map(|coordinator| coordinator.take_processed_durable_acks())
            .unwrap_or_default()
    }

    /// Report that the NetworkOps recipient could not accept an exact durable
    /// handoff. This only reopens and queues a retry; it does not drain or run
    /// coordinator state while the completed-ledger receiver may be locked.
    pub(crate) fn reject_coordinator_durable_handoff(
        &self,
        handoff: DurableHandoffId,
        session: SessionRef,
    ) -> bool {
        let mut guard = self.coordinator.lock().expect("coordinator lock");
        let Some(coordinator) = guard.as_mut() else {
            return false;
        };
        coordinator.recipient_rejected_durable_handoff(handoff, session)
    }

    /// The coordinator's immutable observer snapshot, for status consumers.
    pub fn coordinator_snapshot(&self) -> Option<RunnerSnapshot> {
        self.coordinator
            .lock()
            .expect("coordinator lock")
            .as_ref()
            .map(|adapter| adapter.snapshot())
    }

    /// Read the coordinator's exact validation-recovery latch without driving
    /// events. Sequences are required because validation provenance is keyed
    /// by the verified `(seq, hash)` identity, never by hash alone.
    pub fn coordinator_validation_recovery_latch(
        &self,
    ) -> (Option<(Uint256, u32)>, Option<(Uint256, u32)>) {
        let guard = self.coordinator.lock().expect("coordinator lock");
        let Some(coordinator) = guard.as_ref() else {
            return (None, None);
        };
        let exact = |target: Option<acquisition::LedgerTarget>| {
            target.and_then(|target| target.sequence().map(|seq| (target.hash(), seq)))
        };
        (
            exact(coordinator.current_validation_recovery_target()),
            exact(coordinator.current_validation_recovery_candidate()),
        )
    }

    #[cfg(test)]
    fn coordinator_validation_target(&self) -> Option<acquisition::LedgerTarget> {
        self.coordinator
            .lock()
            .expect("coordinator lock")
            .as_ref()
            .and_then(ProductionAdapter::current_validation_target)
    }

    /// True when rippled's recent-failure cache must suppress non-consensus
    /// re-admission. Consensus remains exempt because an advancing preferred
    /// LCL must be allowed to retry independently of history backfill.
    fn should_defer_coordinator_acquire(&self, hash: &Uint256, reason: AcquireReason) -> bool {
        reason != AcquireReason::Consensus && self.is_failure(hash)
    }

    /// Request a coordinator-owned acquisition. Mirrors `acquire`'s rejection
    /// guards; returns the minted session identity, the registry acquisition
    /// id, and the effects the coordinator emitted so the caller can trace
    /// peer request, timer, and phase transitions without reading coordinator
    /// internals.
    pub(crate) fn coordinator_acquire(
        &self,
        hash: Uint256,
        seq: u32,
        reason: AcquireReason,
    ) -> Option<CoordinatorAcquireOutcome> {
        self.coordinator_acquire_inner(hash, seq, reason, false)
    }

    fn coordinator_acquire_inner(
        &self,
        hash: Uint256,
        seq: u32,
        reason: AcquireReason,
        validation_target: bool,
    ) -> Option<CoordinatorAcquireOutcome> {
        if hash.is_zero() {
            tracing::warn!(target: "inbound_ledger", "coordinator_acquire: REJECTED zero hash");
            return None;
        }
        if self.stopping.load(Ordering::Acquire) {
            tracing::warn!(target: "inbound_ledger", %hash, "coordinator_acquire: REJECTED stopping");
            return None;
        }
        if self.need_network_ledger.load(Ordering::Acquire)
            && reason != AcquireReason::Generic
            && reason != AcquireReason::Consensus
        {
            tracing::info!(
                target: "inbound_ledger",
                %hash,
                seq,
                "coordinator_acquire: REJECTED need_network_ledger"
            );
            return None;
        }
        if self.should_defer_coordinator_acquire(&hash, reason) {
            tracing::debug!(
                target: "inbound_ledger",
                %hash,
                seq,
                ?reason,
                cooldown_secs = FAILURE_COOLDOWN.as_secs(),
                "coordinator_acquire: suppressed recent failed history target"
            );
            return None;
        }
        let mut coordinator_guard = self.coordinator.lock().expect("coordinator lock");
        let coordinator = coordinator_guard.as_mut()?;

        let acquisition_id = self.next_acquisition_id.fetch_add(1, Ordering::Relaxed);
        let inbound_reason = match reason {
            AcquireReason::History => ledger::InboundLedgerReason::History,
            AcquireReason::Generic => ledger::InboundLedgerReason::Generic,
            AcquireReason::Consensus => ledger::InboundLedgerReason::Consensus,
        };
        self.coordinator_origins.register(hash, seq, inbound_reason);

        coordinator.refresh_peers(self.coordinator_peer_snapshot());
        let peers = self
            .coordinator_peer_snapshot()
            .iter()
            .map(|peer| peer.id())
            .collect::<Vec<_>>();
        // A prior peerless demand may mint its session as this connectivity
        // fact restores peers; let that existing pending origin bind first.
        coordinator.connectivity(&peers);
        // Bind this demand before it reaches the runner. `SessionStarted` is
        // dispatched before the first peer send, including when replayed later
        // after a peerless interval. This is the ordinary class even when its
        // reason is Consensus, so it cannot evict preferred-LCL provenance.
        coordinator.register_pending_handoff_origin(hash, reason, acquisition_id, false);
        let target = acquisition::LedgerTarget::new(hash, (seq != 0).then_some(seq));
        let effects = if validation_target {
            coordinator.validation_target(target)
        } else {
            coordinator.acquire_requested(
                target,
                match reason {
                    AcquireReason::History => acquisition::AcquireReason::History,
                    AcquireReason::Generic => acquisition::AcquireReason::Generic,
                    AcquireReason::Consensus => acquisition::AcquireReason::Consensus,
                },
            )
        };
        let session = effects.iter().find_map(|effect| match effect {
            AcquisitionEffect::SessionStarted(session) => Some(*session),
            _ => None,
        });
        self.coordinator_origins
            .retain_targets(|target| coordinator.retains_session_origin_for_hash(target));
        if session.is_none() && !coordinator.retains_session_origin_for_hash(hash) {
            // Retain provenance only when the runner retained this exact
            // demand as live/deferred work. In particular, a phase-neutral
            // moving validation suppressed behind an exact recovery latch
            // must not overwrite a genuine peerless Generic origin.
            coordinator.clear_pending_handoff_origin(hash, reason, acquisition_id, false);
            self.coordinator_origins.remove(hash);
        }
        let Some(session) = session else {
            // An exact active target is intentionally coalesced by the runner:
            // it emits no second SendLedgerRequest and retains the original
            // session/handoff owner. Rejection (for example capacity or an
            // illegal phase) also emits no request. Neither case means a
            // session-creation fault, so keep this as a diagnostic rather than
            // a high-volume false warning during normal consensus polling.
            tracing::debug!(
                target: "inbound_ledger",
                %hash,
                seq,
                ?reason,
                "coordinator_acquire: request emitted no new session effect (coalesced or rejected)"
            );
            return None;
        };
        let handled = coordinator.drain();
        let failures = coordinator.take_terminal_failures();
        drop(coordinator_guard);
        self.record_coordinator_failures(failures);
        tracing::info!(
            target: "inbound_ledger",
            %hash,
            seq,
            ?reason,
            session_id = session.session_id().get(),
            acquisition_id,
            handled,
            "coordinator_acquire: session requested"
        );
        Some(CoordinatorAcquireOutcome {
            session,
            acquisition_id,
            effects,
        })
    }

    /// Route a wire `TmLedgerData` reply to a coordinator session through the
    /// immutable routing snapshot and the per-session admission gate. The
    /// overlay never mutates coordinator state; a deferred or unmatched reply
    /// has no session-side effect.
    pub(crate) fn coordinator_route_ledger_data(
        &self,
        peer_id: overlay::PeerId,
        message: &overlay::TmLedgerData,
    ) -> LedgerDataIngressDisposition {
        let ingress = self
            .coordinator_ingress
            .read()
            .expect("coordinator ingress read")
            .clone();
        let Some(ingress) = ingress else {
            return LedgerDataIngressDisposition::Unmatched;
        };
        ingress.route_ledger_data(peer_id, message)
    }

    /// Terminalize every coordinator session, drain its cancellation effects,
    /// and remove published routes before any dependent broker, timer, worker,
    /// or NodeStore resource is stopped. Late completions are then stale.
    pub fn coordinator_shutdown(&self) {
        let mut guard = self.coordinator.lock().expect("coordinator lock");
        let Some(coordinator) = guard.as_mut() else {
            return;
        };
        coordinator.handle_fact(acquisition::AcquisitionEvent::Shutdown);
    }

    /// Install the app-owned `LedgerMaster::storeLedger` equivalent used by
    /// completed Consensus/Generic acquisitions before their AcqDone-equivalent
    /// queue handoff. History completion deliberately uses its separate path.
    pub(crate) fn set_completed_ledger_store(&self, store: AcquisitionLedgerStore) {
        *self
            .completed_ledger_store
            .write()
            .expect("completed_ledger_store write") = Some(store);
    }

    /// Install the single application owner that compensates early resolver
    /// visibility if a later NodeStore durability fence fails.
    pub(crate) fn set_completed_ledger_revoker(&self, revoker: AcquisitionLedgerRevoker) {
        *self
            .completed_ledger_revoker
            .write()
            .expect("completed_ledger_revoker write") = Some(revoker);
    }

    /// Install the sole owner-level advance event sink. Inbound acquisition
    /// owns no publication policy; it reports only a real terminal/sweep
    /// lifecycle change so ApplicationRoot can coalesce planning on its
    /// validation/NetworkOps serialization boundary.
    pub(crate) fn set_publication_advance_notifier(&self, notifier: AcquisitionAdvanceNotifier) {
        *self
            .publication_advance_notifier
            .write()
            .expect("publication_advance_notifier write") = Some(notifier);
    }

    fn notify_publication_advance(&self) {
        if let Some(notify) = self
            .publication_advance_notifier
            .read()
            .expect("publication_advance_notifier read")
            .clone()
        {
            notify();
        }
    }

    /// Return a read-only, cumulative trace of inbound ledger work across all
    /// active and completed acquisitions. This is intentionally aggregate and
    /// is emitted only through sampled diagnostics or explicit fetch_info.
    pub(crate) fn lifecycle_snapshot(&self) -> AcquisitionLifecycleSnapshot {
        self.lifecycle.snapshot()
    }

    /// Record a parsed wire-level ledger-data packet before registry routing.
    pub fn note_wire_ledger_data(&self, node_count: usize) {
        self.lifecycle
            .wire_ledger_data
            .fetch_add(1, Ordering::Relaxed);
        self.lifecycle
            .wire_nodes
            .fetch_add(node_count as u64, Ordering::Relaxed);
    }

    /// Record a ledger-data relay that is intentionally not processed locally.
    pub fn note_wire_ledger_data_relayed(&self) {
        self.lifecycle.wire_relayed.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a malformed ledger-data message whose hash could not be parsed.
    pub fn note_wire_ledger_data_invalid_hash(&self) {
        self.lifecycle
            .wire_invalid_hash
            .fetch_add(1, Ordering::Relaxed);
    }

    /// Record whether an unroutable state packet was saved for later fetch-pack
    /// use. The call does not change routing or peer charging behavior.
    pub fn note_stale_packet_result(&self, stored: bool) {
        self.lifecycle
            .stale_packet_attempts
            .fetch_add(1, Ordering::Relaxed);
        if stored {
            self.lifecycle
                .stale_packets_stored
                .fetch_add(1, Ordering::Relaxed);
        }
    }

    // ─── Core API ────────────────────────────────────────────────────────

    /// Acquire a ledger by hash. Returns immediately if already complete.
    /// If not tracked, starts a new acquisition. If in-progress, touches
    /// the entry and returns None.
    ///
    /// Matches rippled's `InboundLedgers::acquire()`.
    pub fn acquire(&self, hash: Uint256, seq: u32, reason: AcquireReason) -> Option<Arc<Ledger>> {
        if hash.is_zero() {
            tracing::warn!(target: "inbound_ledger", "acquire: REJECTED zero hash");
            return None;
        }
        if self.stopping.load(Ordering::Acquire) {
            tracing::warn!(target: "inbound_ledger", %hash, "acquire: REJECTED stopping");
            return None;
        }
        if self.need_network_ledger.load(Ordering::Acquire)
            && reason != AcquireReason::Generic
            && reason != AcquireReason::Consensus
        {
            tracing::info!(
                target: "inbound_ledger",
                %hash,
                seq,
                "acquire: REJECTED need_network_ledger"
            );
            return None;
        }

        // M4.2-C3 coordinator switchover. When the coordinator owns session
        // lifecycle this is the only entry point. Re-acquire resolves only an
        // already-completed ledger held in the legacy completed index (rippled
        // `InboundLedgers::acquire` returns null for any ledger the registry
        // does not already hold). Every new start is delegated to the
        // coordinator, which notifies exactly once through the completed-ledger
        // channel after its durability fence; `acquire` therefore returns
        // `None` for new coordinator sessions, exactly like rippled. A caller
        // that re-requests a target the coordinator already completed and
        // consumed is suppressed by the coordinator's retained Complete
        // tombstone, matching rippled's completed-actor reuse window.
        if self.coordinator_installed() {
            let inner = timed_inner_lock(&self.inner);
            let completed = inner.entries.get(&hash).and_then(|entry| {
                if entry.completed_ledger.is_some() {
                    entry.completed_ledger.clone()
                } else if entry.state.completed.load(Ordering::Acquire) {
                    entry.state.completed_ledger()
                } else {
                    None
                }
            });
            drop(inner);
            if let Some(ledger) = completed {
                tracing::info!(
                    target: "inbound_ledger",
                    %hash,
                    seq,
                    ?reason,
                    "acquire: coordinator mode reused completed ledger"
                );
                return Some(ledger);
            }
            self.coordinator_acquire(hash, seq, reason);
            return None;
        }

        let mut inner = timed_inner_lock(&self.inner);

        // Existing acquisition: a failed one returns immediately, exactly as
        // rippled checks `InboundLedger::isFailed()` before `update()`. Do
        // not touch it or refresh recent_failures: its first failure owns the
        // one-minute sweep age and five-minute cooldown. A live acquisition
        // can update an unknown sequence and is retained for the sweep window.
        if let Some(entry) = inner.entries.get_mut(&hash) {
            self.lifecycle
                .acquisition_existing
                .fetch_add(1, Ordering::Relaxed);
            let entry_failed = entry.failed || entry.state.failed.load(Ordering::Acquire);
            let entry_id = entry.id;
            let entry_reason = entry.reason;
            let completion_acknowledged = entry.completion_acknowledged;
            if entry_failed {
                if reason == AcquireReason::Consensus {
                    tracing::info!(
                        target: "lcl_trace",
                        event = "preferred_lcl_registry_existing",
                        %hash,
                        requested_seq = seq,
                        requested_reason = ?reason,
                        acquisition_id = entry_id,
                        entry_reason = ?entry_reason,
                        entry_seq = entry.state.seq(),
                        completed = entry.completed_ledger.is_some()
                            || entry.state.completed.load(Ordering::Acquire),
                        failed = true,
                        completion_acknowledged,
                        returned_ledger = false,
                        "LCL trace: preferred target found as failed inbound entry"
                    );
                }
                return None;
            }
            entry.last_touched = Instant::now();
            let state = Arc::clone(&entry.state);
            let mut entry_seq = state.seq();
            let requested_seq_update = (entry_seq == 0 && seq != 0).then_some(seq);
            let is_completed = entry.state.completed.load(Ordering::Acquire);
            let completed_ledger = entry.completed_ledger.clone();

            // Do not call into AcquisitionState while holding the registry
            // mutex: worker failure reporting can arrive from acquisition
            // state and then lock this registry.
            drop(inner);
            if let Some(requested_seq_update) = requested_seq_update {
                state.update_seq(requested_seq_update);
            }
            // The mutable inbound ledger is authoritative when a duplicate
            // acquire races a verified header. Publish only its settled value
            // back to this exact live registry entry; never replace a known
            // sequence from another acquisition identity.
            let canonical_seq = state.seq();
            if canonical_seq != 0 {
                let mut inner = timed_inner_lock(&self.inner);
                if let Some(entry) = inner.entries.get_mut(&hash)
                    && entry.id == entry_id
                    && entry.seq == 0
                {
                    entry.seq = canonical_seq;
                }
                if let Some(entry) = inner.entries.get(&hash)
                    && entry.id == entry_id
                {
                    entry_seq = state.seq();
                }
            }
            let result = if is_completed {
                completed_ledger.or_else(|| state.completed_ledger())
            } else {
                completed_ledger
            };
            // An in-progress entry is already correlated by the single
            // `preferred_lcl_registry_started` event and the periodic
            // `preferred_lcl_candidate_lookup` result. Logging every
            // consensus caller that observes it produces an unbounded trace
            // storm without adding a lifecycle transition. Emit this event
            // only when the registry can actually return the completed ledger.
            if reason == AcquireReason::Consensus && result.is_some() {
                tracing::info!(
                    target: "lcl_trace",
                    event = "preferred_lcl_registry_existing",
                    %hash,
                    requested_seq = seq,
                    requested_reason = ?reason,
                    acquisition_id = entry_id,
                    entry_reason = ?entry_reason,
                    entry_seq,
                    completed = is_completed,
                    failed = false,
                    completion_acknowledged,
                    returned_ledger = result.is_some(),
                    returned_seq = result.as_ref().map(|ledger| ledger.header().seq),
                    "LCL trace: preferred target found in inbound registry"
                );
            }
            return result;
        }

        // Match rippled InboundLedgers::acquire: retain one acquisition per
        // hash and let the normal per-hash lifecycle, failure cooldown, and
        // idle sweep bound work. Do not globally serialize hash-only
        // consensus requests while the preferred LCL advances.

        // Validate required resources
        let ns = {
            let guard = self.node_store.read().expect("node_store read");
            match guard.as_ref() {
                Some(ns) => ns.clone(),
                None => {
                    tracing::warn!(
                        target: "inbound_ledger",
                        %hash,
                        seq,
                        "acquire: REJECTED node_store not attached"
                    );
                    return None;
                }
            }
        };
        // The reference PeerSet consults the live overlay on each addPeers
        // turn. Keep a cheap provider in the acquisition rather than freezing
        // a construction-time snapshot of peer sessions.
        let peer_provider: AcquisitionPeerProvider = {
            let overlay_rt = Arc::clone(&self.overlay_rt);
            Arc::new(move || {
                use overlay::Overlay as _;
                overlay_rt
                    .read()
                    .expect("inbound overlay_rt read")
                    .as_ref()
                    .map(|runtime| runtime.overlay().active_peers())
                    .unwrap_or_default()
            })
        };
        let initial_peers = peer_provider();
        let initial_peer_count = initial_peers.len();
        let acquisition_id = self.next_acquisition_id.fetch_add(1, Ordering::Relaxed);
        let failure_recorder: AcquisitionFailureRecorder = {
            let inner = Arc::clone(&self.inner);
            let revoker = Arc::clone(&self.completed_ledger_revoker);
            let publication_advance_notifier = Arc::clone(&self.publication_advance_notifier);
            Arc::new(move |failed_hash| {
                let (revoke, transitioned) = {
                    let mut inner = timed_inner_lock(&inner);
                    let (revoke, transitioned) =
                        inner
                            .entries
                            .get_mut(&failed_hash)
                            .map_or((None, false), |entry| {
                                if entry.id != acquisition_id || entry.failed {
                                    return (None, false);
                                }
                                entry.failed = true;
                                let revoke = entry.provisional_identity.take();
                                entry.completed_ledger.take();
                                (revoke, true)
                            });
                    if revoke.is_some() {
                        inner
                            .completed_ready
                            .retain(|(hash, id)| *hash != failed_hash || *id != acquisition_id);
                    }
                    record_recent_failure(&mut inner, failed_hash, Some(acquisition_id));
                    (revoke, transitioned)
                };
                if let Some(identity) = revoke
                    && let Some(revoker) = revoker
                        .read()
                        .expect("completed_ledger_revoker read")
                        .clone()
                {
                    revoker(identity);
                }
                if transitioned
                    && let Some(notify) = publication_advance_notifier
                        .read()
                        .expect("publication_advance_notifier read")
                        .clone()
                {
                    notify();
                }
            })
        };
        let completed_ledger_store = self
            .completed_ledger_store
            .read()
            .expect("completed_ledger_store read")
            .clone();
        let completion_recorder: AcquisitionCompletionRecorder = {
            let inner = Arc::clone(&self.inner);
            Arc::new(move |identity, ledger| {
                let mut inner = inner
                    .lock()
                    .expect("inbound_ledgers completion recorder lock");
                // Match InboundLedger::done(): terminal completion owns the
                // last-action update, so queue latency cannot make a newly
                // completed ledger eligible for an immediate sweep.
                let registered = if let Some(entry) = inner.entries.get_mut(&identity.target_hash)
                    && entry.id == identity.acquisition_id
                    && !entry.failed
                    && identity.ledger_hash == identity.target_hash
                    && ledger.header().seq == identity.ledger_seq
                {
                    entry.provisional_identity = Some(identity);
                    entry.completed_ledger = Some(Arc::clone(&ledger));
                    entry.last_touched = Instant::now();
                    true
                } else {
                    false
                };
                if registered && reason != AcquireReason::History {
                    if let Some(store) = &completed_ledger_store {
                        // Hold the registry identity through history visibility:
                        // cancellation cannot revoke before this exact cache
                        // publication is either complete or refused.
                        store(ledger);
                    }
                }
                if registered {
                    // Resolver visibility intentionally precedes the final
                    // fence, but AcqDone/NetworkOps adoption does not. The
                    // durable callback below owns both ready-queue publication
                    // and the coalesced advance event.
                } else {
                    // Match rippled's InboundLedgers::sweep ownership: once
                    // an entry is no longer resident, a late completion must
                    // not keep a full ledger alive outside the inbound map.
                    // A later validation/history request can acquire it again.
                    tracing::debug!(
                        target: "inbound_ledger",
                        hash = %identity.target_hash,
                        acquisition_id = identity.acquisition_id,
                        "dropping completion for swept inbound ledger"
                    );
                }
                registered
            })
        };
        let durable_completion_recorder: AcquisitionDurableCompletionRecorder = {
            let inner = Arc::clone(&self.inner);
            let publication_advance_notifier = Arc::clone(&self.publication_advance_notifier);
            Arc::new(move |identity| {
                let ready = {
                    let mut inner = inner
                        .lock()
                        .expect("inbound_ledgers durable completion recorder lock");
                    if let Some(entry) = inner.entries.get_mut(&identity.target_hash)
                        && entry.id == identity.acquisition_id
                        && !entry.failed
                        && entry.completed_ledger.is_some()
                        && entry.provisional_identity == Some(identity)
                    {
                        entry.provisional_identity = None;
                        inner
                            .completed_ready
                            .push_back((identity.target_hash, identity.acquisition_id));
                        true
                    } else {
                        false
                    }
                };
                if ready {
                    tracing::debug!(
                        target: "inbound_ledger",
                        event = "provisional_durable_ready",
                        target_hash = %identity.target_hash,
                        ledger_hash = %identity.ledger_hash,
                        ledger_seq = identity.ledger_seq,
                        acquisition_id = identity.acquisition_id,
                        store_generation = identity.store_generation,
                        persistence_generation = identity.persistence_generation,
                        "exact provisional inbound identity crossed durability fence"
                    );
                }
                if ready
                    && let Some(notify) = publication_advance_notifier
                        .read()
                        .expect("publication_advance_notifier read")
                        .clone()
                {
                    notify();
                }
            })
        };
        let sequence_promoter: AcquisitionSequencePromoter = {
            let inner = Arc::clone(&self.inner);
            Arc::new(move |verified_seq| {
                if verified_seq == 0 {
                    return;
                }
                let mut inner = inner
                    .lock()
                    .expect("inbound_ledgers sequence promoter lock");
                if let Some(entry) = inner.entries.get_mut(&hash)
                    && entry.id == acquisition_id
                    && entry.seq == 0
                {
                    entry.seq = verified_seq;
                }
            })
        };
        let acq_state = AcquisitionBuilder {
            hash: SHAMapHash::new(hash),
            acquisition_id,
            seq,
            reason,
            node_store: ns,
            read_broker: self.read_broker.clone(),
            tree_cache: Arc::clone(&self.tree_cache),
            fetch_pack: Arc::clone(&self.fetch_pack),
            store_tx: self.completed_ledgers_tx.clone(),
            failure_recorder,
            sequence_promoter,
            completion_recorder,
            durable_completion_recorder,
            shared_full_below: Arc::clone(&self.full_below),
            worker_pool: Arc::clone(&self.worker_pool),
            scheduler: Arc::clone(&self.scheduler),
            initial_peers,
            peer_provider,
            lifecycle: Arc::clone(&self.lifecycle),
        }
        .build();

        let now = Instant::now();
        inner.entries.insert(
            hash,
            Entry {
                id: acquisition_id,
                seq,
                reason,
                state: Arc::clone(&acq_state),
                last_touched: now,
                started_at: now,
                completed_ledger: None,
                provisional_identity: None,
                completion_acknowledged: false,
                failed: false,
            },
        );
        drop(inner);

        if reason == AcquireReason::Consensus {
            tracing::info!(
                target: "lcl_trace",
                event = "preferred_lcl_registry_started",
                %hash,
                seq,
                reason = ?reason,
                acquisition_id,
                initial_peer_count,
                "LCL trace: started a new preferred-target inbound acquisition"
            );
        }
        tracing::info!(
            target: "inbound_ledger",
            seq,
            %hash,
            reason = ?reason,
            acquisition_id,
            "Acquisition started"
        );
        self.lifecycle
            .acquisition_starts
            .fetch_add(1, Ordering::Relaxed);
        acq_state.start();
        None
    }

    /// Fire-and-forget acquire (for consensus/validation callers).
    /// Checks a pending set to avoid duplicate acquisitions.
    pub fn acquire_async(&self, hash: Uint256, seq: u32, reason: AcquireReason) {
        {
            let mut pending = self.pending_acquires.lock().expect("pending_acquires lock");
            if !pending.insert(hash) {
                return;
            }
        }
        let _ = self.acquire(hash, seq, reason);
        self.pending_acquires
            .lock()
            .expect("pending_acquires lock")
            .remove(&hash);
    }

    /// Start a closed-ledger acquisition when only its hash is known.
    ///
    /// A peer's advertised history range is not a reliable sequence binding
    /// for its current closed-ledger hash. Keep the sequence unknown until the
    /// response header establishes it, while retaining the hash as the primary
    /// acquisition key.
    pub fn acquire_closed_ledger_async(&self, hash: Uint256, reason: AcquireReason) {
        self.acquire_async(hash, 0, reason);
    }

    /// Start phase-neutral consensus-priority acquisition for the newest
    /// trusted-validation ledger (`RCLValidationsAdaptor::GetConsL2`).
    pub fn acquire_validation_ledger_async(&self, hash: Uint256) {
        if self.coordinator_installed() {
            let _ = self.coordinator_acquire_inner(hash, 0, AcquireReason::Consensus, true);
        } else {
            self.acquire_async(hash, 0, AcquireReason::Consensus);
        }
    }

    /// Start the sequence-qualified Generic acquisition requested by
    /// LedgerMaster::checkAccept for a trusted-validation miss. This is
    /// an ordinary Generic demand in both registry modes, matching rippled;
    /// only `RCLValidationsAdaptor::GetConsL2` uses `ValidationTarget`.
    pub fn acquire_check_accept_ledger_async(&self, hash: Uint256, seq: u32) {
        if self.coordinator_installed() {
            let _ = self.coordinator_acquire_inner(hash, seq, AcquireReason::Generic, false);
        } else {
            self.acquire_async(hash, seq, AcquireReason::Generic);
        }
    }

    /// Reserve exactly one actor-owned packet/byte lease before handing a
    /// decoded matching reply to `route_admitted_response_with_seq`. This
    /// performs no overlay work and retains no packet on `Deferred`.
    pub fn reserve_response_admission(
        &self,
        hash: &Uint256,
        packet: &InboundLedgerPacket,
    ) -> LedgerDataAdmission {
        // Coordinator-mode packets either carry a coordinator admission lease
        // or are unmatched. Never probe the legacy actor registry after the
        // switchover: bootstrap retains the rippled-equivalent unmatched
        // state-node fetch-pack path and base/transaction peer charge without
        // granting an actor mailbox any post-install authority.
        if self.coordinator_installed() {
            return LedgerDataAdmission::Unmatched;
        }
        let state = {
            let inner = timed_inner_lock(&self.inner);
            let Some(entry) = inner.entries.get(hash) else {
                return LedgerDataAdmission::Unmatched;
            };
            if entry.failed
                || entry.state.failed.load(Ordering::Acquire)
                || entry.state.stopped.load(Ordering::Acquire)
            {
                return LedgerDataAdmission::Terminal;
            }
            Arc::clone(&entry.state)
        };
        let bytes = packet
            .nodes
            .iter()
            .map(|node| node.node_data.len() + node.node_id.as_ref().map_or(0, Vec::len))
            .sum();
        match state.reserve_packet_admission(bytes) {
            Ok(lease) => LedgerDataAdmission::Admitted(lease),
            Err(PacketAdmissionReservation::Terminal) => LedgerDataAdmission::Terminal,
            Err(PacketAdmissionReservation::Deferred) => LedgerDataAdmission::Deferred,
        }
    }

    /// Consume a previously admitted response lease. The lease itself carries
    /// the actor identity; stale/swept leases become terminal or invalid and
    /// cannot fill a replacement acquisition's mailbox.
    pub fn route_admitted_response_with_seq(
        &self,
        hash: &Uint256,
        lease: InboundPacketAdmissionLease,
        peer_id: u64,
        response_seq: Option<u32>,
        packet: InboundLedgerPacket,
    ) -> LedgerDataRouteDisposition {
        // A live legacy lease prevents coordinator installation, but preserve
        // the invariant defensively for a raced/cancelled caller: no legacy
        // actor consumes a response after the coordinator becomes owner.
        if self.coordinator_installed() {
            return LedgerDataRouteDisposition::Unmatched;
        }
        self.lifecycle
            .route_attempts
            .fetch_add(1, Ordering::Relaxed);
        let state = {
            let inner = timed_inner_lock(&self.inner);
            let Some(entry) = inner.entries.get(hash) else {
                return LedgerDataRouteDisposition::Unmatched;
            };
            if entry.failed
                || entry.state.failed.load(Ordering::Acquire)
                || entry.state.stopped.load(Ordering::Acquire)
            {
                return LedgerDataRouteDisposition::Terminal;
            }
            Arc::clone(&entry.state)
        };
        match state.enqueue_packet_with_admission(lease, peer_id, response_seq, packet) {
            Err(_) => {
                self.lifecycle
                    .route_sequence_mismatch
                    .fetch_add(1, Ordering::Relaxed);
                LedgerDataRouteDisposition::SequenceMismatch
            }
            Ok(PacketEnqueue::Accepted) => {
                self.lifecycle
                    .route_accepted
                    .fetch_add(1, Ordering::Relaxed);
                LedgerDataRouteDisposition::Accepted
            }
            Ok(PacketEnqueue::Terminal) => {
                self.lifecycle
                    .route_terminal
                    .fetch_add(1, Ordering::Relaxed);
                LedgerDataRouteDisposition::Terminal
            }
            Ok(PacketEnqueue::InvalidLease) => LedgerDataRouteDisposition::AdmissionLeaseInvalid,
            Ok(PacketEnqueue::Full) => {
                unreachable!("a consumed packet admission lease reserves mailbox capacity")
            }
        }
    }

    /// Route a TMLedgerData response to the correct acquisition.
    pub fn route_response(&self, hash: &Uint256, peer_id: u64, packet: InboundLedgerPacket) {
        let _ = self.route_response_with_seq(hash, peer_id, None, packet);
    }

    /// Route a response while checking the sequence advertised on the wire.
    ///
    /// The ledger hash is the primary acquisition key. When a nonzero
    /// sequence is available, it is checked against the acquisition's live
    /// state-owned sequence so a peer cannot feed a response for another
    /// ledger into an active acquisition.
    pub fn route_response_with_seq(
        &self,
        hash: &Uint256,
        peer_id: u64,
        response_seq: Option<u32>,
        packet: InboundLedgerPacket,
    ) -> LedgerDataRouteDisposition {
        // Direct callers are also compatibility-only after installation; do
        // not let them bypass coordinator ingress and advance an actor.
        if self.coordinator_installed() {
            return LedgerDataRouteDisposition::Unmatched;
        }
        self.lifecycle
            .route_attempts
            .fetch_add(1, Ordering::Relaxed);
        let state = {
            let mut inner = timed_inner_lock(&self.inner);
            let Some(entry) = inner.entries.get_mut(hash) else {
                self.lifecycle.route_misses.fetch_add(1, Ordering::Relaxed);
                tracing::debug!(
                    target: "inbound_ledger",
                    %hash,
                    peer_id,
                    "route_response: registry miss"
                );
                return LedgerDataRouteDisposition::Unmatched;
            };
            if entry.failed
                || entry.state.failed.load(Ordering::Acquire)
                || entry.state.stopped.load(Ordering::Acquire)
            {
                self.lifecycle
                    .route_terminal
                    .fetch_add(1, Ordering::Relaxed);
                tracing::debug!(
                    target: "inbound_ledger",
                    %hash,
                    peer_id,
                    "route_response: ignored terminal acquisition"
                );
                return LedgerDataRouteDisposition::Terminal;
            }
            let state = Arc::clone(&entry.state);
            if entry.id != state.acquisition_id || state.hash.as_uint256() != hash {
                self.lifecycle.route_misses.fetch_add(1, Ordering::Relaxed);
                tracing::warn!(
                    target: "inbound_ledger",
                    %hash,
                    peer_id,
                    entry_id = entry.id,
                    state_id = state.acquisition_id,
                    "route_response: registry/acquisition identity mismatch"
                );
                return LedgerDataRouteDisposition::Unmatched;
            }
            // Wire receipt does not change rippled InboundLedger::lastAction.
            // Only construction, duplicate acquire/update, and terminal done
            // refresh the sweep clock.
            state
        };

        match state.enqueue_packet_with_sequence(peer_id, response_seq, packet) {
            Err(expected_seq) => {
                let response_seq = response_seq.expect("only a supplied sequence can mismatch");
                self.lifecycle
                    .route_sequence_mismatch
                    .fetch_add(1, Ordering::Relaxed);
                tracing::warn!(
                    target: "inbound_ledger",
                    %hash,
                    expected_seq,
                    response_seq,
                    peer_id,
                    acquisition_id = state.acquisition_id,
                    "route_response: sequence mismatch"
                );
                LedgerDataRouteDisposition::SequenceMismatch
            }
            Ok(PacketEnqueue::Accepted) => {
                self.lifecycle
                    .route_accepted
                    .fetch_add(1, Ordering::Relaxed);
                tracing::debug!(
                    target: "inbound_ledger",
                    %hash,
                    peer_id,
                    "route_response: registry hit"
                );
                LedgerDataRouteDisposition::Accepted
            }
            Ok(PacketEnqueue::Terminal) => {
                self.lifecycle
                    .route_terminal
                    .fetch_add(1, Ordering::Relaxed);
                tracing::debug!(
                    target: "inbound_ledger",
                    %hash,
                    peer_id,
                    "route_response: terminal acquisition"
                );
                LedgerDataRouteDisposition::Terminal
            }
            Ok(PacketEnqueue::InvalidLease) => LedgerDataRouteDisposition::AdmissionLeaseInvalid,
            Ok(PacketEnqueue::Full) => {
                // This packet matched a live acquisition. Do not recategorize
                // it as stale/fetch-pack material: the caller must apply its
                // explicit pressure policy instead.
                self.lifecycle
                    .route_terminal
                    .fetch_add(1, Ordering::Relaxed);
                tracing::warn!(
                    target: "inbound_ledger",
                    %hash,
                    peer_id,
                    "route_response: acquisition mailbox full"
                );
                LedgerDataRouteDisposition::MailboxFull
            }
        }
    }

    /// Remove entries idle for more than one minute, matching
    /// `InboundLedgersImp::sweep`. Failed hashes separately remain in the
    /// five-minute recent-failure cache.
    pub fn sweep(&self) {
        // TaggedCache only expires age/size entries when swept. Keep the
        // shared fetch-pack source on the same lifecycle cadence as rippled's
        // inbound-ledger cache rather than retaining stale peer data forever.
        self.fetch_pack.sweep();
        let now = Instant::now();
        let mut inner = timed_inner_lock(&self.inner);
        let mut to_remove = Vec::new();

        for (hash, entry) in &inner.entries {
            let idle_for = now.duration_since(entry.last_touched);
            // A successful completion must remain resolver-visible until its
            // AcqDone-equivalent consumer acknowledges persistence/acceptance.
            // Rippled stores before dispatching AcqDone; retaining this entry
            // prevents a delayed strand turn from silently losing that ledger.
            if idle_for > SWEEP_IDLE_TIMEOUT
                && !entry.state.has_pending_durability()
                && (!entry.state.completed.load(Ordering::Acquire)
                    && entry.completed_ledger.is_none()
                    || entry.completion_acknowledged)
            {
                to_remove.push((
                    *hash,
                    entry.id,
                    entry.last_touched,
                    entry.state.seq(),
                    entry.reason,
                    idle_for,
                    entry.failed || entry.state.failed.load(Ordering::Acquire),
                    entry.completed_ledger.is_some()
                        || entry.state.completed.load(Ordering::Acquire),
                ));
            }
        }

        // Revalidate and detach under the registry owner lock. A stale
        // snapshot must never cancel a same-hash acquisition that was touched
        // or replaced after the initial scan.
        let mut removed = Vec::new();
        for (hash, id, observed_touch, seq, reason, idle_for, failed, completed) in to_remove {
            let removable = inner.entries.get(&hash).is_some_and(|entry| {
                entry.id == id
                    && entry.last_touched == observed_touch
                    && now.duration_since(entry.last_touched) > SWEEP_IDLE_TIMEOUT
                    && !entry.state.has_pending_durability()
                    && (!entry.state.completed.load(Ordering::Acquire)
                        && entry.completed_ledger.is_none()
                        || entry.completion_acknowledged)
            });
            if removable {
                let entry = inner
                    .entries
                    .remove(&hash)
                    .expect("revalidated inbound entry");
                inner
                    .completed_ready
                    .retain(|(ready_hash, ready_id)| *ready_hash != hash || *ready_id != id);
                removed.push((hash, seq, reason, idle_for, failed, completed, entry));
            }
        }
        inner
            .recent_failures
            .retain(|_, when| when.elapsed() < FAILURE_COOLDOWN);
        drop(inner);

        let revoker = self
            .completed_ledger_revoker
            .read()
            .expect("completed_ledger_revoker read")
            .clone();
        let swept = !removed.is_empty();
        let mut stale_packets = Vec::new();
        for (hash, seq, reason, idle_for, failed, completed, entry) in removed {
            if let Some(identity) = entry.provisional_identity
                && let Some(revoke) = &revoker
            {
                revoke(identity);
            }
            let buffered = entry.state.take_buffered_packets();
            entry.state.cancel();
            stale_packets.push((hash, buffered));
            tracing::info!(
                target: "lcl_trace",
                event = "inbound_swept",
                %hash,
                seq,
                reason = ?reason,
                idle_ms = idle_for.as_millis() as u64,
                failed,
                completed,
                "LCL trace: inbound acquisition removed by sweep"
            );
        }

        // Mirrors InboundLedger destruction: useful state-node packets that
        // were received but not yet processed can seed a later acquisition.
        for (_, buffered) in stale_packets {
            for received in buffered {
                if received.packet.packet_type == ledger::InboundLedgerDataType::StateNode {
                    let stored = self.stash_stale_packet(&received.packet);
                    self.note_stale_packet_result(stored);
                }
            }
        }
        if swept {
            self.notify_publication_advance();
        }

        // Use the application's configured inbound-ledger sweep cadence for
        // coordinator owners too. Their exact one-minute timer only marks
        // eligibility; this global pass owns removal, matching rippled.
        let failures = {
            let mut guard = self
                .coordinator
                .lock()
                .expect("acquisition coordinator lock");
            match guard.as_mut() {
                Some(coordinator) => {
                    coordinator.handle_fact(acquisition::AcquisitionEvent::RegistrySweep);
                    coordinator.take_terminal_failures()
                }
                None => Vec::new(),
            }
        };
        self.record_coordinator_failures(failures);
    }

    /// Record a preferred-LCL request, selection, installation, or rejection
    /// without mutating acquisition or consensus state. `fetch_info` exposes
    /// only this most recent decision so normal recovery does not allocate an
    /// unbounded event history.
    pub fn record_recovery_lcl_decision(
        &self,
        preferred_hash: Uint256,
        candidate: Option<&Ledger>,
        source: &str,
        decision: &str,
    ) {
        let (candidate_hash, candidate_seq) = candidate
            .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq))
            .unzip();
        *self
            .recovery_lcl_decision
            .lock()
            .expect("recovery_lcl_decision lock") = Some(RecoveryLclDecision {
            recorded_at: Instant::now(),
            preferred_hash,
            candidate_hash,
            candidate_seq,
            source: source.to_owned(),
            decision: decision.to_owned(),
        });
    }

    /// Return a bounded, read-only acquisition snapshot for `fetch_info`.
    /// It does not execute a SHAMap walk, read NodeStore, add peers, or alter
    /// selection state.
    pub fn fetch_info_bounded(&self, limit: usize) -> JsonValue {
        let limit = limit.min(FETCH_INFO_MAX_ACQUISITIONS);
        let (entries, active, completed, failed, recent_failures, decision) = {
            let inner = timed_inner_lock(&self.inner);
            let mut active = 0u64;
            let mut completed = 0u64;
            let mut failed = 0u64;
            for entry in inner.entries.values() {
                if entry.failed || entry.state.failed.load(Ordering::Acquire) {
                    failed += 1;
                } else if entry.completed_ledger.is_some()
                    || entry.state.completed.load(Ordering::Acquire)
                {
                    completed += 1;
                } else {
                    active += 1;
                }
            }
            let entries = inner
                .entries
                .iter()
                .take(limit)
                .map(|(hash, entry)| {
                    (
                        *hash,
                        entry.state.seq(),
                        entry.reason,
                        entry.last_touched.elapsed().as_millis() as u64,
                        entry.completed_ledger.is_some()
                            || entry.state.completed.load(Ordering::Acquire),
                        entry.failed || entry.state.failed.load(Ordering::Acquire),
                        Arc::clone(&entry.state),
                    )
                })
                .collect::<Vec<_>>();
            (
                entries,
                active,
                completed,
                failed,
                inner.recent_failures.len() as u64,
                self.recovery_lcl_decision
                    .lock()
                    .expect("recovery_lcl_decision lock")
                    .clone(),
            )
        };

        let acquisitions = entries
            .into_iter()
            .map(
                |(hash, requested_seq, reason, idle_ms, complete, failed, state)| {
                    acquisition_snapshot_json(
                        hash,
                        requested_seq,
                        reason,
                        idle_ms,
                        complete,
                        failed,
                        state.diagnostics(),
                    )
                },
            )
            .collect();
        let worker = self.worker_pool.snapshot();
        let lifecycle = self.lifecycle_snapshot();
        let mut result = BTreeMap::from([
            ("active".to_owned(), JsonValue::Unsigned(active)),
            ("completed".to_owned(), JsonValue::Unsigned(completed)),
            ("failed".to_owned(), JsonValue::Unsigned(failed)),
            (
                "recent_failures".to_owned(),
                JsonValue::Unsigned(recent_failures),
            ),
            ("acquisitions".to_owned(), JsonValue::Array(acquisitions)),
            (
                "worker_pool".to_owned(),
                JsonValue::Object(BTreeMap::from([
                    (
                        "queued_jobs".to_owned(),
                        JsonValue::Unsigned(worker.queued_jobs as u64),
                    ),
                    (
                        "outstanding_ledger_data_jobs".to_owned(),
                        JsonValue::Unsigned(worker.outstanding_ledger_data_jobs as u64),
                    ),
                    (
                        "worker_count".to_owned(),
                        JsonValue::Unsigned(worker.worker_count as u64),
                    ),
                ])),
            ),
        ]);
        result.insert(
            "lifecycle".to_owned(),
            JsonValue::String(format!("{lifecycle:?}")),
        );
        result.insert(
            "coordinator".to_owned(),
            Self::coordinator_snapshot_json(self.coordinator_snapshot()),
        );
        result.insert(
            "last_recovery_lcl_decision".to_owned(),
            recovery_lcl_decision_json(decision),
        );
        JsonValue::Object(result)
    }

    fn coordinator_snapshot_json(snapshot: Option<RunnerSnapshot>) -> JsonValue {
        let Some(snapshot) = snapshot else {
            return JsonValue::Null;
        };
        let active_by_reason = snapshot
            .active_by_reason()
            .iter()
            .map(|(reason, count)| {
                (
                    format!("{reason:?}").to_ascii_lowercase(),
                    JsonValue::Unsigned(*count as u64),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let cancelled_by_reason = snapshot
            .cancelled_by_reason()
            .iter()
            .map(|(reason, count)| (reason.label().to_owned(), JsonValue::Unsigned(*count)))
            .collect::<BTreeMap<_, _>>();
        let failed_by_reason = snapshot
            .failed_by_reason()
            .iter()
            .map(|(reason, count)| (reason.label().to_owned(), JsonValue::Unsigned(*count)))
            .collect::<BTreeMap<_, _>>();
        let session_details = snapshot
            .session_details()
            .iter()
            .map(|session| {
                JsonValue::Object(BTreeMap::from([
                    (
                        "session_id".to_owned(),
                        JsonValue::Unsigned(session.session_id()),
                    ),
                    (
                        "target_hash".to_owned(),
                        JsonValue::String(session.target_hash().to_owned()),
                    ),
                    (
                        "target_sequence".to_owned(),
                        session
                            .target_sequence()
                            .map(|sequence| JsonValue::Unsigned(sequence.into()))
                            .unwrap_or(JsonValue::Null),
                    ),
                    (
                        "reason".to_owned(),
                        JsonValue::String(format!("{:?}", session.reason()).to_ascii_lowercase()),
                    ),
                    (
                        "phase".to_owned(),
                        JsonValue::String(session.phase().to_owned()),
                    ),
                    (
                        "network_admitted".to_owned(),
                        JsonValue::Bool(session.network_admitted()),
                    ),
                    (
                        "local_scan".to_owned(),
                        JsonValue::String(session.local_scan().to_owned()),
                    ),
                    (
                        "peers".to_owned(),
                        JsonValue::Unsigned(session.peer_count() as u64),
                    ),
                    (
                        "plan_seeded".to_owned(),
                        JsonValue::Bool(session.plan_seeded()),
                    ),
                    (
                        "plan_runs".to_owned(),
                        JsonValue::Unsigned(session.plan_runs()),
                    ),
                    (
                        "timeouts".to_owned(),
                        JsonValue::Unsigned(session.timeouts().into()),
                    ),
                    (
                        "packet_count".to_owned(),
                        JsonValue::Unsigned(session.packet_count()),
                    ),
                    (
                        "packet_bytes".to_owned(),
                        JsonValue::Unsigned(session.packet_bytes()),
                    ),
                    (
                        "pending_reads".to_owned(),
                        JsonValue::Unsigned(session.pending_reads() as u64),
                    ),
                    (
                        "read_backlog".to_owned(),
                        JsonValue::Unsigned(session.read_backlog() as u64),
                    ),
                    (
                        "pending_network".to_owned(),
                        JsonValue::Unsigned(session.pending_network() as u64),
                    ),
                    (
                        "retained_network".to_owned(),
                        JsonValue::Unsigned(session.retained_network() as u64),
                    ),
                    (
                        "persistence".to_owned(),
                        JsonValue::String(session.persistence().to_owned()),
                    ),
                ]))
            })
            .collect::<Vec<_>>();
        let validation_recovery_target = snapshot
            .validation_recovery_target()
            .map(|target| {
                JsonValue::Object(BTreeMap::from([
                    (
                        "hash".to_owned(),
                        JsonValue::String(target.hash().to_string()),
                    ),
                    (
                        "sequence".to_owned(),
                        target
                            .sequence()
                            .map(|sequence| JsonValue::Unsigned(sequence.into()))
                            .unwrap_or(JsonValue::Null),
                    ),
                ]))
            })
            .unwrap_or(JsonValue::Null);
        JsonValue::Object(BTreeMap::from([
            (
                "run_epoch".to_owned(),
                JsonValue::Unsigned(snapshot.run_epoch().get()),
            ),
            (
                "phase".to_owned(),
                JsonValue::String(format!("{:?}", snapshot.phase())),
            ),
            (
                "sessions".to_owned(),
                JsonValue::Unsigned(snapshot.session_count() as u64),
            ),
            (
                "detached_sessions".to_owned(),
                JsonValue::Unsigned(snapshot.detached_sessions() as u64),
            ),
            (
                "active_by_reason".to_owned(),
                JsonValue::Object(active_by_reason),
            ),
            (
                "session_details".to_owned(),
                JsonValue::Array(session_details),
            ),
            (
                "storage_generation".to_owned(),
                JsonValue::Unsigned(snapshot.storage_generation().get()),
            ),
            (
                "peers".to_owned(),
                JsonValue::Unsigned(snapshot.peer_count() as u64),
            ),
            (
                "events_handled".to_owned(),
                JsonValue::Unsigned(snapshot.events_handled()),
            ),
            (
                "rejected_events".to_owned(),
                JsonValue::Unsigned(snapshot.rejected_events()),
            ),
            (
                "sessions_started".to_owned(),
                JsonValue::Unsigned(snapshot.sessions_started()),
            ),
            (
                "sessions_cancelled".to_owned(),
                JsonValue::Unsigned(snapshot.sessions_cancelled()),
            ),
            (
                "cancelled_by_reason".to_owned(),
                JsonValue::Object(cancelled_by_reason),
            ),
            (
                "failed_by_reason".to_owned(),
                JsonValue::Object(failed_by_reason),
            ),
            (
                "sessions_completed".to_owned(),
                JsonValue::Unsigned(snapshot.sessions_completed()),
            ),
            (
                "handoff_rejections".to_owned(),
                JsonValue::Unsigned(snapshot.handoff_rejections()),
            ),
            (
                "peer_requests".to_owned(),
                JsonValue::Unsigned(snapshot.peer_requests()),
            ),
            (
                "local_scan_owners".to_owned(),
                JsonValue::Unsigned(snapshot.local_scan_owners() as u64),
            ),
            (
                "local_scan_waiters".to_owned(),
                JsonValue::Unsigned(snapshot.local_scan_waiters() as u64),
            ),
            (
                "validation_recovery_target".to_owned(),
                validation_recovery_target,
            ),
            (
                "validation_recovery_session".to_owned(),
                snapshot
                    .validation_recovery_session()
                    .map(|session| JsonValue::Unsigned(session.session_id().get()))
                    .unwrap_or(JsonValue::Null),
            ),
            (
                "timers_armed".to_owned(),
                JsonValue::Unsigned(snapshot.timers_armed()),
            ),
            (
                "packets_admitted".to_owned(),
                JsonValue::Unsigned(snapshot.packets_admitted()),
            ),
            (
                "packets_dropped".to_owned(),
                JsonValue::Unsigned(snapshot.packets_dropped()),
            ),
            (
                "plan_turns".to_owned(),
                JsonValue::Unsigned(snapshot.plan_turns()),
            ),
            (
                "fetch_pack_advances".to_owned(),
                JsonValue::Unsigned(snapshot.fetch_pack_advances()),
            ),
            ("shutdown".to_owned(), JsonValue::Bool(snapshot.shutdown())),
            (
                "stale_events".to_owned(),
                JsonValue::Unsigned(snapshot.stale_events()),
            ),
        ]))
    }

    /// Check if tracking a hash.
    pub fn contains(&self, hash: &Uint256) -> bool {
        let inner = timed_inner_lock(&self.inner);
        inner.entries.contains_key(hash)
    }

    /// Number of in-progress acquisitions.
    pub fn active_count(&self) -> usize {
        let inner = timed_inner_lock(&self.inner);
        inner
            .entries
            .values()
            .filter(|e| !e.failed && e.completed_ledger.is_none())
            .count()
    }

    /// Unit-test-only completion shortcut. Production terminal acquisition
    /// completion must cross the exact NodeStore durability barrier and record
    /// a `ProvisionalLedgerIdentity`; this helper intentionally cannot do so.
    #[cfg(test)]
    pub fn on_complete(&self, hash: Uint256, ledger: Arc<Ledger>) {
        let completion_id = {
            let mut inner = timed_inner_lock(&self.inner);
            let completion_id = if let Some(entry) = inner.entries.get_mut(&hash) {
                if entry.completed_ledger.is_none() {
                    entry.completed_ledger = Some(ledger);
                    entry.last_touched = Instant::now();
                    Some(entry.id)
                } else {
                    None
                }
            } else {
                None
            };
            if let Some(acquisition_id) = completion_id {
                inner.completed_ready.push_back((hash, acquisition_id));
            }
            completion_id
        };
        if completion_id.is_some() {
            self.notify_publication_advance();
        }
    }

    /// Notify that a ledger acquisition failed.
    pub fn on_failed(&self, hash: Uint256) {
        let state = {
            let mut inner = timed_inner_lock(&self.inner);
            record_recent_failure(&mut inner, hash, None);
            inner
                .entries
                .get(&hash)
                .map(|entry| Arc::clone(&entry.state))
        };
        if let Some(state) = state {
            state.cancel();
            self.notify_publication_advance();
        }
    }

    /// Log a failure for the given hash/seq (matches rippled's `logFailure`).
    pub fn log_failure(&self, hash: Uint256, _seq: u32) {
        {
            let mut inner = timed_inner_lock(&self.inner);
            record_recent_failure(&mut inner, hash, None);
        }
        self.notify_publication_advance();
    }

    /// Return the exact resolver-visible lifecycle identity while its final
    /// NodeStore barrier remains provisional. Callers may use it only as a
    /// wait key; it never grants adoption authority outside NetworkOps.
    pub(crate) fn provisional_identity(&self, hash: &Uint256) -> Option<ProvisionalLedgerIdentity> {
        let inner = timed_inner_lock(&self.inner);
        inner.entries.get(hash).and_then(|entry| {
            (!entry.failed
                && entry.completed_ledger.is_some()
                && !entry.state.completed.load(Ordering::Acquire))
            .then_some(entry.provisional_identity)
            .flatten()
        })
    }

    /// True only while a completed ledger is resolver-visible but its final
    /// NodeStore durability fence has not succeeded. Resolver access remains
    /// available; validation, LCL, and publication owners must not adopt it.
    pub(crate) fn is_provisional(&self, hash: &Uint256) -> bool {
        let inner = timed_inner_lock(&self.inner);
        inner.entries.get(hash).is_some_and(|entry| {
            !entry.failed
                && entry.completed_ledger.is_some()
                && !entry.state.completed.load(Ordering::Acquire)
        })
    }

    /// Check whether a hash is recorded as a recent failure (matches rippled's
    /// `isFailure`). Expires entries older than `FAILURE_COOLDOWN` (5 minutes).
    pub fn is_failure(&self, hash: &Uint256) -> bool {
        let mut inner = timed_inner_lock(&self.inner);
        inner
            .recent_failures
            .retain(|_, t| t.elapsed() < FAILURE_COOLDOWN);
        inner
            .recent_failures
            .get(hash)
            .is_some_and(|t| t.elapsed() < FAILURE_COOLDOWN)
    }

    /// Clear both `recent_failures` and `ledgers_` (matches rippled's
    /// `clearFailures`).
    pub fn clear_failures(&self) {
        let states = {
            let inner = timed_inner_lock(&self.inner);
            inner
                .entries
                .values()
                .map(|entry| Arc::clone(&entry.state))
                .collect::<Vec<_>>()
        };
        // Keep each entry resident through cancellation so the failure
        // recorder can retract any resolver-visible provisional ledger.
        for state in &states {
            state.cancel();
        }
        let changed = {
            let mut inner = timed_inner_lock(&self.inner);
            let changed = !inner.entries.is_empty()
                || !inner.recent_failures.is_empty()
                || !inner.completed_ready.is_empty();
            inner.recent_failures.clear();
            inner.completed_ready.clear();
            inner.entries.clear();
            changed
        };
        if changed {
            self.notify_publication_advance();
        }
    }

    /// Send current peers to all active legacy acquisition workers. Once the
    /// coordinator is installed it owns peer availability through typed facts;
    /// no registry actor is advanced from this compatibility API.
    pub fn send_peers(&self, peers: &[Arc<dyn Peer>]) {
        if self.coordinator_installed() {
            return;
        }
        let states: Vec<Arc<AcquisitionState>> = {
            let inner = timed_inner_lock(&self.inner);
            inner
                .entries
                .values()
                .filter(|e| !e.failed && e.completed_ledger.is_none())
                .map(|e| Arc::clone(&e.state))
                .collect()
        };
        for state in states {
            if state.stopped.load(Ordering::Acquire) || state.completed.load(Ordering::Acquire) {
                continue;
            }
            state.peer_set.refresh_peers(peers.iter().cloned());
        }
    }

    /// Store an object received in a fetch-pack response in the cache read by
    /// all acquisition workers.
    pub fn store_fetch_pack(&self, hash: Uint256, data: Vec<u8>) {
        self.fetch_pack.add_fetch_pack(hash, data);
        self.fetch_pack_wakes
            .lock()
            .expect("fetch-pack wake lock")
            .pending_hashes
            .insert(hash);
    }

    /// Stash state-node data from an untracked ledger response, matching
    /// `InboundLedgersImp::gotStaleData`.
    pub fn stash_stale_packet(&self, packet: &InboundLedgerPacket) -> bool {
        if packet.packet_type != ledger::InboundLedgerDataType::StateNode {
            return false;
        }
        for node in &packet.nodes {
            if node.node_id.is_none() {
                return false;
            }
            let Ok(Some(decoded)) =
                shamap::tree_node::SHAMapTreeNode::make_from_wire(&node.node_data)
            else {
                return false;
            };
            let Ok(prefixed) = decoded.serialize_with_prefix() else {
                return false;
            };
            self.fetch_pack
                .add_fetch_pack(*decoded.get_hash().as_uint256(), prefixed);
        }
        true
    }

    /// Complete the one LedgerMaster single-flight fetch-pack pass. It snapshots
    /// active acquisitions and schedules their local checks through the ready
    /// set, matching rippled `InboundLedgers::gotFetchPack()` without N direct
    /// worker submissions. Coordinator-owned sessions live outside the legacy
    /// registry, so the same pass completion is delivered to the coordinator as
    /// a typed fact: it re-advances each live session against the refreshed
    /// fetch-pack cache.
    pub fn finish_fetch_pack_pass(&self) {
        let generation = {
            let mut wakes = self.fetch_pack_wakes.lock().expect("fetch-pack wake lock");
            // `InboundLedgersImp::gotFetchPack` snapshots every active entry
            // and calls checkLocal for each fetch-pack completion. An empty or
            // late cache insertion is still that event; suppressing it leaves
            // retained descendants asleep indefinitely.
            wakes.next_generation = wakes.next_generation.wrapping_add(1).max(1);
            wakes.pending_hashes.clear();
            wakes.next_generation
        };
        if !self.coordinator_installed() {
            let states: Vec<Arc<AcquisitionState>> = {
                let inner = timed_inner_lock(&self.inner);
                inner
                    .entries
                    .values()
                    .filter(|entry| !entry.failed && entry.completed_ledger.is_none())
                    .map(|entry| Arc::clone(&entry.state))
                    .collect()
            };
            for state in states {
                if state.note_fetch_pack_generation(generation) {
                    self.scheduler.wake(
                        AcquisitionKey {
                            hash: *state.hash.as_uint256(),
                            id: state.acquisition_id,
                        },
                        &state,
                        ReadyCause::FETCH_PACK,
                    );
                }
            }
        }
        if let Some(coordinator) = self.coordinator.lock().expect("coordinator lock").as_ref() {
            // Fetch-pack availability is a coalescible wake: cached objects
            // remain queryable and a later wake/turn rechecks them. Never wait
            // on the bounded owner queue while holding its adapter mutex.
            let _ = coordinator.try_push_control(acquisition::AcquisitionEvent::FetchPackAvailable);
        }
    }

    /// Remove a specific entry.
    pub fn remove(&self, hash: &Uint256) {
        let state = {
            let inner = timed_inner_lock(&self.inner);
            inner
                .entries
                .get(hash)
                .map(|entry| Arc::clone(&entry.state))
        };
        // Cancellation must happen while the exact registry entry is still
        // present so its recorder can revoke a provisional resolver result.
        if let Some(state) = state {
            let acquisition_id = state.acquisition_id;
            state.cancel();
            let removed = {
                let mut inner = timed_inner_lock(&self.inner);
                let exact_entry = inner.entries.get(hash).is_some_and(|entry| {
                    entry.id == acquisition_id && Arc::ptr_eq(&entry.state, &state)
                });
                if exact_entry {
                    inner.entries.remove(hash);
                    inner.completed_ready.retain(|(ready_hash, ready_id)| {
                        ready_hash != hash || *ready_id != acquisition_id
                    });
                }
                exact_entry
            };
            if removed {
                self.notify_publication_advance();
            }
        }
    }

    /// Stop all acquisitions and shut down the worker pool.
    pub fn stop(&self) {
        self.stopping.store(true, Ordering::Release);

        // Phase 3 ordering: coordinator Shutdown terminalizes sessions, drains
        // CancelSession effects through the ports, and refreshes routes before
        // the registry stops the broker, timers, and worker pool.
        self.coordinator_shutdown();

        let states = {
            let inner = timed_inner_lock(&self.inner);
            inner
                .entries
                .values()
                .map(|entry| Arc::clone(&entry.state))
                .collect::<Vec<_>>()
        };
        for state in &states {
            state.cancel();
        }
        {
            let mut inner = timed_inner_lock(&self.inner);
            inner.entries.clear();
            inner.recent_failures.clear();
            inner.completed_ready.clear();
        }
        self.scheduler.stop();
        self.read_broker.stop();
        self.worker_pool.stop();
    }

    // ─── Catchup loop compatibility API ──────────────────────────────────

    /// Poll all completed acquisitions. Prefer `poll_results_bounded` from
    /// timer-driven consensus paths so a completion flood cannot starve the
    /// heartbeat.
    pub fn poll_results(&self) -> Vec<(Uint256, u64, Ledger, AcquireReason)> {
        self.poll_results_bounded(usize::MAX)
    }

    /// Poll at most `budget` successful terminal handoffs. A completion is
    /// enqueued by its terminal callback after it has been made registry-
    /// visible; polling therefore never scans arbitrary in-progress entries.
    /// Unacknowledged results rotate to the back of the queue, so failed
    /// persistence retries remain durable without starving later completions.
    pub fn poll_results_bounded(
        &self,
        budget: usize,
    ) -> Vec<(Uint256, u64, Ledger, AcquireReason)> {
        if budget == 0 {
            return Vec::new();
        }

        let mut inner = timed_inner_lock(&self.inner);
        // Examine only the entries that were ready at this poll's start. This
        // avoids returning the same unacknowledged completion repeatedly when
        // the caller's budget exceeds the ready queue length. The budget counts
        // live handoffs, not stale identities that must be discarded.
        let ready_this_turn = inner.completed_ready.len();
        let mut completed = Vec::with_capacity(ready_this_turn.min(budget));
        for _ in 0..ready_this_turn {
            if completed.len() >= budget {
                break;
            }
            let Some((hash, acquisition_id)) = inner.completed_ready.pop_front() else {
                break;
            };
            let ready = inner.entries.get(&hash).and_then(|entry| {
                if entry.id != acquisition_id
                    || entry.completion_acknowledged
                    || entry.failed
                    || entry.state.failed.load(Ordering::Acquire)
                {
                    return None;
                }
                entry
                    .completed_ledger
                    .clone()
                    .map(|ledger| (ledger, entry.reason))
            });
            let Some((ledger, reason)) = ready else {
                // Completion recording inserts the ledger before enqueuing
                // this exact (hash, acquisition_id), so a non-ready item is
                // stale: it was failed, acknowledged, swept, or replaced.
                // Drop it rather than rotating it indefinitely and consuming
                // later bounded polls ahead of live completions.
                continue;
            };
            inner.completed_ready.push_back((hash, acquisition_id));
            completed.push((hash, acquisition_id, (*ledger).clone(), reason));
        }
        completed
    }

    /// Acknowledge that a consumer has durably handled this completed result.
    /// A failed persistence attempt must not call this: the completed state is
    /// retained so the owner can retry on a later bounded poll.
    pub fn acknowledge_completed(&self, hash: &Uint256, acquisition_id: u64) {
        let mut inner = timed_inner_lock(&self.inner);
        let acknowledged = inner.entries.get_mut(hash).and_then(|entry| {
            let completed = !entry.failed
                && !entry.state.failed.load(Ordering::Acquire)
                && entry.id == acquisition_id
                && (entry.completed_ledger.is_some()
                    || entry.state.completed.load(Ordering::Acquire));
            if !completed {
                return None;
            }
            // Keep completed ledgers resident until the ordinary inbound
            // sweep. `acquire(hash, ...)` must still return this ledger,
            // just as rippled finds completed InboundLedger objects.
            entry.completion_acknowledged = true;
            Some((entry.state.seq(), entry.reason, entry.id))
        });
        if let Some((seq, reason, entry_id)) = acknowledged {
            inner.completed_ready.retain(|(ready_hash, ready_id)| {
                *ready_hash != *hash || *ready_id != acquisition_id
            });
            tracing::info!(
                target: "lcl_trace",
                event = "inbound_completion_acknowledged",
                %hash,
                seq,
                reason = ?reason,
                acquisition_id = entry_id,
                "LCL trace: completed inbound ledger retained until sweep after acknowledgement"
            );
        } else {
            tracing::warn!(
                target: "lcl_trace",
                event = "inbound_completion_ack_rejected",
                %hash,
                "LCL trace: completion acknowledgement found no completed registry entry"
            );
        }
    }

    /// Check if a specific hash is currently in-progress (not completed, not failed).
    pub fn is_in_progress(&self, hash: &Uint256) -> bool {
        let inner = timed_inner_lock(&self.inner);
        inner.entries.get(hash).is_some_and(|e| {
            !e.failed && e.completed_ledger.is_none() && !e.state.completed.load(Ordering::Acquire)
        })
    }

    /// Remove non-in-progress entries with seq below `min_seq`.
    /// Returns number of entries removed.
    pub fn remove_in_progress_below_seq(&self, min_seq: u32) -> usize {
        if min_seq <= 1 {
            return 0;
        }
        let candidates = {
            let inner = timed_inner_lock(&self.inner);
            inner
                .entries
                .iter()
                .filter(|(_, entry)| {
                    (entry.completed_ledger.is_some() || entry.failed)
                        && !entry.state.has_pending_durability()
                        && entry.state.seq() > 1
                        && entry.state.seq() < min_seq
                })
                .map(|(hash, entry)| (*hash, entry.id, Arc::clone(&entry.state)))
                .collect::<Vec<_>>()
        };
        for (_, _, state) in &candidates {
            state.cancel();
        }
        let count = {
            let mut inner = timed_inner_lock(&self.inner);
            let mut count = 0;
            for (hash, acquisition_id, state) in &candidates {
                let exact_entry = inner.entries.get(hash).is_some_and(|entry| {
                    entry.id == *acquisition_id && Arc::ptr_eq(&entry.state, state)
                });
                if exact_entry {
                    inner.entries.remove(hash);
                    inner.completed_ready.retain(|(ready_hash, ready_id)| {
                        ready_hash != hash || *ready_id != *acquisition_id
                    });
                    count += 1;
                }
            }
            count
        };
        if count != 0 {
            self.notify_publication_advance();
        }
        count
    }

    /// Log-visible summary shaped after reference InboundLedgers::getInfo.
    pub fn info_summary(&self) -> String {
        let inner = timed_inner_lock(&self.inner);
        let active = inner
            .entries
            .values()
            .filter(|e| {
                !e.failed
                    && e.completed_ledger.is_none()
                    && !e.state.completed.load(Ordering::Acquire)
            })
            .count();
        let complete = inner
            .entries
            .values()
            .filter(|e| e.completed_ledger.is_some() || e.state.completed.load(Ordering::Acquire))
            .count();
        let failed = inner.recent_failures.len();
        let mut entries: Vec<String> = inner
            .entries
            .iter()
            .map(|(hash, entry)| {
                let seq = entry.state.seq();
                let key = if seq > 1 {
                    seq.to_string()
                } else {
                    hash.to_string()
                };
                let state_label = if entry.failed {
                    "failed"
                } else if entry.completed_ledger.is_some()
                    || entry.state.completed.load(Ordering::Acquire)
                {
                    "complete"
                } else {
                    "in_progress"
                };
                format!("{}:{}", key, state_label)
            })
            .collect();
        entries.sort();
        format!(
            "active={} complete={} failed={} entries=[{}]",
            active,
            complete,
            failed,
            entries.join(",")
        )
    }

    /// Check whether an in-progress acquisition has the given sequence or hash.
    /// Completed entries remain until their consumer acknowledges successful
    /// cache/persistence handling, so they must not block the next history
    /// predecessor request.
    pub fn has_entry_for_seq_or_hash(&self, seq: u32, hash: &Uint256) -> bool {
        let inner = timed_inner_lock(&self.inner);
        inner.entries.iter().any(|(entry_hash, entry)| {
            !entry.failed
                && !entry.state.failed.load(Ordering::Acquire)
                && entry.completed_ledger.is_none()
                && !entry.state.completed.load(Ordering::Acquire)
                && (*entry_hash == *hash || entry.state.seq() == seq)
        })
    }

    /// Remove stale in-progress acquisitions that have had no progress.
    /// Used during cold bootstrap to free slots for new targets.
    /// Returns the number of entries removed.
    pub fn remove_stale_no_progress(&self, idle_timeout: Duration) -> Vec<(Uint256, u32)> {
        let now = Instant::now();
        let removed = {
            let mut inner = timed_inner_lock(&self.inner);
            let stale = inner
                .entries
                .iter()
                .filter(|(_, entry)| {
                    !entry.failed
                        && entry.completed_ledger.is_none()
                        && !entry.state.completed.load(Ordering::Acquire)
                        && now.duration_since(entry.last_touched) > idle_timeout
                })
                .map(|(hash, entry)| (*hash, entry.id))
                .collect::<Vec<_>>();
            let mut removed = Vec::with_capacity(stale.len());
            for (hash, id) in stale {
                let removable = inner.entries.get(&hash).is_some_and(|entry| {
                    entry.id == id
                        && !entry.failed
                        && entry.completed_ledger.is_none()
                        && !entry.state.completed.load(Ordering::Acquire)
                        && now.duration_since(entry.last_touched) > idle_timeout
                });
                if removable {
                    let entry = inner
                        .entries
                        .remove(&hash)
                        .expect("revalidated stale entry");
                    inner
                        .completed_ready
                        .retain(|(ready_hash, ready_id)| *ready_hash != hash || *ready_id != id);
                    removed.push((hash, entry.state.seq(), entry));
                }
            }
            removed
        };
        let revoker = self
            .completed_ledger_revoker
            .read()
            .expect("completed_ledger_revoker read")
            .clone();
        let stale = removed
            .iter()
            .map(|(hash, seq, _)| (*hash, *seq))
            .collect::<Vec<_>>();
        for (_, _, entry) in removed {
            if let Some(identity) = entry.provisional_identity
                && let Some(revoke) = &revoker
            {
                revoke(identity);
            }
            entry.state.cancel();
        }
        stale
    }

    /// Look up a hash for a target sequence from completed (but not yet polled)
    /// acquisitions' ledger skip lists.
    pub fn hash_for_seq_from_completed(
        &self,
        target_seq: u32,
    ) -> Option<basics::sha_map_hash::SHAMapHash> {
        // Snapshot candidates before consulting the acquisition's mutable
        // state. Workers can report failure while holding acquisition state,
        // so taking `inner` and then `state.mutable` would invert the
        // registry's worker callback lock order. The requested sequence may
        // be zero for preferred-LCL recovery; rank by the actual completed
        // ledger header rather than the original request sequence.
        let candidates: Vec<_> = {
            let inner = timed_inner_lock(&self.inner);
            inner
                .entries
                .values()
                .filter(|entry| {
                    !entry.failed
                        && !entry.state.failed.load(Ordering::Acquire)
                        && (entry.completed_ledger.is_some()
                            || entry.state.completed.load(Ordering::Acquire))
                })
                .map(|entry| (entry.completed_ledger.clone(), Arc::clone(&entry.state)))
                .collect()
        };

        let mut best: Option<(u32, basics::sha_map_hash::SHAMapHash)> = None;
        for (completed_ledger, state) in candidates {
            let mut consider = |ledger: &ledger::Ledger| {
                let ledger_seq = ledger.header().seq;
                if ledger_seq < target_seq {
                    return;
                }
                if let Some(hash) = ledger
                    .hash_of_seq(target_seq, &ledger::NullLedgerJournal)
                    .filter(|hash| !hash.is_zero())
                    && best.is_none_or(|(best_seq, _)| ledger_seq < best_seq)
                {
                    best = Some((ledger_seq, hash));
                }
            };

            if let Some(ledger) = completed_ledger {
                consider(&ledger);
            } else {
                let mutable = state.mutable.lock().expect("acq mutable (hash lookup)");
                if let Some(ledger) = mutable.inbound.ledger() {
                    consider(ledger);
                }
            }
        }
        best.map(|(_, hash)| hash)
    }

    /// Find a candidate reference hash from completed acquisitions for hash
    /// discovery when direct lookup fails.
    pub fn candidate_reference_hash_from_completed(
        &self,
        target_seq: u32,
    ) -> Option<(u32, basics::sha_map_hash::SHAMapHash)> {
        // Use candidate_ledger_for_seq logic inline: round up to next 256 boundary.
        let candidate_seq = target_seq.saturating_add(255) & !255;
        if candidate_seq <= target_seq {
            return None;
        }

        // As above, snapshot under the registry mutex and inspect acquisition
        // mutable state only after releasing it. Rank by an acquisition's
        // learned ledger header so completed hash-only recovery candidates
        // participate even though their initial request sequence was zero.
        let candidates: Vec<_> = {
            let inner = timed_inner_lock(&self.inner);
            inner
                .entries
                .values()
                .filter(|entry| {
                    !entry.failed
                        && !entry.state.failed.load(Ordering::Acquire)
                        && (entry.completed_ledger.is_some()
                            || entry.state.completed.load(Ordering::Acquire))
                })
                .map(|entry| (entry.completed_ledger.clone(), Arc::clone(&entry.state)))
                .collect()
        };

        let mut best: Option<(u32, basics::sha_map_hash::SHAMapHash)> = None;
        for (completed_ledger, state) in candidates {
            let mut consider = |ledger: &ledger::Ledger| {
                let ledger_seq = ledger.header().seq;
                if ledger_seq < target_seq {
                    return;
                }
                if let Some(hash) = ledger
                    .hash_of_seq(candidate_seq, &ledger::NullLedgerJournal)
                    .filter(|hash| !hash.is_zero())
                    && best.is_none_or(|(best_seq, _)| ledger_seq < best_seq)
                {
                    best = Some((ledger_seq, hash));
                }
            };

            if let Some(ledger) = completed_ledger {
                consider(&ledger);
            } else {
                let mutable = state.mutable.lock().expect("acq mutable (candidate)");
                if let Some(ledger) = mutable.inbound.ledger() {
                    consider(ledger);
                }
            }
        }
        best.map(|(_, hash)| (candidate_seq, hash))
    }
}

impl std::fmt::Debug for InboundLedgers {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InboundLedgers").finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::super::acquisition::{
        ACQ_MAILBOX_BYTE_CAPACITY, ACQ_MAILBOX_PACKET_CAPACITY, AcquisitionSnapshot,
        SequencePromotionAttempt, SequenceRoutePause,
    };
    use super::super::worker_pool::WorkerPool;
    use super::{
        AcquireReason, AcquisitionLifecycleCounters, AcquisitionLifecycleSnapshot,
        CompletedInboundLedger, InboundLedgers, LedgerDataRouteDisposition, RecoveryLclDecision,
        RegistryInner, SWEEP_IDLE_TIMEOUT, acquisition_snapshot_json, failure_matches_entry,
        record_recent_failure, record_recent_failure_at, recovery_lcl_decision_json,
        response_sequence_matches_request,
    };
    use acquisition::{DurableHandoffId, IdCounter, SessionRef, StoreGeneration};
    use basics::base_uint::Uint256;
    use basics::basic_config::BasicConfig;
    use basics::hardened_hash::HardenedHashBuilder;
    use basics::tagged_cache::MonotonicClock;
    use ledger::{FetchPackCache, InboundLedgerDataType, InboundLedgerPacket, Ledger};
    use nodestore::{DummyScheduler, ManagerImp, NullJournal, Scheduler};
    use overlay::{Peer, PeerImp, PeerSet as _};
    use protocol::{JsonValue, PublicKey};
    use shamap::family::FullBelowCacheImpl;
    use shamap::tree_node_cache::TreeNodeCache;
    use std::collections::{BTreeMap, HashMap, VecDeque};
    use std::net::SocketAddr;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Arc, mpsc};
    use std::time::{Duration, Instant};
    use tempfile::TempDir;

    /// Build the same real in-memory node store used by the acquisition
    /// integration fixtures. `acquire` performs a local-store check before
    /// processing ingress, so a genuine store keeps this route test on the
    /// production path.
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

    fn registry_with_manual_worker_pool(worker_pool: Arc<WorkerPool>) -> (TempDir, InboundLedgers) {
        let (dir, node_store) = test_node_store();
        let (completed_tx, _completed_rx) = mpsc::sync_channel(1);
        let registry = InboundLedgers::with_worker_pool(
            Arc::new(TreeNodeCache::new(
                "registry-ingress-test",
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
            worker_pool,
        );
        registry.set_node_store(node_store);
        (dir, registry)
    }

    fn packet_with_exact_payload_bytes(bytes: usize) -> InboundLedgerPacket {
        InboundLedgerPacket::new(
            InboundLedgerDataType::StateNode,
            vec![ledger::InboundLedgerNodeData::new(None, vec![0xA5; bytes])],
        )
    }

    fn active_state(
        registry: &InboundLedgers,
        hash: &Uint256,
    ) -> Arc<super::super::acquisition::AcquisitionState> {
        let inner = registry.inner.lock().expect("registry lock");
        Arc::clone(&inner.entries.get(hash).expect("active acquisition").state)
    }

    #[test]
    fn completed_inbound_ledger_requires_complete_coordinator_identity_for_ack() {
        let mut ids = IdCounter::new();
        let session = SessionRef::new(
            ids.next_id(),
            ids.next_id(),
            Uint256::from(1),
            ids.next_id(),
            StoreGeneration::new(1),
        );
        let ledger = Arc::new(Ledger::from_ledger_seq_and_close_time(1, 1, false));
        let complete = CompletedInboundLedger {
            ledger: Arc::clone(&ledger),
            reason: AcquireReason::Consensus,
            acquisition_id: 1,
            from_coordinator: true,
            durable_handoff: Some(DurableHandoffId::new(7)),
            coordinator_session: Some(session),
        };
        assert_eq!(
            complete.coordinator_handoff(),
            Some((DurableHandoffId::new(7), session))
        );

        let legacy = CompletedInboundLedger {
            ledger,
            reason: AcquireReason::Consensus,
            acquisition_id: 1,
            from_coordinator: false,
            durable_handoff: None,
            coordinator_session: None,
        };
        assert_eq!(legacy.coordinator_handoff(), None);
    }

    #[test]
    fn response_admission_127_128_129_and_byte_boundaries_route_and_release_exactly_once() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let hash = Uint256::from_array([0xC2; 32]);
        assert!(registry.acquire(hash, 1, AcquireReason::Generic).is_none());
        let state = active_state(&registry, &hash);
        let empty = InboundLedgerPacket::new(InboundLedgerDataType::Base, Vec::new());

        let mut leases = Vec::with_capacity(ACQ_MAILBOX_PACKET_CAPACITY);
        for count in 1..=ACQ_MAILBOX_PACKET_CAPACITY {
            let lease = match registry.reserve_response_admission(&hash, &empty) {
                super::LedgerDataAdmission::Admitted(lease) => lease,
                _ => panic!("reservation {count} must fit the live mailbox"),
            };
            if count == ACQ_MAILBOX_PACKET_CAPACITY - 1 {
                assert_eq!(leases.len() + 1, 127, "the 127th lease remains admitted");
            }
            leases.push(lease);
        }
        assert_eq!(leases.len(), 128, "the 128th lease remains admitted");
        assert!(
            matches!(
                registry.reserve_response_admission(&hash, &empty),
                super::LedgerDataAdmission::Deferred
            ),
            "the 129th matching reply is explicit local backpressure, not a terminal reply"
        );

        drop(leases.pop().expect("one live reservation"));
        let routed_lease = match registry.reserve_response_admission(&hash, &empty) {
            super::LedgerDataAdmission::Admitted(lease) => lease,
            _ => panic!("one dropped lease must release exactly one slot"),
        };
        assert_eq!(
            registry.route_admitted_response_with_seq(
                &hash,
                routed_lease,
                77,
                Some(1),
                empty.clone()
            ),
            super::LedgerDataRouteDisposition::Accepted,
            "the replacement lease is consumed by the live route exactly once"
        );
        assert!(
            matches!(
                registry.reserve_response_admission(&hash, &empty),
                super::LedgerDataAdmission::Deferred
            ),
            "queued routed work plus unconsumed leases still occupies all 128 slots"
        );

        assert!(
            state.clear_terminal_work().is_empty(),
            "the count-boundary terminal clear owns no read tickets"
        );
        drop(leases);
        let mut fresh = Vec::with_capacity(ACQ_MAILBOX_PACKET_CAPACITY);
        for _ in 0..ACQ_MAILBOX_PACKET_CAPACITY {
            fresh.push(
                state
                    .reserve_packet_admission(0)
                    .expect("stale lease drops must not release a fresh reservation"),
            );
        }
        assert!(
            matches!(
                state.reserve_packet_admission(0),
                Err(super::super::acquisition::PacketAdmissionReservation::Deferred)
            ),
            "fresh 129th reservation remains deferred"
        );
        assert!(
            state.clear_terminal_work().is_empty(),
            "the fresh lease cleanup is idempotent and owns no read tickets"
        );
        drop(fresh);

        let below = packet_with_exact_payload_bytes(ACQ_MAILBOX_BYTE_CAPACITY - 1);
        let one_byte = packet_with_exact_payload_bytes(1);
        let below_lease = match registry.reserve_response_admission(&hash, &below) {
            super::LedgerDataAdmission::Admitted(lease) => lease,
            _ => panic!("4 MiB minus one byte must fit"),
        };
        let final_byte_lease = match registry.reserve_response_admission(&hash, &one_byte) {
            super::LedgerDataAdmission::Admitted(lease) => lease,
            _ => panic!("the final byte must fit the exact byte boundary"),
        };
        assert!(
            matches!(
                registry.reserve_response_admission(&hash, &one_byte),
                super::LedgerDataAdmission::Deferred
            ),
            "one byte above 4 MiB is explicit deferred backpressure"
        );
        drop((below_lease, final_byte_lease));

        let exact = packet_with_exact_payload_bytes(ACQ_MAILBOX_BYTE_CAPACITY);
        let exact_lease = match registry.reserve_response_admission(&hash, &exact) {
            super::LedgerDataAdmission::Admitted(lease) => lease,
            _ => panic!("an exact 4 MiB payload must fit"),
        };
        assert!(
            matches!(
                registry.reserve_response_admission(&hash, &one_byte),
                super::LedgerDataAdmission::Deferred
            ),
            "the next byte above an exact 4 MiB reservation is deferred"
        );
        drop(exact_lease);
        registry.stop();
    }

    #[test]
    fn admitted_lease_cancel_sweep_stop_and_drop_are_terminal_not_capacity_replies() {
        let empty = || InboundLedgerPacket::new(InboundLedgerDataType::Base, Vec::new());

        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let cancelled_hash = Uint256::from_array([0xC1; 32]);
        assert!(
            registry
                .acquire(cancelled_hash, 1, AcquireReason::Generic)
                .is_none()
        );
        let cancelled_state = active_state(&registry, &cancelled_hash);
        let cancelled_lease = match registry.reserve_response_admission(&cancelled_hash, &empty()) {
            super::LedgerDataAdmission::Admitted(lease) => lease,
            _ => panic!("active acquisition admits its first response"),
        };
        cancelled_state.cancel();
        assert_eq!(
            registry.route_admitted_response_with_seq(
                &cancelled_hash,
                cancelled_lease,
                77,
                Some(1),
                empty(),
            ),
            super::LedgerDataRouteDisposition::Terminal,
            "a cancelled acquisition is terminal, never a capacity or stale-data reply"
        );
        assert!(cancelled_state.reserve_packet_admission(0).is_err());
        registry.stop();

        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let swept_hash = Uint256::from_array([0xC0; 32]);
        assert!(
            registry
                .acquire(swept_hash, 1, AcquireReason::Generic)
                .is_none()
        );
        let swept_state = active_state(&registry, &swept_hash);
        let swept_lease = match registry.reserve_response_admission(&swept_hash, &empty()) {
            super::LedgerDataAdmission::Admitted(lease) => lease,
            _ => panic!("active acquisition admits its first response"),
        };
        {
            let mut inner = registry.inner.lock().expect("registry lock");
            inner
                .entries
                .get_mut(&swept_hash)
                .expect("active entry")
                .last_touched = Instant::now() - SWEEP_IDLE_TIMEOUT - Duration::from_secs(1);
        }
        registry.sweep();
        assert!(matches!(
            registry.reserve_response_admission(&swept_hash, &empty()),
            super::LedgerDataAdmission::Unmatched
        ));
        assert_eq!(
            registry.route_admitted_response_with_seq(
                &swept_hash,
                swept_lease,
                77,
                Some(1),
                empty()
            ),
            super::LedgerDataRouteDisposition::Unmatched,
            "a swept stale lease cannot be converted into a capacity or cancelled reply"
        );
        assert!(swept_state.reserve_packet_admission(0).is_err());
        registry.stop();

        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let stopped_hash = Uint256::from_array([0xBF; 32]);
        assert!(
            registry
                .acquire(stopped_hash, 1, AcquireReason::Generic)
                .is_none()
        );
        let stopped_state = active_state(&registry, &stopped_hash);
        let stopped_lease = match registry.reserve_response_admission(&stopped_hash, &empty()) {
            super::LedgerDataAdmission::Admitted(lease) => lease,
            _ => panic!("active acquisition admits its first response"),
        };
        registry.stop();
        assert_eq!(
            registry.route_admitted_response_with_seq(
                &stopped_hash,
                stopped_lease,
                77,
                Some(1),
                empty()
            ),
            super::LedgerDataRouteDisposition::Unmatched,
            "registry stop detaches and terminally clears the lease before its later drop"
        );
        assert!(stopped_state.reserve_packet_admission(0).is_err());
    }

    #[test]
    fn admitted_response_lease_consumes_one_actor_reservation_before_route() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let hash = Uint256::from_array([0xC4; 32]);
        assert!(registry.acquire(hash, 1, AcquireReason::Generic).is_none());
        let packet = InboundLedgerPacket::new(InboundLedgerDataType::Base, Vec::new());
        let lease = match registry.reserve_response_admission(&hash, &packet) {
            super::LedgerDataAdmission::Admitted(lease) => lease,
            _ => panic!("live acquisition must reserve its bounded actor lease"),
        };
        assert_eq!(
            registry.route_admitted_response_with_seq(&hash, lease, 77, Some(1), packet),
            super::LedgerDataRouteDisposition::Accepted,
            "a consumed lease cannot be re-admitted or require a second scheduler reservation"
        );
        assert_eq!(registry.lifecycle_snapshot().route_accepted, 1);
        registry.stop();
    }

    #[test]
    fn empty_fetch_pack_pass_wakes_active_acquisitions() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let hash = Uint256::from_array([0xC3; 32]);
        assert!(registry.acquire(hash, 1, AcquireReason::Generic).is_none());
        let state = {
            let inner = registry.inner.lock().expect("registry lock");
            Arc::clone(&inner.entries.get(&hash).expect("active entry").state)
        };
        assert!(!state.fetch_pack_ready.load(Ordering::Acquire));
        registry.finish_fetch_pack_pass();
        assert!(
            state.fetch_pack_ready.load(Ordering::Acquire),
            "every fetch-pack completion, including an empty one, wakes checkLocal"
        );
        registry.stop();
    }

    #[test]
    fn coordinator_mode_bypasses_legacy_response_admission() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};

        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(Arc::clone(&worker_pool));
        registry.set_phase_state(Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Disconnected,
        )));
        assert!(registry.install_coordinator());

        let packet = InboundLedgerPacket::new(InboundLedgerDataType::Base, Vec::new());
        assert!(matches!(
            registry.reserve_response_admission(&Uint256::from_array([0xC5; 32]), &packet),
            super::LedgerDataAdmission::Unmatched
        ));
        assert_eq!(
            registry
                .route_response_with_seq(&Uint256::from_array([0xC5; 32]), 99, Some(1), packet,),
            super::LedgerDataRouteDisposition::Unmatched
        );
        assert_eq!(registry.active_count(), 0);
        assert_eq!(
            worker_pool.snapshot().queued_jobs,
            0,
            "coordinator-mode unmatched traffic must not wake a legacy actor"
        );
        registry.stop();
    }

    #[test]
    fn moving_validation_candidates_keep_session_origins_bounded_and_none_withdraws() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};

        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        registry.set_phase_state(Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Full,
        )));
        assert!(registry.install_coordinator());

        assert!(registry.coordinator_validation_recovery_target(Some((Uint256::from(70), 70))));
        assert_eq!(registry.coordinator_origins.len(), 1);
        assert_eq!(
            registry.coordinator_validation_recovery_latch(),
            (Some((Uint256::from(70), 70)), None)
        );
        assert!(registry.coordinator_validation_recovery_target(Some((Uint256::from(71), 71))));
        assert_eq!(registry.coordinator_origins.len(), 2);
        assert_eq!(
            registry.coordinator_validation_recovery_latch(),
            (Some((Uint256::from(70), 70)), Some((Uint256::from(71), 71)))
        );
        assert!(registry.coordinator_validation_recovery_target(Some((Uint256::from(72), 72))));
        assert_eq!(registry.coordinator_origins.len(), 2);
        assert_eq!(
            registry.coordinator_validation_recovery_latch(),
            (Some((Uint256::from(70), 70)), Some((Uint256::from(72), 72)))
        );
        assert!(registry.coordinator_validation_recovery_target(None));
        assert_eq!(registry.coordinator_origins.len(), 1);
        assert_eq!(
            registry.coordinator_validation_recovery_latch(),
            (Some((Uint256::from(70), 70)), None)
        );
    }

    #[test]
    fn check_accept_misses_remain_generic_without_mutating_recovery_latch() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};

        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        registry.set_phase_state(Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Full,
        )));
        assert!(registry.install_coordinator());
        let anchor = (Uint256::from(80), 80);
        assert!(registry.coordinator_validation_recovery_target(Some(anchor)));

        for seq in 81..181 {
            registry.acquire_check_accept_ledger_async(Uint256::from(seq), seq as u32);
        }

        assert_eq!(
            registry.coordinator_validation_recovery_latch(),
            (Some(anchor), None),
            "ordinary checkAccept misses must not become moving validation targets"
        );
        let snapshot = registry
            .coordinator_snapshot()
            .expect("coordinator snapshot");
        assert_eq!(
            snapshot
                .active_by_reason()
                .get(&acquisition::AcquireReason::Consensus),
            None,
            "checkAccept Generic misses must not be promoted to consensus priority"
        );
        assert_eq!(
            registry.coordinator_validation_target(),
            None,
            "checkAccept Generic misses must not mutate GetConsL2 validation-target state"
        );
    }

    #[test]
    fn peerless_moving_check_accept_origins_follow_the_bounded_generic_owner() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};

        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        registry.set_phase_state(Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Full,
        )));
        assert!(registry.install_coordinator());

        for seq in 81..181 {
            registry.acquire_check_accept_ledger_async(Uint256::from(seq), seq as u32);
        }

        assert_eq!(
            registry.coordinator_origins.len(),
            1,
            "superseded peerless Generic tips must not leak hash-keyed origin metadata"
        );
        assert_eq!(
            registry.coordinator_validation_target(),
            None,
            "peerless checkAccept Generic misses must not become ValidationTargets"
        );

        let get_cons_l2 = Uint256::from(200);
        registry.acquire_validation_ledger_async(get_cons_l2);
        assert_eq!(
            registry.coordinator_validation_target(),
            Some(acquisition::LedgerTarget::new(get_cons_l2, None)),
            "GetConsL2 remains the dedicated consensus-priority ValidationTarget path"
        );
    }

    #[test]
    fn coordinator_install_rejects_an_unacknowledged_legacy_completion() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};

        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let mut ledger = Ledger::from_ledger_seq_and_close_time(48, 1_000, false);
        ledger.set_immutable(true);
        let ledger = Arc::new(ledger);
        let hash = *ledger.header().hash.as_uint256();
        assert!(
            registry
                .acquire(hash, 0, AcquireReason::Consensus)
                .is_none()
        );
        registry.on_complete(hash, Arc::clone(&ledger));
        active_state(&registry, &hash).cancel();
        registry.set_phase_state(Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Disconnected,
        )));

        assert!(
            !registry.install_coordinator(),
            "the legacy ready-queue handoff must finish before coordinator ownership starts"
        );
        let completed = registry.poll_results_bounded(1);
        assert_eq!(completed.len(), 1);
        registry.acknowledge_completed(&hash, completed[0].1);
        assert!(
            registry.install_coordinator(),
            "an acknowledged terminal legacy cache entry no longer owns lifecycle work"
        );
        registry.stop();
    }

    #[test]
    fn coordinator_install_rejects_a_live_legacy_actor() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};

        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let hash = Uint256::from_array([0xC4; 32]);
        assert!(registry.acquire(hash, 1, AcquireReason::Generic).is_none());
        let legacy = active_state(&registry, &hash);
        registry.set_phase_state(Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Disconnected,
        )));

        assert!(
            !registry.install_coordinator(),
            "a live legacy actor and coordinator must never become concurrent session owners"
        );
        assert!(!registry.coordinator_installed());
        assert!(
            !legacy.stopped.load(Ordering::Acquire),
            "a rejected install preserves the explicit coordinator-absent compatibility path"
        );
        registry.stop();
    }

    #[test]
    fn fetch_pack_pass_notifies_the_coordinator_when_installed() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        registry.set_phase_state(Arc::new(
            crate::network::network_ops::SharedNetworkOpsState::new(
                crate::network::network_ops::NetworkOpsOperatingMode::Disconnected,
            ),
        ));
        assert!(
            registry.install_coordinator(),
            "node store and phase state enable the coordinator install"
        );
        assert_eq!(
            registry.coordinator_drain(),
            0,
            "no events are queued before any pass"
        );
        registry.finish_fetch_pack_pass();
        assert_eq!(
            registry.coordinator_drain(),
            1,
            "the pass completion reaches the coordinator as a typed fact"
        );
        registry.stop();
    }

    #[test]
    fn peer_availability_fact_and_heartbeat_route_through_the_coordinator() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let state = Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Disconnected,
        ));
        registry.set_phase_state(Arc::clone(&state));
        assert!(registry.install_coordinator());

        // Without the coordinator installed the bridge reports false.
        let (_dir2, registry2) = registry_with_manual_worker_pool(Arc::new(WorkerPool::new(0)));
        assert!(!registry2.coordinator_report_peer_availability(&[]));
        assert!(!registry2.coordinator_heartbeat());

        state.set_need_network_ledger(false);
        // A usable-peer fact motivates Disconnected -> Connected without
        // changing rippled's independent startup-recovery latch.
        assert!(registry.coordinator_report_peer_availability(&[1u32]));
        assert_eq!(
            state.operating_mode(),
            NetworkOpsOperatingMode::Connected,
            "the coordinator alone publishes the mode from the fact"
        );
        assert!(!state.need_network_ledger());
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &acquisition::SyncPhase::Connected
        );

        // The heartbeat re-publishes the phase for normalization without
        // changing sessions.
        assert!(registry.coordinator_heartbeat());
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &acquisition::SyncPhase::Connected
        );

        // A peer-loss fact demotes Connected -> Disconnected and preserves the
        // independent latch.
        assert!(registry.coordinator_report_peer_availability(&[]));
        assert_eq!(
            state.operating_mode(),
            NetworkOpsOperatingMode::Disconnected
        );
        assert!(!state.need_network_ledger());
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &acquisition::SyncPhase::Disconnected
        );
        registry.stop();
    }

    #[test]
    fn startup_fact_seeds_the_initial_phase_and_never_mints_a_session() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let state = Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Disconnected,
        ));
        registry.set_phase_state(Arc::clone(&state));
        assert!(registry.install_coordinator());

        // Without the coordinator installed the bridge reports false.
        let (_dir2, registry2) = registry_with_manual_worker_pool(Arc::new(WorkerPool::new(0)));
        assert!(!registry2.coordinator_startup(acquisition::SyncPhase::Connected));

        state.set_need_network_ledger(false);
        // The startup fact seeds the initial phase (start_valid Full) and
        // publishes only its mode. It never touches sessions or the latch.
        let full = acquisition::SyncPhase::Full {
            lcl: acquisition::LedgerIdentity::new(Uint256::from_array([0x21; 32]), 9),
            published: acquisition::LedgerIdentity::new(Uint256::from_array([0x22; 32]), 9),
        };
        assert!(registry.coordinator_startup(full));
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &full
        );
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Full);
        assert!(!state.need_network_ledger());
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .session_count(),
            0,
            "a startup seed must not mint an acquisition session"
        );

        // A networked startup re-seed (Connected) re-publishes the phase;
        // the seed is idempotent for the owner and still creates no session.
        assert!(registry.coordinator_startup(acquisition::SyncPhase::Connected));
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Connected);
        assert!(!state.need_network_ledger());
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .session_count(),
            0
        );
        registry.stop();
    }

    #[test]
    fn production_rotation_is_retained_coalesced_and_applied_before_owner_drain() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let registry = Arc::new(registry);
        let ledger_master_runtime = crate::AppLedgerMasterRuntime::default();

        // Exercise the production bootstrap ordering: online delete may
        // complete before the shared acquisition registry is installed.
        ledger_master_runtime.publish_store_rotation(2);
        ledger_master_runtime.publish_store_rotation(4);
        ledger_master_runtime.publish_store_rotation(3);
        ledger_master_runtime.install_inbound_ledgers(Arc::clone(&registry));
        registry.set_phase_state(Arc::new(
            crate::network::network_ops::SharedNetworkOpsState::new(
                crate::network::network_ops::NetworkOpsOperatingMode::Disconnected,
            ),
        ));
        assert!(registry.install_coordinator());
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .storage_generation()
                .get(),
            1,
            "the rotation worker must not mutate coordinator state"
        );

        let (handled, _) = registry.coordinator_drain_with_status();
        assert_eq!(handled, 1, "coalesced rotation is one owner fact");
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .storage_generation()
                .get(),
            4,
            "the newest retained generation becomes authoritative"
        );

        // Once installed, the same production publisher still leaves the
        // mutation pending until the serialized owner pass.
        ledger_master_runtime.publish_store_rotation(5);
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .storage_generation()
                .get(),
            4
        );
        assert_eq!(registry.coordinator_drain_with_status().0, 1);
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .storage_generation()
                .get(),
            5
        );
        registry.stop();
    }

    #[test]
    fn need_network_ledger_gate_rejects_history_but_lets_generic_reach_the_coordinator() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};
        let state = Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Disconnected,
        ));
        // The production registry shares the phase state's need_network_ledger
        // atomic (bootstrap passes `network_ops_state().need_network_ledger_arc()`),
        // so the admission gate reads the independent startup/recovery latch.
        let (_dir, node_store) = test_node_store();
        let (completed_tx, _completed_rx) = mpsc::sync_channel(1);
        let registry = InboundLedgers::with_worker_pool(
            Arc::new(TreeNodeCache::new(
                "registry-need-network-ledger-test",
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
            state.need_network_ledger_arc(),
            Arc::new(WorkerPool::new(0)),
        );
        registry.set_node_store(node_store);
        registry.set_phase_state(Arc::clone(&state));
        assert!(registry.install_coordinator());
        // Network startup owns the latch independently of the coordinator
        // phase; emulate bootstrap setting it before the startup fact.
        state.set_need_network_ledger(true);
        assert!(registry.coordinator_startup(acquisition::SyncPhase::Connected));
        assert!(state.need_network_ledger());

        // Usable peers make the coordinator's peer view non-empty (the harness
        // has no overlay runtime, so a later acquire re-feeds Connectivity(empty)
        // and demotes — that demotion is the observable that the gate was
        // bypassed and the coordinator was actually consulted).
        assert!(registry.coordinator_report_peer_availability(&[1u32]));
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &acquisition::SyncPhase::Connected
        );

        // A History acquire is rejected by the admission gate before the
        // coordinator is consulted: no Connectivity is fed and no session is
        // minted (rippled suppresses history work while needNetworkLedger).
        let hash = Uint256::from_array([0x31; 32]);
        assert!(
            registry
                .coordinator_acquire(hash, 9, AcquireReason::History)
                .is_none(),
            "History acquires are gated by need_network_ledger"
        );
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &acquisition::SyncPhase::Connected,
            "the gate must fire before any connectivity/acquire fact reaches the coordinator"
        );
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .session_count(),
            0
        );

        // A Generic acquire bypasses the gate and reaches the coordinator: it
        // feeds Connectivity(empty) (the harness overlay is absent), which
        // demotes Connected -> Disconnected. This is the M6-D replay-parent
        // path: the parent is requested as Generic precisely so it is not
        // rejected by this gate.
        assert!(
            registry
                .coordinator_acquire(hash, 9, AcquireReason::Generic)
                .is_none(),
            "no session is minted without overlay peers in the harness"
        );
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &acquisition::SyncPhase::Disconnected,
            "the Generic acquire reached the coordinator and fed Connectivity(empty)"
        );
        registry.stop();
    }

    #[test]
    fn lcl_and_publication_facts_route_through_the_coordinator() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let state = Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Disconnected,
        ));
        registry.set_phase_state(Arc::clone(&state));
        assert!(registry.install_coordinator());

        // Without the coordinator installed the bridges report false.
        let (_dir2, registry2) = registry_with_manual_worker_pool(Arc::new(WorkerPool::new(0)));
        let identity = acquisition::LedgerIdentity::new(Uint256::from_array([0x11; 32]), 7);
        assert!(!registry2.coordinator_lcl_installed(identity));
        assert!(!registry2.coordinator_publication_committed(identity, true));

        // Usable peers take the coordinator to Connected.
        assert!(registry.coordinator_report_peer_availability(&[1u32]));
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &acquisition::SyncPhase::Connected
        );

        // A locally resident preferred LCL installed while Connected drives
        // Connected -> Tracking through the phase port (rippled
        // switchLastClosedLedger clearing needNetworkLedger without a fetch).
        assert!(registry.coordinator_lcl_installed(identity));
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Tracking);
        assert!(!state.need_network_ledger());
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &acquisition::SyncPhase::Tracking { lcl: identity }
        );

        // A non-fresh publication cannot promote Tracking -> Full.
        assert!(registry.coordinator_publication_committed(identity, false));
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Tracking);
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &acquisition::SyncPhase::Tracking { lcl: identity }
        );

        // The matching fresh publication drives Tracking -> Full.
        assert!(registry.coordinator_publication_committed(identity, true));
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Full);
        assert!(!state.need_network_ledger());
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &acquisition::SyncPhase::Full {
                lcl: identity,
                published: identity
            }
        );
        registry.stop();
    }

    #[test]
    fn preferred_lcl_divergence_and_blocked_facts_route_through_the_coordinator() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let state = Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Disconnected,
        ));
        registry.set_phase_state(Arc::clone(&state));
        assert!(registry.install_coordinator());

        // Without the coordinator installed the bridges report false.
        let (_dir2, registry2) = registry_with_manual_worker_pool(Arc::new(WorkerPool::new(0)));
        let identity = acquisition::LedgerIdentity::new(Uint256::from_array([0x11; 32]), 7);
        let target = acquisition::LedgerTarget::new(Uint256::from_array([0x22; 32]), Some(9));
        assert!(!registry2.coordinator_preferred_lcl_divergence(target));
        assert!(!registry2.coordinator_blocked_with_no_target());

        // Reach Tracking: usable peers -> Connected, resident LCL -> Tracking.
        assert!(registry.coordinator_report_peer_availability(&[1u32]));
        assert!(registry.coordinator_lcl_installed(identity));
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Tracking);

        // A preferred-LCL divergence fact demotes Tracking -> Syncing without
        // minting a session or re-enabling the startup latch.
        assert!(registry.coordinator_preferred_lcl_divergence(target));
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Syncing);
        assert!(!state.need_network_ledger());
        assert_eq!(
            registry
                .coordinator_snapshot()
                .expect("coordinator snapshot")
                .phase(),
            &acquisition::SyncPhase::Syncing { target }
        );
        assert_eq!(registry.coordinator_snapshot().unwrap().session_count(), 0);

        // A no-consensus-positions fact while Syncing is rejected (legal only
        // from Full); it must not demote the phase.
        assert!(registry.coordinator_blocked_with_no_target());
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Syncing);

        // From Full, the blocked-state fact demotes Full -> Connected.
        let (_dir3, full_registry) = registry_with_manual_worker_pool(Arc::new(WorkerPool::new(0)));
        let full_state = Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Disconnected,
        ));
        full_registry.set_phase_state(Arc::clone(&full_state));
        assert!(full_registry.install_coordinator());
        assert!(full_registry.coordinator_report_peer_availability(&[1u32]));
        assert!(full_registry.coordinator_lcl_installed(identity));
        assert!(full_registry.coordinator_publication_committed(identity, true));
        assert_eq!(full_state.operating_mode(), NetworkOpsOperatingMode::Full);

        // Consensus quorum is independent from acquisition transport: the peer
        // remains retained while the public/coordinator mode disconnects.
        assert!(full_registry.coordinator_report_consensus_quorum(false));
        assert_eq!(
            full_state.operating_mode(),
            NetworkOpsOperatingMode::Disconnected
        );
        assert_eq!(
            full_registry.coordinator_snapshot().unwrap().peer_count(),
            1
        );
        assert!(full_registry.coordinator_report_consensus_quorum(true));
        assert_eq!(
            full_state.operating_mode(),
            NetworkOpsOperatingMode::Connected
        );
        assert!(full_registry.coordinator_lcl_installed(identity));
        assert!(full_registry.coordinator_publication_committed(identity, true));
        assert_eq!(full_state.operating_mode(), NetworkOpsOperatingMode::Full);

        assert!(full_registry.coordinator_blocked_with_no_target());
        assert_eq!(
            full_state.operating_mode(),
            NetworkOpsOperatingMode::Connected
        );
        assert!(!full_state.need_network_ledger());
        registry.stop();
        full_registry.stop();
    }

    #[test]
    fn preferred_lcl_no_change_retires_syncing_policy_and_restores_full_mode() {
        use crate::network::network_ops::{NetworkOpsOperatingMode, SharedNetworkOpsState};
        let (_dir, registry) = registry_with_manual_worker_pool(Arc::new(WorkerPool::new(0)));
        let state = Arc::new(SharedNetworkOpsState::new(
            NetworkOpsOperatingMode::Disconnected,
        ));
        registry.set_phase_state(Arc::clone(&state));
        assert!(registry.install_coordinator());
        let local = acquisition::LedgerIdentity::new(Uint256::from_array([0x41; 32]), 41);
        let stale = acquisition::LedgerTarget::new(Uint256::from_array([0x42; 32]), None);

        assert!(registry.coordinator_report_peer_availability(&[1u32]));
        assert!(registry.coordinator_lcl_installed(local));
        assert!(registry.coordinator_publication_committed(local, true));
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Full);
        assert!(registry.coordinator_preferred_lcl_divergence(stale));
        assert_eq!(
            state.operating_mode(),
            NetworkOpsOperatingMode::Connected,
            "a hash-only recovery target with stale validated age normalizes publicly to Connected"
        );

        assert!(registry.coordinator_preferred_lcl_reconciled(local));
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Tracking);
        assert!(registry.coordinator_publication_committed(local, true));
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Full);
        assert!(matches!(
            registry.coordinator_snapshot().expect("snapshot").phase(),
            acquisition::SyncPhase::Full { .. }
        ));
        registry.stop();
    }

    #[test]
    fn registry_ingress_coalesces_and_charges_selected_peer_malformed_packets() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(Arc::clone(&worker_pool));
        let hash = Uint256::from_array([0xC7; 32]);
        let peer = PeerImp::new(
            77,
            SocketAddr::from(([127, 0, 0, 1], 51235)),
            PublicKey::from_bytes([0x03; 33]),
            "registry-ingress-parity-peer",
        );
        peer.record_ledger(hash, 1);

        assert!(
            registry.acquire(hash, 1, AcquireReason::Generic).is_none(),
            "production registry creates the active acquisition"
        );
        let state = {
            let inner = registry.inner.lock().expect("registry lock");
            Arc::clone(
                &inner
                    .entries
                    .get(&hash)
                    .expect("active acquisition entry")
                    .state,
            )
        };
        let queued_before_ingress = worker_pool.snapshot().queued_jobs;
        assert_eq!(
            queued_before_ingress, 1,
            "acquire queues its real initialization job"
        );

        // Drain the synchronous initialization setup turn so packet admission
        // observes an idle mailbox token. Initialization refreshes from the
        // absent overlay runtime; install the selected live peer after that
        // setup turn, before the first bounded FIFO packet step runs.
        assert!(worker_pool.run_next_job_for_test());
        state
            .peer_set
            .refresh_peers(vec![Arc::clone(&peer) as Arc<dyn Peer>]);
        state.peer_set.add_peers(1, &mut |_| true, &mut |_| {});
        let queued_before_routes = worker_pool.snapshot().queued_jobs;

        let routed_before = registry.lifecycle_snapshot();
        let malformed = || InboundLedgerPacket::new(InboundLedgerDataType::Base, Vec::new());
        assert_eq!(
            registry.route_response_with_seq(&hash, 77, Some(1), malformed()),
            LedgerDataRouteDisposition::Accepted
        );
        assert_eq!(
            registry.route_response_with_seq(&hash, 77, Some(1), malformed()),
            LedgerDataRouteDisposition::Accepted
        );
        assert_eq!(
            worker_pool.snapshot().queued_jobs,
            queued_before_routes + 1,
            "two production registry routes queue one coalesced packet worker"
        );
        let routed = registry.lifecycle_snapshot();
        assert_eq!(routed.route_attempts, routed_before.route_attempts + 2);
        assert_eq!(routed.route_accepted, routed_before.route_accepted + 2);
        assert_eq!(
            routed.data_jobs_submitted,
            routed_before.data_jobs_submitted + 1
        );
        assert_eq!(
            routed.data_jobs_coalesced,
            routed_before.data_jobs_coalesced + 1
        );

        // The one coalesced packet worker processes both routed packets in
        // FIFO order within a single bounded turn.
        assert!(worker_pool.run_next_job_for_test());

        let charges = peer.charges();
        assert_eq!(
            charges.len(),
            2,
            "both routed packets are processed in FIFO continuation order"
        );
        for (fee, context) in charges {
            assert_eq!(fee, (*resource::FEE_MALFORMED_REQUEST).clone());
            assert_eq!(context, "ledger_data empty header");
        }
        let drained = registry.lifecycle_snapshot();
        assert_eq!(drained.packet_steps, routed_before.packet_steps + 2);
        assert_eq!(
            drained.packet_steps_completed,
            routed_before.packet_steps_completed + 2
        );
        assert_eq!(
            drained.packet_step_errors,
            routed_before.packet_step_errors + 2
        );
        registry.stop();
    }

    #[test]
    fn route_uses_promoted_state_sequence_not_stale_entry_snapshot() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let hash = Uint256::from_array([0xC6; 32]);
        assert!(
            registry.acquire(hash, 0, AcquireReason::Generic).is_none(),
            "hash-only acquisition must be active"
        );
        let state = {
            let inner = registry.inner.lock().expect("registry lock");
            Arc::clone(
                &inner
                    .entries
                    .get(&hash)
                    .expect("active acquisition entry")
                    .state,
            )
        };
        state.update_seq(2);
        assert_eq!(state.seq(), 2, "state CAS publishes the live sequence");
        {
            let mut inner = registry.inner.lock().expect("registry lock");
            inner
                .entries
                .get_mut(&hash)
                .expect("active acquisition entry")
                .seq = 0;
        }

        assert_eq!(
            registry.route_response_with_seq(
                &hash,
                77,
                Some(1),
                InboundLedgerPacket::new(InboundLedgerDataType::Base, Vec::new()),
            ),
            LedgerDataRouteDisposition::SequenceMismatch,
            "state-owned sequence rejects a mismatched concurrent wire response"
        );
        let lifecycle = registry.lifecycle_snapshot();
        assert_eq!(lifecycle.route_sequence_mismatch, 1);
        assert_eq!(lifecycle.route_accepted, 0);
        registry.stop();
    }

    #[test]
    fn route_and_sequence_promotion_are_linearized_before_packet_enqueue() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let registry = Arc::new(registry);
        let hash = Uint256::from_array([0xC5; 32]);
        assert!(
            registry.acquire(hash, 0, AcquireReason::Generic).is_none(),
            "hash-only acquisition must be active"
        );
        let state = {
            let inner = registry.inner.lock().expect("registry lock");
            Arc::clone(
                &inner
                    .entries
                    .get(&hash)
                    .expect("active acquisition entry")
                    .state,
            )
        };
        let route_pause = Arc::new(SequenceRoutePause::default());
        let promotion_attempt = Arc::new(SequencePromotionAttempt::default());
        state.set_sequence_route_pause_for_test(Arc::clone(&route_pause));
        state.set_sequence_promotion_attempt_for_test(Arc::clone(&promotion_attempt));

        let (route_tx, route_rx) = mpsc::sync_channel(1);
        let routing_registry = Arc::clone(&registry);
        let routing_thread = std::thread::spawn(move || {
            route_tx
                .send(routing_registry.route_response_with_seq(
                    &hash,
                    77,
                    Some(1),
                    InboundLedgerPacket::new(InboundLedgerDataType::Base, Vec::new()),
                ))
                .expect("route result receiver");
        });
        route_pause.wait_until_entered();

        let (promotion_tx, promotion_rx) = mpsc::sync_channel(1);
        let promotion_state = Arc::clone(&state);
        let promotion_thread = std::thread::spawn(move || {
            promotion_state.update_seq(2);
            promotion_tx
                .send(())
                .expect("promotion completion receiver");
        });
        promotion_attempt.wait_until_attempted();
        assert_eq!(
            state.seq(),
            0,
            "promotion cannot publish while a validated route still owns the enqueue boundary"
        );

        route_pause.release();
        assert_eq!(
            route_rx
                .recv_timeout(Duration::from_secs(5))
                .expect("route completion"),
            LedgerDataRouteDisposition::Accepted,
            "an initially unknown sequence accepts the header response before promotion"
        );
        promotion_rx
            .recv_timeout(Duration::from_secs(5))
            .expect("promotion completion");
        routing_thread.join().expect("routing thread");
        promotion_thread.join().expect("promotion thread");
        assert_eq!(state.seq(), 2);
        assert_eq!(
            registry.route_response_with_seq(
                &hash,
                77,
                Some(1),
                InboundLedgerPacket::new(InboundLedgerDataType::Base, Vec::new()),
            ),
            LedgerDataRouteDisposition::SequenceMismatch,
            "a response cannot validate as zero and enqueue after the nonzero promotion"
        );
        registry.stop();
    }

    #[test]
    fn acquire_async_initializes_once_before_ledger_data_work() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(Arc::clone(&worker_pool));
        let hash = Uint256::from_array([0xC8; 32]);

        registry.acquire_async(hash, 1, AcquireReason::Consensus);
        registry.acquire_async(hash, 1, AcquireReason::Consensus);

        // rippled runs InboundLedger::init from acquire(), so this must not
        // be a queued JtLedgerData-equivalent job. The only queued work is
        // the first TimeoutCounter callback armed by initialization.
        assert_eq!(registry.lifecycle_snapshot().initialization_jobs, 1);
        assert_eq!(
            worker_pool.snapshot().queued_jobs,
            1,
            "only the timeout callback may remain queued after synchronous initialization"
        );
        assert!(worker_pool.run_next_job_for_test());
        assert_eq!(registry.lifecycle_snapshot().initialization_jobs, 1);
        registry.stop();
    }

    #[test]
    fn acquire_initialization_does_not_starve_timeout_admission() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(Arc::clone(&worker_pool));

        // rippled's acquire() runs InboundLedger::init immediately. Each new
        // incomplete ledger then asks TimeoutCounter to queue recovery work;
        // with a five-job admission limit, the first five are live and only
        // the sixth is deferred. The scheduler FIFO retains that sixth turn
        // rather than filling the ledger-data queue, so a later timeout
        // callback can always be admitted once a reserved turn completes.
        for suffix in 1..=6u8 {
            registry.acquire(
                Uint256::from_array([suffix; 32]),
                u32::from(suffix),
                AcquireReason::Consensus,
            );
        }

        let lifecycle = registry.lifecycle_snapshot();
        assert_eq!(lifecycle.initialization_jobs, 6);
        assert_eq!(
            worker_pool.snapshot().queued_jobs,
            5,
            "deferred initialization must not fill the ledger-data queue"
        );

        // Draining the reserved turns admits the retained sixth and any rerun
        // demand; the five-turn boundary is never exceeded and no turn is
        // rejected or dropped.
        for _ in 0..5 {
            assert!(worker_pool.run_next_job_for_test());
            assert!(
                worker_pool.snapshot().queued_jobs <= 5,
                "the six live acquisitions must not exceed the five-slot boundary"
            );
        }
        registry.stop();
    }

    #[test]
    fn acquisition_lifecycle_snapshot_exposes_route_and_worker_boundaries() {
        let counters = AcquisitionLifecycleCounters::default();
        assert_eq!(counters.snapshot(), AcquisitionLifecycleSnapshot::default());

        counters.acquisition_starts.fetch_add(1, Ordering::Relaxed);
        counters.wire_ledger_data.fetch_add(2, Ordering::Relaxed);
        counters.route_attempts.fetch_add(3, Ordering::Relaxed);
        counters.route_accepted.fetch_add(1, Ordering::Relaxed);
        counters.route_misses.fetch_add(1, Ordering::Relaxed);
        counters
            .route_sequence_mismatch
            .fetch_add(1, Ordering::Relaxed);
        counters.data_jobs_submitted.fetch_add(1, Ordering::Relaxed);
        counters.data_jobs_started.fetch_add(1, Ordering::Relaxed);
        counters.packet_steps.fetch_add(4, Ordering::Relaxed);
        counters.terminal_completed.fetch_add(1, Ordering::Relaxed);

        assert_eq!(
            counters.snapshot(),
            AcquisitionLifecycleSnapshot {
                acquisition_starts: 1,
                wire_ledger_data: 2,
                route_attempts: 3,
                route_accepted: 1,
                route_misses: 1,
                route_sequence_mismatch: 1,
                data_jobs_submitted: 1,
                data_jobs_started: 1,
                packet_steps: 4,
                terminal_completed: 1,
                ..AcquisitionLifecycleSnapshot::default()
            }
        );
    }

    #[test]
    fn unknown_closed_ledger_sequence_accepts_authoritative_response_sequence() {
        assert!(response_sequence_matches_request(0, 105_847_104));
        assert!(response_sequence_matches_request(105_847_104, 0));
        assert!(response_sequence_matches_request(105_847_104, 105_847_104));
        assert!(!response_sequence_matches_request(105_847_103, 105_847_104));
    }

    #[test]
    fn stale_inbound_acquisitions_match_rippleds_one_minute_sweep() {
        assert_eq!(SWEEP_IDLE_TIMEOUT, Duration::from_secs(60));
    }

    #[test]
    fn recovery_lcl_diagnostic_reports_selected_candidate() {
        let preferred = Uint256::from_array([0xA5; 32]);
        let candidate = Uint256::from_array([0xB6; 32]);
        let JsonValue::Object(value) = recovery_lcl_decision_json(Some(RecoveryLclDecision {
            recorded_at: Instant::now(),
            preferred_hash: preferred,
            candidate_hash: Some(candidate),
            candidate_seq: Some(123),
            source: "completed_recovery".to_owned(),
            decision: "installed".to_owned(),
        })) else {
            panic!("recovery diagnostic must be an object");
        };

        assert_eq!(
            value.get("preferred_hash"),
            Some(&JsonValue::String(preferred.to_string()))
        );
        assert_eq!(
            value.get("candidate_hash"),
            Some(&JsonValue::String(candidate.to_string()))
        );
        assert_eq!(value.get("candidate_seq"), Some(&JsonValue::Unsigned(123)));
        assert_eq!(
            value.get("decision"),
            Some(&JsonValue::String("installed".to_owned()))
        );
    }

    #[test]
    fn failed_acquisition_enters_cooldown_without_waiting_for_sweep() {
        let hash = Uint256::from_array([0xF1; 32]);
        let mut inner = RegistryInner {
            entries: BTreeMap::new(),
            recent_failures: HashMap::new(),
            completed_ready: VecDeque::new(),
        };

        record_recent_failure(&mut inner, hash, None);

        assert!(
            inner
                .recent_failures
                .get(&hash)
                .is_some_and(|recorded_at| recorded_at.elapsed() < Duration::from_secs(1))
        );
    }

    #[test]
    fn repeated_failure_records_preserve_the_original_cooldown_time() {
        let hash = Uint256::from_array([0xF2; 32]);
        let first_failure = Instant::now() - Duration::from_secs(240);
        let mut inner = RegistryInner {
            entries: BTreeMap::new(),
            recent_failures: HashMap::new(),
            completed_ready: VecDeque::new(),
        };

        record_recent_failure_at(&mut inner, hash, None, first_failure);
        record_recent_failure_at(&mut inner, hash, None, Instant::now());

        assert_eq!(inner.recent_failures.get(&hash), Some(&first_failure));
    }

    #[test]
    fn delayed_failure_cannot_match_a_replacement_acquisition() {
        assert!(failure_matches_entry(None, 2));
        assert!(failure_matches_entry(Some(2), 2));
        assert!(!failure_matches_entry(Some(1), 2));
    }

    #[test]
    fn swept_unacknowledged_completion_remains_resolver_visible() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let mut ledger = Ledger::from_ledger_seq_and_close_time(44, 1_000, false);
        ledger.set_immutable(true);
        let ledger = Arc::new(ledger);
        let hash = *ledger.header().hash.as_uint256();
        assert!(
            registry
                .acquire(hash, 0, AcquireReason::Consensus)
                .is_none()
        );
        registry.on_complete(hash, Arc::clone(&ledger));
        {
            let mut inner = registry.inner.lock().expect("registry lock");
            inner
                .entries
                .get_mut(&hash)
                .expect("completed entry")
                .last_touched = Instant::now() - SWEEP_IDLE_TIMEOUT - Duration::from_secs(1);
        }

        registry.sweep();
        assert!(registry.contains(&hash));
        assert_eq!(registry.poll_results_bounded(1).len(), 1);
        registry.stop();
    }

    #[test]
    fn completion_ready_queue_bypasses_in_progress_registry_prefix() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        // These lower hashes would consume a scan budget before the completed
        // target in the former BTreeMap polling implementation.
        for fill in [0x01, 0x02, 0x03] {
            assert!(
                registry
                    .acquire(Uint256::from_array([fill; 32]), 0, AcquireReason::Consensus)
                    .is_none()
            );
        }

        let mut ledger = Ledger::from_ledger_seq_and_close_time(45, 1_000, false);
        ledger.set_immutable(true);
        let ledger = Arc::new(ledger);
        let hash = *ledger.header().hash.as_uint256();
        assert!(
            registry
                .acquire(hash, 0, AcquireReason::Consensus)
                .is_none()
        );
        registry.on_complete(hash, Arc::clone(&ledger));

        let first = registry.poll_results_bounded(1);
        assert_eq!(first.len(), 1);
        assert_eq!(first[0].0, hash);
        assert_eq!(
            first[0].1,
            registry
                .inner
                .lock()
                .expect("registry lock")
                .entries
                .get(&hash)
                .expect("completed entry")
                .id
        );

        // The retained handoff retries after a failed consumer turn, but it
        // is not duplicated within a single oversized poll.
        assert_eq!(registry.poll_results_bounded(8).len(), 1);
        registry.acknowledge_completed(&hash, first[0].1);
        assert!(registry.poll_results_bounded(1).is_empty());
        registry.stop();
    }

    #[test]
    fn stale_failed_completion_does_not_consume_next_ready_poll_slot() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);

        let stale_hash = Uint256::from_array([0xF4; 32]);
        assert!(
            registry
                .acquire(stale_hash, 0, AcquireReason::Consensus)
                .is_none()
        );
        let mut stale_ledger = Ledger::from_ledger_seq_and_close_time(46, 1_000, false);
        stale_ledger.set_immutable(true);
        registry.on_complete(stale_hash, Arc::new(stale_ledger));
        registry.on_failed(stale_hash);

        let mut live_ledger = Ledger::from_ledger_seq_and_close_time(47, 1_000, false);
        live_ledger.set_immutable(true);
        let live_ledger = Arc::new(live_ledger);
        let live_hash = *live_ledger.header().hash.as_uint256();
        assert!(
            registry
                .acquire(live_hash, 0, AcquireReason::Consensus)
                .is_none()
        );
        registry.on_complete(live_hash, Arc::clone(&live_ledger));

        let ready = registry.poll_results_bounded(1);
        assert_eq!(ready.len(), 1);
        assert_eq!(ready[0].0, live_hash);
        registry.acknowledge_completed(&live_hash, ready[0].1);
        assert!(registry.poll_results_bounded(1).is_empty());
        registry.stop();
    }

    #[test]
    fn acknowledged_completion_remains_acquirable_until_sweep() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let hash = Uint256::from_array([0xF5; 32]);
        assert!(
            registry
                .acquire(hash, 0, AcquireReason::Consensus)
                .is_none()
        );

        let mut ledger = Ledger::from_ledger_seq_and_close_time(42, 1_000, false);
        ledger.set_immutable(true);
        let ledger = Arc::new(ledger);
        registry.on_complete(hash, Arc::clone(&ledger));
        let acquisition_id = registry
            .inner
            .lock()
            .expect("registry lock")
            .entries
            .get(&hash)
            .expect("completed entry")
            .id;
        registry.acknowledge_completed(&hash, acquisition_id);

        assert!(registry.contains(&hash));
        assert_eq!(
            registry
                .acquire(hash, 0, AcquireReason::Consensus)
                .expect("completed acquisition remains available until sweep")
                .header()
                .seq,
            ledger.header().seq
        );
        registry.stop();
    }

    #[test]
    fn consensus_acquire_ignores_recent_failure_cooldown() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let hash = Uint256::from_array([0xF4; 32]);
        registry
            .inner
            .lock()
            .expect("registry lock")
            .recent_failures
            .insert(hash, Instant::now());

        assert!(
            registry
                .acquire(hash, 0, AcquireReason::Consensus)
                .is_none(),
            "consensus must create the hash-only target even after a History cooldown"
        );
        assert!(registry.contains(&hash));
        registry.stop();
    }

    #[test]
    fn coordinator_non_consensus_acquire_respects_recent_failure_cooldown() {
        let worker_pool = Arc::new(WorkerPool::new(0));
        let (_dir, registry) = registry_with_manual_worker_pool(worker_pool);
        let hash = Uint256::from_array([0xF5; 32]);
        registry
            .inner
            .lock()
            .expect("registry lock")
            .recent_failures
            .insert(hash, Instant::now());

        assert!(registry.should_defer_coordinator_acquire(&hash, AcquireReason::Generic));
        assert!(registry.should_defer_coordinator_acquire(&hash, AcquireReason::History));
        assert!(
            !registry.should_defer_coordinator_acquire(&hash, AcquireReason::Consensus),
            "preferred-LCL consensus recovery must not be blocked by history cooldown"
        );
        registry.stop();
    }

    #[test]
    fn delayed_failure_from_a_swept_acquisition_records_hash_cooldown() {
        let hash = Uint256::from_array([0xF3; 32]);
        let mut inner = RegistryInner {
            entries: BTreeMap::new(),
            recent_failures: HashMap::new(),
            completed_ready: VecDeque::new(),
        };

        record_recent_failure_at(&mut inner, hash, Some(17), Instant::now());

        assert!(
            inner.recent_failures.contains_key(&hash),
            "rippled AcqDone records the hash-wide cooldown even after the acquisition was swept"
        );
    }

    #[test]
    fn fetch_info_handles_zero_lookup_and_worker_counts_without_panicking() {
        let snapshot = AcquisitionSnapshot {
            age_ms: 1,
            header_after_ms: None,
            seq: 0,
            have_header: false,
            have_state: false,
            have_transactions: false,
            timeouts: 0,
            packets: 0,
            useful_packets: 0,
            useful_nodes: 0,
            state_packets: 0,
            state_useful_nodes: 0,
            state_duplicate_nodes: 0,
            malformed_packets: 0,
            state_scan_runs: 0,
            state_missing_nodes: 0,
            tx_missing_nodes: 0,
            state_scan_us: 0,
            state_scan_branch_steps: 0,
            state_scan_missing_nodes_recorded: 0,
            state_scan_positive_progress_slices: 0,
            state_scan_branch_budget_yields: 0,
            state_scan_deferred_read_budget_yields: 0,
            state_scan_deferred_read_resume_yields: 0,
            state_scan_missing_node_limit_yields: 0,
            state_scan_completed_slices: 0,
            state_scan_last_yield: "none",
            state_scan_last_branch_steps: 0,
            state_scan_last_deferred_reads: 0,
            state_scan_last_deferred_resumes: 0,
            state_scan_last_missing_nodes: 0,
            state_scan_branches_seen: 0,
            state_scan_duplicate_missing_hashes: 0,
            state_scan_full_below_hits: 0,
            state_scan_loaded_or_cached_children: 0,
            state_scan_pending_reads: 0,
            state_scan_read_slot_full: 0,
            state_scan_read_admission_accepted: 0,
            state_scan_read_admission_deferred: 0,
            state_scan_read_admission_attached: 0,
            state_scan_read_broker_rejected: 0,
            state_scan_max_pending_reads: 0,
            state_scan_pending_hits: 0,
            state_scan_pending_misses: 0,
            state_scan_deferred_resumes: 0,
            state_scan_yields: 0,
            state_scan_continuations: 0,
            timeout_dispatches: 0,
            state_scan_max_buffered_packets: 0,
            data_drain_runs: 0,
            data_drain_us: 0,
            data_drain_max_us: 0,
            data_drain_max_packets: 0,
            tx_scan_us: 0,
            worker_jobs: 0,
            worker_queue_wait_us: 7,
            node_store_fetch_hits: 0,
            node_store_fetch_misses: 0,
            tracked_peers: 0,
            buffered_packets: 0,
            buffered_packets_high_water: 0,
            mailbox_token: "idle",
            scan_continuation_pending: false,
            pending_admitted_timeouts: 0,
        };

        let JsonValue::Object(values) = acquisition_snapshot_json(
            Uint256::from_u64(1),
            0,
            AcquireReason::Consensus,
            0,
            false,
            false,
            snapshot,
        ) else {
            panic!("acquisition diagnostics must be an object");
        };

        assert_eq!(values.get("state_packets"), Some(&JsonValue::Unsigned(0)));
        assert_eq!(
            values.get("state_useful_nodes"),
            Some(&JsonValue::Unsigned(0))
        );
        assert_eq!(
            values.get("state_duplicate_nodes"),
            Some(&JsonValue::Unsigned(0))
        );
        assert_eq!(values.get("state_scan_runs"), Some(&JsonValue::Unsigned(0)));
        assert_eq!(
            values.get("state_scan_pending_reads"),
            Some(&JsonValue::Unsigned(0))
        );
        assert_eq!(values.get("data_drain_runs"), Some(&JsonValue::Unsigned(0)));
        assert_eq!(
            values.get("node_store_lookup_hit_rate_ppm"),
            Some(&JsonValue::Null)
        );
        assert_eq!(
            values.get("average_worker_queue_wait_us"),
            Some(&JsonValue::Null)
        );
    }
}
