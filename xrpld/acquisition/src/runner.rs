//! The serialized coordinator runner (M3: typed events, reads, writes, timers).
//!
//! [`CoordinatorRunner`] is the production authority of the acquisition domain.
//! It owns [`CoordinatorState`] on one serialized strand/thread, consumes typed
//! [`AcquisitionEvent`]s, mutates coordinator state, and returns the typed
//! [`AcquisitionEffect`]s for adapters to execute *after* the call returns.
//!
//! Concurrency and ownership rules this runner enforces:
//!
//! * No callback is ever invoked while handling an event: `handle_event` only
//!   reads its owned state and returns a value list. An adapter can therefore
//!   never hold a resource lock while coordinator logic runs.
//! * The runner holds no port references; effects are executed by the caller
//!   after state mutation, and adapters return typed completion events.
//! * A completion may mutate state only when its [`SessionRef`] matches a live
//!   session. Timers are matched exactly against the operation that armed them;
//!   reads/writes/fences/handoffs gain exact in-flight operation matching in M4
//!   when the runner dispatches them.
//! * Cancellation invalidates a session immediately; every late event for it is
//!   stale and ignored (counted for observability).
//! * After [`AcquisitionEvent::Shutdown`] the runner produces no further
//!   effects and every later event is stale.
//!
//! Session lifecycle (tree plan, mailbox, persistence intent) migrates into the
//! coordinator in M4; here the runner owns the typed boundary, service phase,
//! session identity, admission accounting, and staleness/cancellation rules.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::Arc;
use std::time::Duration;

use ledger::Ledger;

use basics::base_uint::Uint256;

use crate::effect::AcquisitionEffect;
use crate::event::{AcquisitionEvent, ConsensusTarget};
use crate::handoff::{DurableHandoffAcknowledgement, DurableLedger};
use crate::id::{DurableHandoffId, IdCounter, PeerId, RunEpoch, StoreGeneration};
use crate::identity::{OperationKind, OperationRef, SessionRef};
use crate::ingress::{
    ADMISSION_BYTE_LIMIT, ADMISSION_PACKET_LIMIT, AdmissionBudget, AdmittedLedgerPacket,
};
use crate::io::{DurabilityCompletion, ReadCompletion, ReadPriority, WriteCompletion};
use crate::peer::{
    LedgerDataRequest, LedgerNodeRequest, PeerAvailabilitySnapshot, PeerRequest,
    PeerTargetCapability,
};
use crate::phase::{SyncPhase, TransitionFact};
use crate::plan::{
    MAX_TIMEOUT_REPROBES, NetworkLane, NullPlanSeed, PlanDurabilityOutcome, PlanNetworkNeed,
    PlanReadOutcome, PlanSeed, PlanTimeout, PlanTurn, PlanWriteOutcome, SessionPlan, TurnContext,
};
use crate::session::{CancelReason, FailureReason, SessionPhase, session_phase_transition};
use crate::target::{AcquireReason, LedgerIdentity, LedgerTarget};
use crate::timer::{TimerKind, TimerRequest};

/// Small fixed delay for one durable-handoff delivery retry. The timer is
/// deliberately coordinator-owned and rearmed only after a later rejection;
/// it avoids immediate retry loops while keeping failed delivery responsive.
pub const HANDOFF_RETRY_DELAY: Duration = Duration::from_millis(100);

/// rippled `InboundLedger::addPeers` begins acquisition through this many
/// scored peers (`kPeerCountStart` in `InboundLedger.cpp`). Keep the
/// coordinator's peer policy at that protocol boundary without reintroducing
/// a second peer-set lifecycle owner.
const INITIAL_PEER_REQUEST_FANOUT: usize = 5;
/// rippled `InboundLedger::addPeers` adds this many scored peers after a
/// no-progress timeout (`kPeerCountAdd`).
const TIMEOUT_PEER_ESCALATION: usize = 3;
/// An acquisition has at most the initial rippled peer fanout plus one
/// `kPeerCountAdd` window for each bounded no-progress timeout. This is a
/// selected-peer window, not an unbounded history of every responder.
const MAX_SELECTED_PEERS: usize = INITIAL_PEER_REQUEST_FANOUT
    + TIMEOUT_PEER_ESCALATION * crate::plan::DEFAULT_MAX_ACQUIRE_TIMEOUTS as usize;
/// rippled switches to `TMGetObjectByHash` only after more than four
/// no-progress timeouts (`kLedgerBecomeAggressiveThreshold`).
const AGGRESSIVE_TIMEOUT_THRESHOLD: u32 = 4;
/// rippled's `InboundLedgers::sweep` removes a per-hash acquisition one minute
/// after its constructor/update touch, even if it is still active.
const SESSION_IDLE_MINIMUM: Duration = Duration::from_secs(60);
/// `JtLedgerData` runs at most three jobs concurrently in rippled. Quaxar uses
/// one serialized continuation per session, so one global three-owner pool is
/// the conservative async analogue for initial and triggered local scans.
const MAX_LOCAL_SCAN_OWNERS: usize = 3;
const MAX_PLAIN_CONSENSUS_SCAN_BURST: usize = 2;
const TERMINAL_RETENTION: Duration = Duration::from_secs(60);
/// rippled request batch limits from
/// `../rippled/src/xrpld/app/ledger/detail/InboundLedger.cpp`:
/// `kReqNodesReply` for a response-triggered request and `kReqNodes` for
/// blind/local/timeout work.
const REPLY_NODE_REQUEST_BATCH: usize = 128;
const BLIND_NODE_REQUEST_BATCH: usize = 12;
/// Bounded timeout request batch (`kReqNodes`), shared with the plan's local
/// reprobe batch so one timeout interval covers one exact rotating frontier.
const TIMEOUT_FRONTIER_REQUEST_LIMIT: usize = MAX_TIMEOUT_REPROBES;

/// One coordinator-wide credit pool prevents independent session timers from
/// recreating the outbound request storm. These are policy limits, not wire
/// limits: `REPLY_NODE_REQUEST_BATCH` remains 128 and blind/timeout requests
/// remain 12 as required by rippled `InboundLedger::filterNodes`.
const MAX_OUTBOUND_REQUESTS_GLOBAL: usize = 256;
const MAX_OUTBOUND_REQUESTS_PER_PEER: usize = 64;
const MAX_OUTBOUND_REQUESTS_PER_SESSION: usize = 64;
const MAX_QUEUED_REQUEST_INTENTS: usize = 512;
/// Peerless acquisition demand is retained in two explicit classes: the
/// latest preferred-consensus target and the latest ordinary/cache target.
/// This mirrors the bounded app-side pending-origin policy.
const MAX_DEFERRED_PEERLESS_ACQUIRES: usize = 2;

/// Exact outbound work retained until the common emitter obtains a credit.
/// This intentionally has no `OperationRef`: only the coordinator-owned
/// emitter mints an operation identity at the instant an effect is emitted.
/// Thus a queued normal frontier batch remains exact work rather than a
/// prematurely dispatched request with an unbounded outstanding lifetime.
#[derive(Debug, Clone, PartialEq, Eq)]
struct RequestIntent {
    session: SessionRef,
    peer: PeerId,
    request: LedgerDataRequest,
}

/// Resource policy owned by the serialized coordinator, not by the overlay.
/// The queue retains pending work while the counters represent requests that
/// were actually emitted. Credits are released conservatively only when an
/// acquire timeout expires, connectivity is lost, or a session terminalizes.
#[derive(Debug, Default)]
struct OutboundRequestAdmission {
    intents: VecDeque<RequestIntent>,
    outstanding: BTreeMap<OperationRef, PeerId>,
    outstanding_by_peer: BTreeMap<PeerId, usize>,
    outstanding_by_session: BTreeMap<SessionRef, usize>,
}

/// Coordinator-owned budgets for the acquisition domain.
///
/// `Default` reproduces the existing per-ledger mailbox semantics (`128`
/// packets, `4 MiB`) as the admission budget and bounds live sessions so
/// history demand cannot consume unbounded coordinator state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BudgetState {
    max_sessions: usize,
    admission: AdmissionBudget,
    acquire_timeout: Duration,
}

impl BudgetState {
    /// Builds an explicit budget.
    pub const fn new(
        max_sessions: usize,
        admission: AdmissionBudget,
        acquire_timeout: Duration,
    ) -> Self {
        Self {
            max_sessions,
            admission,
            acquire_timeout,
        }
    }

    /// The maximum concurrently live sessions.
    pub const fn max_sessions(self) -> usize {
        self.max_sessions
    }

    /// The per-session admission budget (defaults to the existing mailbox
    /// limits of `128` packets / `4 MiB`).
    pub const fn admission(self) -> AdmissionBudget {
        self.admission
    }

    /// The acquisition attempt deadline before a session fails.
    pub const fn acquire_timeout(self) -> Duration {
        self.acquire_timeout
    }
}

impl Default for BudgetState {
    fn default() -> Self {
        Self::new(
            16,
            AdmissionBudget::new(ADMISSION_PACKET_LIMIT, ADMISSION_BYTE_LIMIT),
            // rippled's InboundLedger timer runs every three seconds; the
            // seventh no-progress interval terminalizes the acquisition.
            Duration::from_secs(3),
        )
    }
}

/// All mutable acquisition-domain state owned by the coordinator on one owner
/// task, as documented in `docs/ARCHITECTURE.md`.
#[derive(Debug)]
pub struct CoordinatorState {
    phase: SyncPhase,
    /// Whether the configured consensus peer threshold is currently met.
    /// Transport connectivity remains independently usable for acquisition
    /// while this gate prevents it from publishing Connected.
    consensus_quorum_available: bool,
    run_epoch: RunEpoch,
    sessions: BTreeMap<SessionRef, CoordinatorSession>,
    budgets: BudgetState,
    peer_view: PeerAvailabilitySnapshot,
    target_peer_capabilities: BTreeMap<LedgerTarget, Vec<PeerTargetCapability>>,
    /// At most one latest preferred-consensus demand plus one latest ordinary
    /// demand deferred only because no usable peer capability existed. They
    /// are replayed by this same owner on the next `PeerCapabilityAvailable`
    /// fact; there is never an adapter-side retry queue.
    deferred_acquires: BTreeMap<LedgerTarget, (AcquireReason, bool, bool)>,
    /// Latest preferred-LCL demand observed from consensus. This is a policy
    /// and promotion candidate only; scheduling remains bound to the exact
    /// latched recovery owner until its natural reconciliation boundary.
    latest_consensus_target: Option<LedgerTarget>,
    /// Latest hash requested by `RCLValidationsAdaptor::acquire`. It receives
    /// outbound priority without becoming preferred-LCL or operating-mode
    /// policy state.
    latest_validation_target: Option<LedgerTarget>,
    /// Exact live owner satisfying `latest_validation_target`, retained only
    /// for validation-demand lifecycle accounting. It is deliberately not an
    /// outbound or recovery scheduling priority.
    latest_validation_session: Option<SessionRef>,
    /// Exact phase-neutral validation-recovery target. Unlike
    /// `latest_validation_target`, this target is stable across moving
    /// accepted-boundary observations until its session reaches a terminal
    /// boundary.
    validation_recovery_target: Option<LedgerTarget>,
    /// Exact live owner for `validation_recovery_target`, when one has been
    /// admitted. The target may exist without a session while peerless or at
    /// capacity.
    validation_recovery_session: Option<SessionRef>,
    /// Newest still-observed candidate waiting behind the exact owner.
    validation_recovery_candidate: Option<LedgerTarget>,
    /// Stable preferred-LCL target currently being recovered. It is latched
    /// before a matching session necessarily exists, so a divergence fact and
    /// the later missing-ledger acquisition cannot be separated by a moving
    /// consensus or validation observation.
    recovery_anchor_target: Option<LedgerTarget>,
    /// Exact owner of the consensus LCL currently being recovered. This is
    /// the coordinator equivalent of rippled's `acquiringLedger_`: newer
    /// consensus and validation observations may update policy candidates,
    /// but cannot preempt this owner while it remains viable. Operating-mode
    /// transitions are deliberately independent, so a transient
    /// Full/Tracking/Connected publication does not lose the recovery latch.
    recovery_anchor_session: Option<SessionRef>,
    /// Latest preferred-LCL demand that could not obtain capacity after
    /// cancellable Generic/History work was considered. It is coordinator
    /// state, not a registry retry or consensus callback latch.
    deferred_consensus_acquire: Option<LedgerTarget>,
    storage_generation: StoreGeneration,
    /// Latest serialized local LCL fact. A Full identity is refreshed only by
    /// a fresh publication of this exact ledger.
    last_installed_lcl: Option<LedgerIdentity>,
    local_scan_owners: BTreeSet<SessionRef>,
    local_scan_waiters: VecDeque<SessionRef>,
    plain_consensus_scan_burst: usize,
    /// Sweep-eligible owners that were executing the async equivalent of a
    /// synchronous rippled ledger-data job when the registry sweep ran. The
    /// registry reference may disappear, but its graph survives until that
    /// scan reaches a network boundary.
    swept_local_scan_owners: BTreeSet<SessionRef>,
    /// The sole outbound-acquisition admission boundary. Every Base, normal
    /// frontier, timeout, Base retry, and recovery request enters here before
    /// the common emitter can construct a `PeerRequest`.
    outbound: OutboundRequestAdmission,
    ids: IdCounter,
}

/// The coordinator-owned lifecycle of one session.
///
/// Owns the [`SessionPlan`] (mailbox, tree engine, read admission, persistence
/// intent, timeout budget, cancellation) plus the pending timer used for exact
/// `TimerFired` matching. No other component may mutate this state.
#[derive(Debug)]
pub struct CoordinatorSession {
    target: LedgerTarget,
    reason: AcquireReason,
    phase: SessionPhase,
    plan: SessionPlan,
    sent_peers: BTreeSet<PeerId>,
    /// True only while this active session is admitted to issue peer work.
    /// Peer loss pauses it immediately; bounded recovery grants reactivate at
    /// most one waiting session per currently usable peer.
    network_admitted: bool,
    pending_timer: Option<(TimerKind, OperationRef)>,
    /// Independent from the three-second acquisition timer: repeated same-hash
    /// demand replaces this identity just like `InboundLedger::update::touch`.
    pending_expiry_timer: Option<OperationRef>,
    expiry_sweep_eligible: bool,
    pending_header_read: Option<OperationRef>,
    pending_handoff: Option<DurableHandoffId>,
    // The durable ledger is retained for handoff retry: `plan.durable_ledger()`
    // yields the payload exactly once, and any timer-driven re-publish of the
    // pending handoff id carries the same payload for recipient deduplication.
    durable: Option<Arc<Ledger>>,
}

impl CoordinatorSession {
    fn new(target: LedgerTarget, reason: AcquireReason, admission: AdmissionBudget) -> Self {
        Self {
            target,
            reason,
            phase: SessionPhase::Active,
            plan: SessionPlan::new(admission),
            sent_peers: BTreeSet::new(),
            // New target creation retains the existing initial fanout policy.
            // Scarce-peer admission applies only to recovery after a loss.
            network_admitted: true,
            pending_timer: None,
            pending_expiry_timer: None,
            expiry_sweep_eligible: false,
            pending_header_read: None,
            pending_handoff: None,
            durable: None,
        }
    }

    /// The target being acquired.
    pub const fn target(&self) -> LedgerTarget {
        self.target
    }

    /// Why the target is being acquired.
    pub const fn reason(&self) -> AcquireReason {
        self.reason
    }

    /// The session lifecycle phase.
    pub const fn phase(&self) -> &SessionPhase {
        &self.phase
    }

    /// The coordinator-owned session plan.
    pub const fn plan(&self) -> &SessionPlan {
        &self.plan
    }

    /// The currently accepted packet count (queued mailbox packets).
    pub fn packet_count(&self) -> u64 {
        self.plan.packet_count()
    }

    /// The currently accepted packet bytes (queued mailbox packets).
    pub fn packet_bytes(&self) -> u64 {
        self.plan.packet_bytes()
    }

    /// Bounded selected peers eligible for timeout resends. Reply-driven
    /// requests may use a responding peer once without expanding this window.
    pub fn sent_peers(&self) -> &BTreeSet<PeerId> {
        &self.sent_peers
    }

    /// The timer this session has armed and is waiting on, if any.
    pub const fn pending_timer(&self) -> Option<(TimerKind, OperationRef)> {
        self.pending_timer
    }

    /// The one-minute live-acquisition expiry currently armed for this hash.
    pub const fn pending_expiry_timer(&self) -> Option<OperationRef> {
        self.pending_expiry_timer
    }

    /// The durable handoff id this session is awaiting acknowledgement for,
    /// once its durability fence passed.
    pub const fn pending_handoff(&self) -> Option<DurableHandoffId> {
        self.pending_handoff
    }

    fn can_promote_unknown_sequence(&self, target: LedgerTarget) -> bool {
        // A known sequence strengthens the identity metadata of an active
        // hash-only acquisition; it does not change the session, its rooted
        // plan, or any in-flight operation. Once the Base packet has seeded
        // the plan, replacing this session would discard admitted work and
        // restart the same hash from scratch.
        (self.phase == SessionPhase::Active || self.phase == SessionPhase::Dormant)
            && self.target.hash() == target.hash()
            && self.target.sequence().is_none()
            && target.sequence().is_some()
    }

    fn promote_target(&mut self, target: LedgerTarget) {
        self.target = target;
    }

    /// Rippled performs all repeated 512-read deferred batches inside one
    /// synchronous `getMissingNodes` call while holding the InboundLedger
    /// mutex. Quaxar externalizes those reads, so timer events may interleave;
    /// this identifies the interval in which they must not consume network
    /// timeout/registry-expiry semantics or tear down the private tree graph.
    fn local_reconstruction_in_flight(&self) -> bool {
        self.pending_header_read.is_some()
            || self.plan.pending_read_count() != 0
            || self.plan.read_backlog_count() != 0
            || matches!(
                self.plan.persistence(),
                crate::plan::SessionPersistence::IncrementalWritePending { .. }
            )
    }
}

/// An immutable snapshot of runner-owned state for observability.
///
/// Admission-gate reservation counters live at ingress and are composed into
/// the adapter-level [`crate::CoordinatorSnapshot`]; this snapshot reports what
/// the runner owns.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunnerSessionSnapshot {
    session_id: u64,
    target_hash: String,
    target_sequence: Option<u32>,
    reason: AcquireReason,
    phase: &'static str,
    network_admitted: bool,
    local_scan: &'static str,
    peer_count: usize,
    plan_seeded: bool,
    plan_runs: u64,
    timeouts: u32,
    packet_count: u64,
    packet_bytes: u64,
    pending_reads: usize,
    read_backlog: usize,
    pending_network: usize,
    retained_network: usize,
    persistence: &'static str,
}

impl RunnerSessionSnapshot {
    pub const fn session_id(&self) -> u64 {
        self.session_id
    }
    pub fn target_hash(&self) -> &str {
        &self.target_hash
    }
    pub const fn target_sequence(&self) -> Option<u32> {
        self.target_sequence
    }
    pub const fn reason(&self) -> AcquireReason {
        self.reason
    }
    pub const fn phase(&self) -> &'static str {
        self.phase
    }
    pub const fn network_admitted(&self) -> bool {
        self.network_admitted
    }
    pub const fn local_scan(&self) -> &'static str {
        self.local_scan
    }
    pub const fn peer_count(&self) -> usize {
        self.peer_count
    }
    pub const fn plan_seeded(&self) -> bool {
        self.plan_seeded
    }
    pub const fn plan_runs(&self) -> u64 {
        self.plan_runs
    }
    pub const fn timeouts(&self) -> u32 {
        self.timeouts
    }
    pub const fn packet_count(&self) -> u64 {
        self.packet_count
    }
    pub const fn packet_bytes(&self) -> u64 {
        self.packet_bytes
    }
    pub const fn pending_reads(&self) -> usize {
        self.pending_reads
    }
    pub const fn read_backlog(&self) -> usize {
        self.read_backlog
    }
    pub const fn pending_network(&self) -> usize {
        self.pending_network
    }
    pub const fn retained_network(&self) -> usize {
        self.retained_network
    }
    pub const fn persistence(&self) -> &'static str {
        self.persistence
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunnerSnapshot {
    run_epoch: RunEpoch,
    phase: SyncPhase,
    session_count: usize,
    detached_sessions: usize,
    active_by_reason: BTreeMap<AcquireReason, usize>,
    session_details: Vec<RunnerSessionSnapshot>,
    storage_generation: StoreGeneration,
    peer_count: usize,
    local_scan_owners: usize,
    local_scan_waiters: usize,
    recovery_anchor_session: Option<SessionRef>,
    validation_recovery_target: Option<LedgerTarget>,
    validation_recovery_session: Option<SessionRef>,
    events_handled: u64,
    stale_events: u64,
    rejected_events: u64,
    sessions_started: u64,
    sessions_cancelled: u64,
    cancelled_by_reason: BTreeMap<CancelReason, u64>,
    failed_by_reason: BTreeMap<FailureReason, u64>,
    sessions_completed: u64,
    handoff_rejections: u64,
    peer_requests: u64,
    timers_armed: u64,
    packets_admitted: u64,
    packets_dropped: u64,
    plan_turns: u64,
    fetch_pack_advances: u64,
    shutdown: bool,
}

impl RunnerSnapshot {
    /// The coordinator run epoch.
    pub const fn run_epoch(&self) -> RunEpoch {
        self.run_epoch
    }

    /// The current service phase.
    pub const fn phase(&self) -> &SyncPhase {
        &self.phase
    }

    /// The number of tracked sessions.
    pub const fn session_count(&self) -> usize {
        self.session_count
    }

    /// Sessions detached from the hash registry by sweep but temporarily
    /// retained by an already queued/running local-scan continuation.
    pub const fn detached_sessions(&self) -> usize {
        self.detached_sessions
    }

    /// Live sessions grouped by acquisition reason.
    pub fn active_by_reason(&self) -> &BTreeMap<AcquireReason, usize> {
        &self.active_by_reason
    }

    /// Per-session acquisition state used to distinguish disk, network, and
    /// lifecycle stalls without enabling high-volume trace logging.
    pub fn session_details(&self) -> &[RunnerSessionSnapshot] {
        &self.session_details
    }

    /// The current NodeStore generation.
    pub const fn storage_generation(&self) -> StoreGeneration {
        self.storage_generation
    }

    /// The number of usable peers in the last connectivity snapshot.
    pub const fn peer_count(&self) -> usize {
        self.peer_count
    }

    pub const fn local_scan_owners(&self) -> usize {
        self.local_scan_owners
    }

    pub const fn local_scan_waiters(&self) -> usize {
        self.local_scan_waiters
    }

    /// Exact live session bound to the stable preferred-LCL recovery anchor.
    pub const fn recovery_anchor_session(&self) -> Option<SessionRef> {
        self.recovery_anchor_session
    }

    /// Exact phase-neutral validation-recovery target, including while it is
    /// waiting peerless or for capacity.
    pub const fn validation_recovery_target(&self) -> Option<LedgerTarget> {
        self.validation_recovery_target
    }

    /// Exact live session bound to the validation-recovery target.
    pub const fn validation_recovery_session(&self) -> Option<SessionRef> {
        self.validation_recovery_session
    }

    /// Events accepted by the runner (including rejected/stale ones).
    pub const fn events_handled(&self) -> u64 {
        self.events_handled
    }

    /// Stale events ignored after cancellation, replacement, or shutdown.
    pub const fn stale_events(&self) -> u64 {
        self.stale_events
    }

    /// Events rejected for a policy reason (no peers, phase rules, capacity).
    pub const fn rejected_events(&self) -> u64 {
        self.rejected_events
    }

    /// Sessions started.
    pub const fn sessions_started(&self) -> u64 {
        self.sessions_started
    }

    /// Sessions cancelled.
    pub const fn sessions_cancelled(&self) -> u64 {
        self.sessions_cancelled
    }

    /// Terminal cancellations grouped by their exact coordinator-owned reason.
    pub fn cancelled_by_reason(&self) -> &BTreeMap<CancelReason, u64> {
        &self.cancelled_by_reason
    }

    /// Terminal failures grouped by their exact coordinator-owned reason.
    pub fn failed_by_reason(&self) -> &BTreeMap<FailureReason, u64> {
        &self.failed_by_reason
    }

    /// Sessions that reached `Complete` after a durable handoff ack.
    pub const fn sessions_completed(&self) -> u64 {
        self.sessions_completed
    }

    /// Durable handoff deliveries rejected by the adapter (channel full or
    /// disconnected); each accepted rejection arms one exact retry timer for
    /// the same id. Duplicate rejections while armed are stale.
    pub const fn handoff_rejections(&self) -> u64 {
        self.handoff_rejections
    }

    /// Peer requests emitted.
    pub const fn peer_requests(&self) -> u64 {
        self.peer_requests
    }

    /// Timers armed.
    pub const fn timers_armed(&self) -> u64 {
        self.timers_armed
    }

    /// Packets routed to sessions.
    pub const fn packets_admitted(&self) -> u64 {
        self.packets_admitted
    }

    /// Packets dropped by the defensive session mailbox bounds.
    pub const fn packets_dropped(&self) -> u64 {
        self.packets_dropped
    }

    /// Bounded tree-plan turns executed across live sessions.
    pub const fn plan_turns(&self) -> u64 {
        self.plan_turns
    }

    /// Turns run in response to a fetch-pack availability fact.
    pub const fn fetch_pack_advances(&self) -> u64 {
        self.fetch_pack_advances
    }

    /// True after a shutdown event was handled.
    pub const fn shutdown(&self) -> bool {
        self.shutdown
    }
}

/// Counter state for runner observability.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct RunnerStats {
    events_handled: u64,
    stale_events: u64,
    rejected_events: u64,
    sessions_started: u64,
    sessions_cancelled: u64,
    cancelled_by_reason: BTreeMap<CancelReason, u64>,
    failed_by_reason: BTreeMap<FailureReason, u64>,
    sessions_completed: u64,
    handoff_rejections: u64,
    peer_requests: u64,
    timers_armed: u64,
    packets_admitted: u64,
    packets_dropped: u64,
    plan_turns: u64,
    fetch_pack_advances: u64,
}

/// The serialized coordinator event loop.
#[derive(Debug)]
pub struct CoordinatorRunner {
    state: CoordinatorState,
    stats: RunnerStats,
    shutdown: bool,
    /// One-shot engine construction port. It runs outside coordinator state
    /// mutation and returns a uniquely owned engine or nothing.
    plan_seed: Box<dyn PlanSeed + Send + Sync>,
}

impl CoordinatorRunner {
    /// A runner with default budgets for a run epoch.
    pub fn new(run_epoch: RunEpoch) -> Self {
        Self::with_budget(run_epoch, BudgetState::default())
    }

    /// A runner seeded into an exact phase with a usable peer, for
    /// deterministic transition tests.
    #[cfg(test)]
    pub(crate) fn with_phase(run_epoch: RunEpoch, phase: SyncPhase) -> Self {
        let mut runner = Self::with_budget(run_epoch, BudgetState::default());
        runner.state.phase = phase;
        runner.state.peer_view = PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]);
        runner
    }

    /// A runner with explicit budgets.
    pub fn with_budget(run_epoch: RunEpoch, budgets: BudgetState) -> Self {
        Self::with_plan_seed(run_epoch, budgets, Box::new(NullPlanSeed))
    }

    /// A runner with explicit budgets and a plan seed. The seed builds a rooted
    /// engine from the first Base/header packet; with `NullPlanSeed` packets
    /// stay in the session mailbox and the session waits on its timer.
    pub fn with_plan_seed(
        run_epoch: RunEpoch,
        budgets: BudgetState,
        plan_seed: Box<dyn PlanSeed + Send + Sync>,
    ) -> Self {
        Self {
            state: CoordinatorState {
                phase: SyncPhase::Disconnected,
                consensus_quorum_available: true,
                run_epoch,
                sessions: BTreeMap::new(),
                budgets,
                peer_view: PeerAvailabilitySnapshot::new(vec![]),
                target_peer_capabilities: BTreeMap::new(),
                deferred_acquires: BTreeMap::new(),
                latest_consensus_target: None,
                latest_validation_target: None,
                latest_validation_session: None,
                validation_recovery_target: None,
                validation_recovery_session: None,
                validation_recovery_candidate: None,
                recovery_anchor_target: None,
                recovery_anchor_session: None,
                deferred_consensus_acquire: None,
                storage_generation: StoreGeneration::new(1),
                last_installed_lcl: None,
                local_scan_owners: BTreeSet::new(),
                local_scan_waiters: VecDeque::new(),
                plain_consensus_scan_burst: 0,
                swept_local_scan_owners: BTreeSet::new(),
                outbound: OutboundRequestAdmission::default(),
                ids: IdCounter::new(),
            },
            stats: RunnerStats::default(),
            shutdown: false,
            plan_seed,
        }
    }

    /// Handles one typed event and returns the effects adapters must execute
    /// after this call returns. Never invokes a port or callback.
    pub fn handle_event(&mut self, event: AcquisitionEvent) -> Vec<AcquisitionEffect> {
        if self.shutdown {
            // After shutdown the coordinator produces no effects; every later
            // event is stale.
            self.stats.stale_events += 1;
            return Vec::new();
        }
        let mut effects = match event {
            AcquisitionEvent::Shutdown => self.on_shutdown(),
            AcquisitionEvent::StartupMode { phase } => self.on_startup_mode(phase),
            AcquisitionEvent::Connectivity(snapshot) => self.on_connectivity(snapshot, false),
            AcquisitionEvent::TransportConnectivity(snapshot) => {
                self.on_transport_connectivity(snapshot)
            }
            AcquisitionEvent::ConsensusQuorumLost => self.on_consensus_quorum_lost(),
            AcquisitionEvent::ConsensusQuorumAvailable => self.on_consensus_quorum_available(),
            AcquisitionEvent::AcquireRequested { target, reason } => {
                self.on_acquire(target, reason, false, false)
            }
            AcquisitionEvent::ValidationTarget(target) => self.on_validation_target(target),
            AcquisitionEvent::ValidationRecoveryTarget(target) => {
                self.on_validation_recovery_target(target)
            }
            AcquisitionEvent::ConsensusTarget(target) => self.on_consensus(target),
            AcquisitionEvent::ConsensusViewChange => self.on_consensus_view_change(),
            AcquisitionEvent::PreferredLclDivergence { target } => {
                self.on_preferred_lcl_divergence(target)
            }
            AcquisitionEvent::PreferredLclReconciled { lcl } => {
                self.on_preferred_lcl_reconciled(lcl)
            }
            AcquisitionEvent::BlockedWithNoTarget => self.on_blocked_with_no_target(),
            AcquisitionEvent::PacketAdmitted(packet) => self.on_packet(packet),
            AcquisitionEvent::ReadCompleted(completion) => self.on_read(completion),
            AcquisitionEvent::WriteCompleted(completion) => self.on_write(completion),
            AcquisitionEvent::DurabilityFenced(completion) => self.on_durability(completion),
            AcquisitionEvent::DurableHandoffAcknowledged(ack) => self.on_handoff_ack(ack),
            AcquisitionEvent::DurableHandoffRejected {
                handoff, session, ..
            } => self.on_handoff_rejected(handoff, session),
            AcquisitionEvent::TimerFired { operation, timer } => self.on_timer(operation, timer),
            AcquisitionEvent::LclInstalled(identity) => self.on_lcl_installed(identity),
            AcquisitionEvent::PublicationCommitted { identity, fresh } => {
                self.on_publication(identity, fresh)
            }
            AcquisitionEvent::StoreRotated(generation) => self.on_store_rotated(generation),
            AcquisitionEvent::FetchPackAvailable => self.on_fetch_pack(),
            AcquisitionEvent::RegistrySweep => self.on_registry_sweep(),
            AcquisitionEvent::Heartbeat => self.on_heartbeat(),
        };
        self.reconcile_validation_owner();
        self.reconcile_validation_recovery_owner(&mut effects);
        // A terminal validation-recovery owner must clear or promote its exact
        // successor before ordinary preferred work observes the freed slot.
        // Replaying first can admit a moving consensus tip, then admit the
        // promoted recovery candidate in the same event.
        self.replay_deferred_consensus(&mut effects);
        self.reconcile_recovery_anchor();
        self.enforce_recovery_anchor_phase(&mut effects);
        self.promote_latest_viable_syncing_anchor(&mut effects);
        // All peer sends leave through one post-mutation emitter. This ensures
        // an adapter never sees a request before the owner recorded its
        // credits, and makes the queue/credit policy common to every source.
        if !self.shutdown {
            effects.extend(self.emit_admitted_requests());
        }
        self.stats.events_handled += 1;
        effects
    }

    /// Applies one drained NodeStore completion wave behind the same barrier
    /// used by rippled's `gmnProcessDeferredReads`: every exact operation is
    /// settled first, then each affected session continuation resumes once.
    pub fn handle_read_batch(
        &mut self,
        completions: Vec<ReadCompletion>,
    ) -> Vec<AcquisitionEffect> {
        if self.shutdown {
            self.stats.stale_events += completions.len() as u64;
            return Vec::new();
        }
        let count = completions.len() as u64;
        let mut effects = self.on_read_batch(completions);
        self.reconcile_validation_owner();
        self.reconcile_validation_recovery_owner(&mut effects);
        self.replay_deferred_consensus(&mut effects);
        self.reconcile_recovery_anchor();
        self.enforce_recovery_anchor_phase(&mut effects);
        self.promote_latest_viable_syncing_anchor(&mut effects);
        effects.extend(self.emit_admitted_requests());
        self.stats.events_handled += count;
        effects
    }

    /// True only when the coordinator retained the latest capacity-deferred
    /// preferred-LCL demand. Adapters use this disposition to retain the
    /// session-origin binding; they never become a second retry owner.
    pub fn has_deferred_consensus_target(&self, target: LedgerTarget) -> bool {
        self.state.deferred_consensus_acquire == Some(target)
    }

    /// Newest trusted-validation target supplied by `GetConsL2`. Ordinary
    /// Generic acquisitions must never mutate this phase-neutral owner hint.
    pub const fn latest_validation_target(&self) -> Option<LedgerTarget> {
        self.state.latest_validation_target
    }

    /// True when `target` is the exact phase-neutral validation-recovery latch,
    /// including while it waits peerless or for a bounded session slot.
    pub fn has_validation_recovery_target(&self, target: LedgerTarget) -> bool {
        self.state
            .validation_recovery_target
            .is_some_and(|anchor| anchor.hash() == target.hash())
    }

    pub const fn validation_recovery_target(&self) -> Option<LedgerTarget> {
        self.state.validation_recovery_target
    }

    pub const fn recovery_anchor_session(&self) -> Option<SessionRef> {
        self.state.recovery_anchor_session
    }

    pub const fn validation_recovery_session(&self) -> Option<SessionRef> {
        self.state.validation_recovery_session
    }

    /// True only when the exact validation-recovery latch has not yet bound a
    /// live session. App provenance remains pending only for this case.
    pub fn has_unbound_validation_recovery_target(&self, target: LedgerTarget) -> bool {
        self.has_validation_recovery_target(target)
            && self.state.validation_recovery_session.is_none()
    }

    pub fn has_validation_recovery_candidate(&self, target: LedgerTarget) -> bool {
        self.state
            .validation_recovery_candidate
            .is_some_and(|candidate| candidate.hash() == target.hash())
    }

    pub const fn validation_recovery_candidate(&self) -> Option<LedgerTarget> {
        self.state.validation_recovery_candidate
    }

    /// True when a same-hash live owner still needs its app-side origin to
    /// construct the one-shot plan engine.
    pub fn retains_session_origin_for_hash(&self, hash: Uint256) -> bool {
        self.state.sessions.values().any(|session| {
            !session.phase.is_terminal()
                && session.target.hash() == hash
                && session.plan.engine().is_none()
        }) || self
            .state
            .deferred_acquires
            .keys()
            .any(|target| target.hash() == hash)
            || self
                .state
                .deferred_consensus_acquire
                .is_some_and(|target| target.hash() == hash)
            || (self.state.recovery_anchor_session.is_none()
                && self
                    .state
                    .recovery_anchor_target
                    .is_some_and(|target| target.hash() == hash))
            || (self.state.validation_recovery_session.is_none()
                && self
                    .state
                    .validation_recovery_target
                    .is_some_and(|target| target.hash() == hash))
            || self
                .state
                .validation_recovery_candidate
                .is_some_and(|target| target.hash() == hash)
    }

    /// Retain and replay the latest consensus target only when a session slot
    /// is actually free. This is invoked after every fact on the serialized
    /// owner; no registry, adapter, or consensus callback owns a retry loop.
    fn replay_deferred_consensus(&mut self, effects: &mut Vec<AcquisitionEffect>) {
        if self.shutdown
            || !self.state.peer_view.has_usable_peer_capability()
            || self
                .state
                .sessions
                .iter()
                .filter(|(session, state)| self.counts_toward_live_capacity(**session, state))
                .count()
                >= self.state.budgets.max_sessions
        {
            return;
        }
        let Some(target) = self.state.deferred_consensus_acquire.take() else {
            return;
        };
        self.state.latest_consensus_target = Some(target);
        effects.extend(self.on_acquire(target, AcquireReason::Consensus, true, false));
    }

    /// Keep a recoverable Syncing anchor stable while its exact owner remains
    /// live or retained. Once that owner is terminal, expired, cancelled, or
    /// could not be admitted, promote the latest consensus target that still
    /// has viable coordinator-owned work. This is deliberately an event-boundary
    /// reconciliation: cancellation cascades such as store rotation finish
    /// before a replacement is selected, so they cannot publish a transient
    /// anchor whose session is about to be cancelled in the same event.
    fn promote_latest_viable_syncing_anchor(&mut self, effects: &mut Vec<AcquisitionEffect>) {
        // The explicit recovery latch owns promotion whenever present. Its
        // exact session reconciliation above advances the target only at a
        // terminal/invalidation boundary; the moving latest candidate must
        // not bypass that policy through phase-only viability checks.
        if self.state.recovery_anchor_target.is_some() {
            return;
        }
        let SyncPhase::Syncing { target: anchor } = self.state.phase else {
            return;
        };
        if self.has_viable_target_work(anchor) {
            return;
        }
        let Some(latest) = self.state.latest_consensus_target else {
            return;
        };
        if latest.hash() == anchor.hash() || !self.has_viable_target_work(latest) {
            return;
        }
        let next = SyncPhase::Syncing { target: latest };
        self.state.phase = next;
        effects.push(AcquisitionEffect::SetServicePhase(next));
        tracing::info!(
            target: "acquisition_trace",
            event = "syncing_anchor_promoted",
            old_target_hash = %anchor.hash(),
            old_target_seq = ?anchor.sequence(),
            target_hash = %latest.hash(),
            target_seq = ?latest.sequence(),
            "acquisition trace: terminal or inadmissible recovery anchor promoted to latest viable consensus target"
        );
    }

    fn has_viable_target_work(&self, target: LedgerTarget) -> bool {
        self.state
            .sessions
            .values()
            .any(|session| !session.phase.is_terminal() && session.target.hash() == target.hash())
            || self
                .state
                .deferred_consensus_acquire
                .is_some_and(|deferred| deferred.hash() == target.hash())
            || self
                .state
                .deferred_acquires
                .keys()
                .any(|deferred| deferred.hash() == target.hash())
    }

    fn reconcile_validation_owner(&mut self) {
        let Some(target) = self.state.latest_validation_target else {
            self.state.latest_validation_session = None;
            return;
        };
        self.state.latest_validation_session = self
            .state
            .sessions
            .iter()
            .filter(|(_, session)| {
                !session.phase.is_terminal() && session.target.hash() == target.hash()
            })
            .max_by_key(|(session, _)| session.session_id())
            .map(|(session, _)| *session);
        if self.state.latest_validation_session.is_none()
            && !self
                .state
                .deferred_acquires
                .keys()
                .any(|deferred| deferred.hash() == target.hash())
        {
            self.state.latest_validation_target = None;
        }
    }

    /// Binds and advances the phase-neutral validation-recovery latch. A
    /// missing session is a retained demand (peerless or capacity constrained),
    /// not a terminal boundary. Once an exact bound session terminalizes, only
    /// the newest candidate observed while it was live may become the next
    /// owner.
    fn reconcile_validation_recovery_owner(&mut self, effects: &mut Vec<AcquisitionEffect>) {
        if self.shutdown {
            return;
        }

        if let Some(owner) = self.state.validation_recovery_session {
            let owner_state = self.state.sessions.get(&owner);
            if owner_state.is_some_and(|state| !state.phase.is_terminal()) {
                return;
            }

            self.state.validation_recovery_session = None;
            self.state.validation_recovery_target = None;
            let Some(candidate) = self.state.validation_recovery_candidate.take() else {
                return;
            };
            self.state.validation_recovery_target = Some(candidate);
        }

        let Some(target) = self.state.validation_recovery_target else {
            return;
        };
        if let Some(owner) = self.viable_session_for_target(target) {
            self.state.validation_recovery_session = Some(owner);
            if let Some(state) = self.state.sessions.get(&owner)
                && target.sequence().is_none()
                && state.target.sequence().is_some()
            {
                self.state.validation_recovery_target = Some(state.target);
            }
            // Binding an already-existing session changes its scheduler rank.
            // If every scan slot is occupied (especially by owners waiting on
            // incremental write completion), no unrelated event is guaranteed
            // to call `ensure_local_scan_permit` for this newly-exact waiter.
            // Kick it now so the normal strict-rank boundary logic can reclaim
            // an idle lower-ranked slot without overlapping physical writes.
            if self.state.local_scan_waiters.contains(&owner) {
                self.run_plan_turn(owner, None, effects);
            }
            return;
        }

        // The exact target itself is the durable retry authority. Peerless and
        // capacity rejection therefore cannot lose it or substitute a moving
        // validation tip.
        effects.extend(self.on_acquire(target, AcquireReason::Consensus, false, true));
        self.state.validation_recovery_session = self.viable_session_for_target(target);
    }

    /// Latch one exact consensus recovery owner until it naturally finishes
    /// or is invalidated. `latest_consensus_target` is only the candidate to
    /// use after that boundary; it is never itself scheduling authority.
    /// This mirrors rippled's `RCLConsensus::Adaptor::acquiringLedger_`, whose
    /// hash remains the active acquisition until the requested ledger changes
    /// at a real reconciliation boundary.
    fn reconcile_recovery_anchor(&mut self) {
        if let Some(anchor) = self.state.recovery_anchor_session {
            let anchor_state = self.state.sessions.get(&anchor);
            let live_target = anchor_state.and_then(|session| {
                (!session.phase.is_terminal()
                    && self
                        .state
                        .recovery_anchor_target
                        .is_some_and(|target| target.hash() == session.target.hash()))
                .then_some(session.target)
            });
            if let Some(live_target) = live_target {
                if self.state.recovery_anchor_target.is_some_and(|target| {
                    target.sequence().is_none() && live_target.sequence().is_some()
                }) {
                    self.state.recovery_anchor_target = Some(live_target);
                }
                return;
            }
            if anchor_state.is_some_and(|session| session.phase == SessionPhase::Complete) {
                // Durable handoff completion is not LCL adoption. Keep the
                // stable target authoritative until NetworkOps reports the
                // exact LclInstalled/PreferredLclReconciled boundary, but the
                // terminal session no longer participates in scheduling.
                self.state.recovery_anchor_session = None;
                return;
            }
            // An exact owner existed and reached a terminal/invalidation
            // boundary. Only now may the latest viable policy candidate be
            // promoted into the recovery latch.
            self.state.recovery_anchor_session = None;
            self.state.recovery_anchor_target = None;
            if let Some((target, session)) = self.state.latest_consensus_target.and_then(|target| {
                self.viable_session_for_target(target)
                    .map(|session| (target, session))
            }) {
                self.state.recovery_anchor_target = Some(target);
                self.state.recovery_anchor_session = Some(session);
            }
            return;
        }

        if let Some(target) = self.state.recovery_anchor_target {
            // PreferredLclDivergence can precede the matching acquisition.
            // Keep the target stable while waiting; absence is not failure.
            self.state.recovery_anchor_session = self.viable_session_for_target(target);
            return;
        }

        // With no existing or pending latch, latest consensus remains policy
        // metadata only. `observe_consensus_target(..., true)` or an explicit
        // divergence is the sole authority that starts recovery.
    }

    fn observe_consensus_target(&mut self, target: LedgerTarget, latch_if_empty: bool) {
        let selected = self
            .state
            .latest_consensus_target
            .filter(|current| {
                current.hash() == target.hash()
                    && current.sequence().is_some()
                    && target.sequence().is_none()
            })
            .unwrap_or(target);
        self.state.latest_consensus_target = Some(selected);
        if latch_if_empty && self.state.recovery_anchor_target.is_none() {
            self.state.recovery_anchor_target = Some(selected);
        }
    }

    fn enforce_recovery_anchor_phase(&mut self, effects: &mut Vec<AcquisitionEffect>) {
        let Some(target) = self.state.recovery_anchor_target else {
            return;
        };
        if self.shutdown
            || !self.state.peer_view.has_usable_peer_capability()
            || matches!(
                self.state.phase,
                SyncPhase::Disconnected | SyncPhase::Stopping
            )
        {
            return;
        }
        let next = SyncPhase::Syncing { target };
        if self.state.phase != next {
            self.state.phase = next;
            effects.push(AcquisitionEffect::SetServicePhase(next));
        }
    }

    fn viable_session_for_target(&self, target: LedgerTarget) -> Option<SessionRef> {
        self.state
            .sessions
            .iter()
            .filter(|(_, session)| {
                !session.phase.is_terminal() && session.target.hash() == target.hash()
            })
            // InboundLedgers has one owner per hash. If retained test state
            // contains more than one, preserve the oldest exact owner rather
            // than letting a moving observation win.
            .min_by_key(|(session, _)| session.session_id())
            .map(|(session, _)| *session)
    }

    /// The coordinator run epoch.
    pub const fn run_epoch(&self) -> RunEpoch {
        self.state.run_epoch
    }

    /// The current service phase.
    pub const fn phase(&self) -> &SyncPhase {
        &self.state.phase
    }

    /// The current NodeStore generation.
    pub const fn storage_generation(&self) -> StoreGeneration {
        self.state.storage_generation
    }

    /// The live session for the exact reference, if any.
    pub fn session(&self, session: SessionRef) -> Option<&CoordinatorSession> {
        self.state.sessions.get(&session)
    }

    /// Refresh target-specific overlay knowledge inside the serialized owner
    /// without running a second event/effect emission cycle.
    pub fn update_target_peer_capabilities(
        &mut self,
        target: LedgerTarget,
        peers: Vec<PeerTargetCapability>,
    ) {
        self.state.target_peer_capabilities.insert(target, peers);
    }

    pub fn active_targets(&self) -> Vec<LedgerTarget> {
        self.state
            .sessions
            .iter()
            .filter(|(session_ref, session)| {
                session.phase == SessionPhase::Active
                    && !self.state.swept_local_scan_owners.contains(session_ref)
            })
            .map(|(_, session)| session.target)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    /// Every packet-routable session reference, in target/session order.
    ///
    /// Adapters rebuild routing snapshots from this set so a session is routed
    /// exactly while it can accept packets. Dormant consensus sessions and
    /// sessions awaiting durable handoff acknowledgement are excluded: neither
    /// may reserve ingress capacity.
    pub fn live_sessions(&self) -> impl Iterator<Item = SessionRef> + '_ {
        self.state
            .sessions
            .iter()
            // A registry sweep removes rippled's hash lookup even while a
            // queued/running JobQueue lambda retains the object by shared_ptr.
            // Keep executing the private graph, but stop routing new packets
            // to that detached registry owner until a fresh demand touches it.
            .filter(|(session_ref, session)| {
                session.phase == SessionPhase::Active
                    && !self.state.swept_local_scan_owners.contains(session_ref)
            })
            .map(|(session_ref, _)| *session_ref)
    }

    /// Whether this retained session consumes one admission slot. A registry
    /// sweep detaches rippled's hash entry while an already queued/running job
    /// may still hold the acquisition object alive; that private continuation
    /// is neither new routable work nor a capacity-preemption candidate.
    fn counts_toward_live_capacity(&self, session: SessionRef, state: &CoordinatorSession) -> bool {
        !state.phase.is_terminal() && !self.state.swept_local_scan_owners.contains(&session)
    }

    /// Runner-owned observable state.
    pub fn snapshot(&self) -> RunnerSnapshot {
        let mut active_by_reason = BTreeMap::new();
        for (session_ref, session) in &self.state.sessions {
            if !session.phase.is_terminal()
                && session.phase != SessionPhase::Dormant
                && !self.state.swept_local_scan_owners.contains(session_ref)
            {
                *active_by_reason.entry(session.reason).or_insert(0usize) += 1;
            }
        }
        let session_details = self
            .state
            .sessions
            .iter()
            .map(|(session, state)| RunnerSessionSnapshot {
                session_id: session.session_id().get(),
                target_hash: session.target_hash().to_string(),
                target_sequence: state.target.sequence(),
                reason: state.reason,
                phase: state.phase.label(),
                network_admitted: state.network_admitted,
                local_scan: if self.state.swept_local_scan_owners.contains(session)
                    && self.state.local_scan_owners.contains(session)
                {
                    "detached_owner"
                } else if self.state.swept_local_scan_owners.contains(session)
                    && self.state.local_scan_waiters.contains(session)
                {
                    "detached_waiting"
                } else if self.state.local_scan_owners.contains(session) {
                    "owner"
                } else if self.state.local_scan_waiters.contains(session) {
                    "waiting"
                } else {
                    "idle"
                },
                peer_count: state.sent_peers.len(),
                plan_seeded: state.plan.engine().is_some(),
                plan_runs: state.plan.runs(),
                timeouts: state.plan.timeouts(),
                packet_count: state.plan.packet_count(),
                packet_bytes: state.plan.packet_bytes(),
                pending_reads: state.plan.pending_read_count(),
                read_backlog: state.plan.read_backlog_count(),
                pending_network: state.plan.pending_network().len(),
                retained_network: state.plan.retained_network().len(),
                persistence: state.plan.persistence().label(),
            })
            .collect();
        RunnerSnapshot {
            run_epoch: self.state.run_epoch,
            phase: self.state.phase,
            session_count: self.state.sessions.len(),
            detached_sessions: self.state.swept_local_scan_owners.len(),
            active_by_reason,
            session_details,
            storage_generation: self.state.storage_generation,
            peer_count: self.state.peer_view.peers().len(),
            local_scan_owners: self.state.local_scan_owners.len(),
            local_scan_waiters: self.state.local_scan_waiters.len(),
            recovery_anchor_session: self.state.recovery_anchor_session,
            validation_recovery_target: self.state.validation_recovery_target,
            validation_recovery_session: self.state.validation_recovery_session,
            events_handled: self.stats.events_handled,
            stale_events: self.stats.stale_events,
            rejected_events: self.stats.rejected_events,
            sessions_started: self.stats.sessions_started,
            sessions_cancelled: self.stats.sessions_cancelled,
            cancelled_by_reason: self.stats.cancelled_by_reason.clone(),
            failed_by_reason: self.stats.failed_by_reason.clone(),
            sessions_completed: self.stats.sessions_completed,
            handoff_rejections: self.stats.handoff_rejections,
            peer_requests: self.stats.peer_requests,
            timers_armed: self.stats.timers_armed,
            packets_admitted: self.stats.packets_admitted,
            packets_dropped: self.stats.packets_dropped,
            plan_turns: self.stats.plan_turns,
            fetch_pack_advances: self.stats.fetch_pack_advances,
            shutdown: self.shutdown,
        }
    }

    fn on_shutdown(&mut self) -> Vec<AcquisitionEffect> {
        let mut effects = Vec::new();
        if let Ok(next) = self.state.phase.apply(TransitionFact::Shutdown) {
            self.state.phase = next;
            effects.push(AcquisitionEffect::SetServicePhase(next));
        }
        self.cancel_all(CancelReason::Shutdown, &mut effects);
        self.shutdown = true;
        effects
    }

    /// Seeds the coordinator's initial service phase from the bootstrap startup
    /// intent. Not a transition and never touches a session: it re-publishes
    /// the phase through the phase port so the coordinator is the sole mode
    /// writer from the moment it installs (M6-D). A repeat of the same phase is
    /// a no-op; a different seed re-publishes the new phase.
    fn on_startup_mode(&mut self, phase: SyncPhase) -> Vec<AcquisitionEffect> {
        let mut effects = Vec::new();
        if phase == self.state.phase {
            return effects;
        }
        self.state.phase = phase;
        if let SyncPhase::Syncing { target } = phase
            && self.state.recovery_anchor_target.is_none()
        {
            self.state.recovery_anchor_target = Some(target);
        }
        effects.push(AcquisitionEffect::SetServicePhase(phase));
        effects
    }

    fn on_connectivity(
        &mut self,
        snapshot: PeerAvailabilitySnapshot,
        phase_neutral: bool,
    ) -> Vec<AcquisitionEffect> {
        let had_peers = self.state.peer_view.has_usable_peer_capability();
        let has_peers = snapshot.has_usable_peer_capability();
        let departed_peers = self
            .state
            .peer_view
            .peers()
            .iter()
            .copied()
            .filter(|peer| !snapshot.peers().contains(peer))
            .collect::<BTreeSet<_>>();
        self.state.peer_view = snapshot;
        // A usable-to-usable membership change still makes requests to a
        // departed peer stale. Release only their exact operation credits and
        // retarget retained, not-yet-emitted work after reconciling the
        // coordinator-owned selected-peer view. This cannot affect a new
        // same-target session because every credit key includes SessionRef.
        if !departed_peers.is_empty() {
            self.release_request_credits_for_departed_peers(&departed_peers);
            self.reconcile_live_sessions_for_peer_view();
            self.retarget_unavailable_queued_request_intents();
        }
        let mut effects = Vec::new();

        match (had_peers, has_peers) {
            (false, false) => {
                // Already disconnected; an unchanged snapshot changes nothing.
                return effects;
            }
            (true, false) => {
                if !phase_neutral {
                    if let Ok(next) = self.state.phase.apply(TransitionFact::PeerCapabilityLost) {
                        self.state.phase = next;
                        effects.push(AcquisitionEffect::SetServicePhase(next));
                    }
                }
                // Retain every session and all non-timer operations exactly as
                // before. Clearing only the expected acquisition timer pauses
                // timeout accounting: an old wakeup is stale and cannot spend
                // budget while the session waits for scarce recovery capacity.
                self.pause_live_sessions_for_peer_loss();
                tracing::info!(
                    target: "acquisition_trace",
                    event = "peer_capability_lost_sessions_paused",
                    phase = ?self.state.phase,
                    active_sessions = self.live_sessions().count(),
                    "acquisition trace: service phase demoted while live acquisition sessions remain owned and resumable"
                );
            }
            (false, true) => {
                if !phase_neutral && self.state.consensus_quorum_available {
                    if let Ok(next) = self
                        .state
                        .phase
                        .apply(TransitionFact::PeerCapabilityAvailable)
                    {
                        self.state.phase = next;
                        effects.push(AcquisitionEffect::SetServicePhase(next));
                    }
                }
                self.resume_live_sessions_after_peer_recovery(&mut effects);
            }
            (true, true) => {
                // A usable-to-usable fact is also a bounded recovery-admission
                // opportunity. It can grant only waiting sessions, never
                // replay every retained session or rearm their paused timers.
                self.resume_live_sessions_after_peer_recovery(&mut effects);
            }
        }

        // A target received while peerless is a concrete consensus/recovery
        // fact, not disposable work. It remains separate from the bounded
        // recovery grants so target creation preserves its existing policy.
        if has_peers {
            let deferred = std::mem::take(&mut self.state.deferred_acquires);
            for (target, (reason, preferred_target, phase_neutral)) in deferred {
                effects.extend(self.on_acquire(target, reason, preferred_target, phase_neutral));
            }
        }
        effects
    }

    fn on_transport_connectivity(
        &mut self,
        snapshot: PeerAvailabilitySnapshot,
    ) -> Vec<AcquisitionEffect> {
        let phase = self.state.phase;
        let mut effects = self.on_connectivity(snapshot, true);
        // Recovery may replay retained demand through on_acquire. This fact is
        // deliberately transport-only, so neither that replay nor direct peer
        // membership handling may publish or retain a phase transition.
        self.state.phase = phase;
        effects.retain(|effect| !matches!(effect, AcquisitionEffect::SetServicePhase(_)));
        effects
    }

    fn on_consensus_quorum_lost(&mut self) -> Vec<AcquisitionEffect> {
        if !self.state.consensus_quorum_available {
            return Vec::new();
        }
        self.state.consensus_quorum_available = false;
        if matches!(self.state.phase, SyncPhase::Disconnected) {
            return Vec::new();
        }
        self.apply_mode_only_fact(TransitionFact::ConsensusQuorumLost)
    }

    fn on_consensus_quorum_available(&mut self) -> Vec<AcquisitionEffect> {
        if self.state.consensus_quorum_available
            && !matches!(self.state.phase, SyncPhase::Disconnected)
        {
            return Vec::new();
        }
        self.state.consensus_quorum_available = true;
        self.apply_mode_only_fact(TransitionFact::ConsensusQuorumAvailable)
    }

    fn apply_mode_only_fact(&mut self, fact: TransitionFact) -> Vec<AcquisitionEffect> {
        let mut effects = Vec::new();
        if let Ok(next) = self.state.phase.apply(fact) {
            if next != self.state.phase {
                self.state.phase = next;
                effects.push(AcquisitionEffect::SetServicePhase(next));
            }
        } else {
            self.stats.rejected_events += 1;
        }
        effects
    }

    fn on_consensus(&mut self, target: ConsensusTarget) -> Vec<AcquisitionEffect> {
        // Consensus observations always update preferred-policy metadata.
        // Session admission is centralized in on_acquire, where a Full or
        // Tracking node with an exact validation-recovery owner coalesces a
        // different moving tip instead of competing with that recovery tree.
        let incoming = target.target();
        let latch_if_empty = matches!(self.state.phase, SyncPhase::Syncing { .. })
            || (self.state.last_installed_lcl.is_none()
                && !matches!(
                    self.state.phase,
                    SyncPhase::Tracking { .. } | SyncPhase::Full { .. }
                ));
        self.observe_consensus_target(incoming, latch_if_empty);
        let selected = self
            .state
            .latest_consensus_target
            .expect("observed consensus target");
        if self
            .state
            .deferred_consensus_acquire
            .is_some_and(|deferred| deferred.hash() == selected.hash())
        {
            self.state.deferred_consensus_acquire = None;
        }
        self.on_acquire(selected, target.reason(), true, false)
    }

    fn on_validation_target(&mut self, target: LedgerTarget) -> Vec<AcquisitionEffect> {
        self.state.latest_validation_target = Some(target);
        self.state.latest_validation_session = None;
        self.on_acquire(target, AcquireReason::Consensus, false, true)
    }

    fn on_validation_recovery_target(
        &mut self,
        target: Option<LedgerTarget>,
    ) -> Vec<AcquisitionEffect> {
        let Some(target) = target else {
            // Accepted-boundary absence withdraws only work waiting behind the
            // stable owner. It is not authority to cancel an in-flight tree.
            self.state.validation_recovery_candidate = None;
            return Vec::new();
        };

        if let Some(anchor) = self.state.validation_recovery_target {
            if anchor.hash() == target.hash() {
                if self
                    .state
                    .validation_recovery_session
                    .and_then(|owner| self.state.sessions.get(&owner))
                    .is_some_and(|state| state.phase.is_terminal())
                {
                    self.state.validation_recovery_candidate = Some(target);
                    return Vec::new();
                }
                self.state.validation_recovery_candidate = None;
                return self.on_acquire(target, AcquireReason::Consensus, false, true);
            }
            self.state.validation_recovery_candidate = Some(target);
            return Vec::new();
        }

        self.state.validation_recovery_target = Some(target);
        self.state.validation_recovery_candidate = None;
        self.on_acquire(target, AcquireReason::Consensus, false, true)
    }

    /// Rippled `consensusViewChange` changes only the operating mode. The
    /// serialized `checkLastClosedLedger` path is responsible for selecting a
    /// concrete preferred-LCL recovery target later.
    fn on_consensus_view_change(&mut self) -> Vec<AcquisitionEffect> {
        self.apply_mode_only_fact(TransitionFact::ConsensusViewChange)
    }

    /// A target-bearing preferred-LCL divergence from the serialized
    /// `checkLastClosedLedger` path.
    /// Demotes `Connected/Tracking/Full -> Syncing { target }` without minting
    /// a session. While already Syncing, the fact updates preferred policy
    /// outside the phase but preserves the recovery anchor whose installation
    /// can complete recovery. The
    /// resident-and-compatible switch path must not start a peer
    /// fetch, and the missing/incomplete path feeds its own `AcquireRequested`
    /// demand. Rejected without usable peers (the transition rules require a
    /// fresh `PeerCapabilityAvailable` fact first). Older and newer per-hash
    /// acquisition sessions may continue independently of that stable anchor.
    fn on_preferred_lcl_divergence(&mut self, target: LedgerTarget) -> Vec<AcquisitionEffect> {
        if !self.state.peer_view.has_usable_peer_capability() {
            self.stats.rejected_events += 1;
            tracing::info!(
                target: "acquisition_trace",
                event = "preferred_lcl_divergence_rejected",
                target_hash = %target.hash(),
                target_seq = ?target.sequence(),
                phase = ?self.state.phase,
                peer_count = self.state.peer_view.peers().len(),
                reason = "no_usable_peers",
                "acquisition trace: preferred-LCL divergence did not enter coordinator"
            );
            return Vec::new();
        }
        self.observe_consensus_target(target, true);
        let fact = TransitionFact::PreferredLclDivergence { target };
        let mut effects = Vec::new();
        if let Ok(next) = self.state.phase.apply(fact) {
            if next != self.state.phase {
                self.state.phase = next;
                effects.push(AcquisitionEffect::SetServicePhase(next));
            }
        } else {
            self.stats.rejected_events += 1;
        }
        effects
    }

    fn on_preferred_lcl_reconciled(&mut self, lcl: LedgerIdentity) -> Vec<AcquisitionEffect> {
        self.state.last_installed_lcl = Some(lcl);
        // This explicit NetworkOps fact proves there is no longer a preferred
        // LCL mismatch, even when the retained recovery hash differs from the
        // local ledger that won reconciliation.
        self.state.recovery_anchor_target = None;
        self.state.recovery_anchor_session = None;
        // The validation-recovery owner is likewise only fallback acquisition
        // advice.  A serialized NetworkOps reconciliation is stronger proof:
        // it must retire that older owner so it cannot mask the newly resident
        // ordinary preferred LCL on the next accepted-boundary pass.
        self.state.validation_recovery_target = None;
        self.state.validation_recovery_session = None;
        self.state.validation_recovery_candidate = None;
        self.state.latest_consensus_target = None;
        self.state.deferred_consensus_acquire = None;
        let fact = TransitionFact::PreferredLclReconciled { lcl };
        let mut effects = Vec::new();
        if let Ok(next) = self.state.phase.apply(fact)
            && next != self.state.phase
        {
            self.state.phase = next;
            effects.push(AcquisitionEffect::SetServicePhase(next));
        }
        effects
    }

    /// Consensus accepted a round with no usable peer positions, or NetworkOPs
    /// became amendment/UNL blocked, while `Full`. Demotes `Full -> Connected`
    /// with no concrete target; a later
    /// [`AcquisitionEvent::PreferredLclDivergence`] or
    /// [`AcquisitionEvent::ConsensusTarget`] fact motivates `Connected -> Syncing`.
    fn on_blocked_with_no_target(&mut self) -> Vec<AcquisitionEffect> {
        let fact = TransitionFact::BlockedWithNoTarget;
        let mut effects = Vec::new();
        if let Ok(next) = self.state.phase.apply(fact) {
            if next != self.state.phase {
                self.state.phase = next;
                effects.push(AcquisitionEffect::SetServicePhase(next));
            }
        } else {
            self.stats.rejected_events += 1;
        }
        effects
    }

    /// The bounded retained-session policy may evict the oldest unowned dormant
    /// consensus session before deferring a newer preferred target at capacity.
    /// Exact preferred and validation recovery owners remain non-evictable;
    /// rippled retains those per-hash InboundLedgers until a natural terminal
    /// boundary.
    fn evict_oldest_dormant_consensus(&mut self, effects: &mut Vec<AcquisitionEffect>) -> bool {
        let recovery_anchor = self.state.recovery_anchor_session;
        let validation_recovery = self.state.validation_recovery_session;
        let oldest = self
            .state
            .sessions
            .iter()
            .filter(|(session, state)| {
                state.reason == AcquireReason::Consensus
                    && state.phase == SessionPhase::Dormant
                    && recovery_anchor != Some(**session)
                    && validation_recovery != Some(**session)
            })
            .min_by_key(|(session, _)| session.session_id())
            .map(|(session, _)| *session);
        let Some(session) = oldest else {
            return false;
        };
        self.cancel_session(session, CancelReason::Replaced, effects);
        true
    }

    fn eligible_peers_for_target(&self, target: LedgerTarget) -> Vec<PeerId> {
        let available = self.state.peer_view.peers();
        match self.state.target_peer_capabilities.get(&target) {
            Some(capabilities) => {
                // `Peer::hasLedger` is a score in rippled's PeerSet, not an
                // eligibility fence: PeerSetImpl sorts peers that advertise
                // the exact ledger first, then still admits other connected
                // peers up to the requested limit. In particular, a retained
                // InboundLedger must be able to replay after reconnect before
                // fresh status messages repopulate the peers' ledger ranges.
                //
                // Preserve that ordering while keeping the transport snapshot
                // authoritative for membership. Treating `Some([])` as no
                // eligible peers strands a paused session forever even though
                // the coordinator has usable peers again.
                let mut peers = capabilities
                    .iter()
                    .map(|capability| capability.peer())
                    .filter(|peer| available.contains(peer))
                    .collect::<Vec<_>>();
                let preferred = peers.iter().copied().collect::<BTreeSet<_>>();
                peers.extend(
                    available
                        .iter()
                        .copied()
                        .filter(|peer| !preferred.contains(peer)),
                );
                peers
            }
            None => available.to_vec(),
        }
    }

    fn peer_is_high_latency(&self, target: LedgerTarget, peer: PeerId) -> bool {
        self.state
            .target_peer_capabilities
            .get(&target)
            .and_then(|capabilities| {
                capabilities
                    .iter()
                    .find(|capability| capability.peer() == peer)
            })
            .is_some_and(|capability| capability.high_latency())
    }

    fn on_acquire(
        &mut self,
        target: LedgerTarget,
        reason: AcquireReason,
        preferred_target: bool,
        phase_neutral: bool,
    ) -> Vec<AcquisitionEffect> {
        let mut effects = Vec::new();
        let authoritative_recovery_demand = reason == AcquireReason::Consensus
            && !phase_neutral
            && self
                .state
                .recovery_anchor_target
                .is_some_and(|anchor| anchor.hash() == target.hash());
        let authoritative_validation_recovery_demand = reason == AcquireReason::Consensus
            && phase_neutral
            && self
                .state
                .validation_recovery_target
                .is_some_and(|anchor| anchor.hash() == target.hash());
        // NetworkOps reports a moving preferred ledger through both
        // ConsensusTarget and AcquireRequested, while trusted validation has
        // its own ValidationTarget path. Centralize the recovery gate here so
        // none of those production paths can mint competing sessions while a
        // phase-neutral exact recovery tree is restoring a Full/Tracking node.
        // The exact anchor hash remains admissible. Once validation recovery
        // is the stable NetworkOps target, its ownership applies in Syncing as
        // well as Full/Tracking; otherwise a terminal owner can spawn both a
        // moving preferred session and its promoted exact successor.
        if reason == AcquireReason::Consensus
            && self
                .state
                .validation_recovery_target
                .is_some_and(|anchor| anchor.hash() != target.hash())
        {
            if preferred_target || authoritative_recovery_demand {
                self.state.deferred_consensus_acquire = Some(target);
            }
            return effects;
        }

        // Rippled retains completed and failed InboundLedgers in its hash
        // registry for one minute. Repeated acquire() calls reuse the completed
        // ledger or return the failed actor until the sweep removes it; neither
        // path starts a duplicate acquisition. Our terminal session retains
        // the same graph for that interval, so do not mint a same-hash
        // replacement around it.
        // An authoritative unbound demand remains latched and is replayed by
        // the TerminalRetention event immediately after the tombstone is reaped.
        let terminal_same_hash = self.state.sessions.iter().find_map(|(session, state)| {
            (session.target_hash() == target.hash()
                && matches!(
                    state.phase,
                    SessionPhase::Complete | SessionPhase::Failed { .. }
                ))
            .then_some(state.phase.clone())
        });
        if let Some(terminal_phase) = terminal_same_hash {
            // A failed actor did not satisfy the request, so an authoritative
            // policy demand must retry after its tombstone is swept. A
            // completed actor already satisfied every same-hash caller;
            // retaining that call as deferred work would manufacture a stale
            // duplicate one minute later, unlike rippled's completed reuse.
            if matches!(terminal_phase, SessionPhase::Failed { .. })
                && (preferred_target || authoritative_recovery_demand)
            {
                self.state.deferred_consensus_acquire = Some(target);
            }
            if terminal_phase == SessionPhase::Complete && authoritative_validation_recovery_demand
            {
                self.state.validation_recovery_target = None;
                self.state.validation_recovery_session = None;
            }
            tracing::info!(
                target: "acquisition_trace",
                event = "acquire_suppressed_by_terminal_tombstone",
                target_hash = %target.hash(),
                target_seq = ?target.sequence(),
                ?reason,
                "acquisition trace: terminal same-hash owner retained until terminal sweep"
            );
            return effects;
        }
        let stable_priority_demand =
            authoritative_recovery_demand || authoritative_validation_recovery_demand;
        let moving_preferred_observation = preferred_target
            && self
                .state
                .recovery_anchor_target
                .is_some_and(|anchor| anchor.hash() != target.hash());

        // Retain one latest preferred target and one latest ordinary/cache
        // target while peerless. The owner replays them after
        // `PeerCapabilityAvailable`; an unbounded moving-tip map would turn a
        // temporary disconnection into a reconnect request storm.
        if !self.state.peer_view.has_usable_peer_capability() {
            if !moving_preferred_observation {
                self.retain_peerless_acquire(
                    target,
                    reason,
                    authoritative_recovery_demand,
                    phase_neutral,
                );
            }
            tracing::info!(
                target: "acquisition_trace",
                event = "acquire_demand_deferred",
                target_hash = %target.hash(),
                target_seq = ?target.sequence(),
                ?reason,
                phase = ?self.state.phase,
                peer_count = self.state.peer_view.peers().len(),
                "acquisition trace: retained target demand until usable peer capability returns"
            );
            return effects;
        }

        // Resolve duplicate demand before capacity and cancellation. An exact
        // same-target demand coalesces with its live owner, including a
        // DurablePending handoff. The only mutable coalescing case is an
        // unknown-sequence session promoted to a known sequence before its
        // header seeded a plan; later or conflicting requests retain the
        // existing replacement semantics, except DurablePending is never
        // cancelled because its durable result is committed to delivery.
        //
        // Ordinary consensus demand is not authoritative for the global phase
        // target, but it still owns active per-hash acquisition work.
        // `latest_consensus_target` remains authoritative through durable
        // completion until the matching LCL-install fact arrives. Do not let
        // any non-authoritative Consensus/Generic/History demand overwrite its
        // phase merely because the preferred session has already terminalized.
        // The demand still gets its independent per-hash session below.
        let ordinary_demand_with_preferred =
            !authoritative_recovery_demand && self.state.latest_consensus_target.is_some();
        let same_hash = self.live_sessions_for_hash(target.hash());
        let exact = same_hash.iter().copied().find(|session| {
            self.state
                .sessions
                .get(session)
                .is_some_and(|state| state.target == target)
        });
        let promotion = if exact.is_none() {
            same_hash.iter().copied().find(|session| {
                self.state
                    .sessions
                    .get(session)
                    .is_some_and(|state| state.can_promote_unknown_sequence(target))
            })
        } else {
            None
        };
        // A hash-only demand carries less identity information than an
        // existing same-hash session with a verified sequence. It therefore
        // coalesces with that live owner rather than cancelling it. This is
        // the legacy InboundLedgers one-acquisition-per-hash behavior and
        // avoids consensus's hash-only follow-up thrashing a catch-up request
        // that already knows the sequence.
        let hash_only_coalesce = if exact.is_none() && promotion.is_none() {
            // InboundLedgers is keyed only by hash. Conflicting/redundant
            // sequence metadata never replaces the existing tree owner;
            // `update(seq)` only fills a previously unknown sequence.
            same_hash.first().copied()
        } else {
            None
        };
        let replaceable: Vec<SessionRef> = if !ordinary_demand_with_preferred
            && exact.is_none()
            && promotion.is_none()
            && hash_only_coalesce.is_none()
        {
            same_hash
                .iter()
                .copied()
                .filter(|session| {
                    self.state
                        .sessions
                        .get(session)
                        .is_some_and(|state| state.phase != SessionPhase::DurablePending)
                })
                .collect()
        } else {
            Vec::new()
        };
        let continuing_existing =
            exact.is_some() || promotion.is_some() || hash_only_coalesce.is_some();
        // Terminal sessions remain observable for stale-event accounting, but
        // they are no longer live coordinator work and must not consume the
        // bounded concurrent-session budget. Otherwise a sequence of failed
        // targets permanently stalls acquisition after `max_sessions`.
        let live_sessions = self
            .state
            .sessions
            .iter()
            .filter(|(session, state)| self.counts_toward_live_capacity(**session, state))
            .count();
        let mut would_exceed = !continuing_existing
            && live_sessions.saturating_sub(replaceable.len()) >= self.state.budgets.max_sessions;
        // A retained preferred-LCL target reserves the next free slot. Generic
        // or History work may coalesce with an existing owner, but cannot take
        // that slot and permanently strand convergence.
        if !stable_priority_demand
            && !continuing_existing
            && self.state.deferred_consensus_acquire.is_some()
        {
            would_exceed = true;
        }
        // A new consensus target evicts retained dormant consensus work before
        // it can be deferred at capacity. Persisting and DurablePending never
        // qualify for dormancy or eviction.
        if would_exceed
            && authoritative_recovery_demand
            && self.evict_oldest_dormant_consensus(&mut effects)
        {
            would_exceed = false;
        }
        // A later preferred-LCL observation does not cancel an existing
        // per-hash InboundLedger in rippled. Preserve the exact validation
        // recovery tree through its natural terminal boundary and retain the
        // latest preferred demand below when capacity is exhausted.
        // Consensus may preempt only a cancellable lower-priority session.
        // DurablePending is intentionally excluded: its completed result and
        // handoff are already committed and must not be revoked.
        if would_exceed && stable_priority_demand {
            let preempt = self
                .state
                .sessions
                .iter()
                .filter(|(session, state)| {
                    self.counts_toward_live_capacity(**session, state)
                        && matches!(
                            state.reason,
                            AcquireReason::History | AcquireReason::Generic
                        )
                        && matches!(state.phase, SessionPhase::Active | SessionPhase::Persisting)
                })
                .min_by_key(|(_, state)| match state.reason {
                    AcquireReason::History => 0u8,
                    AcquireReason::Generic => 1u8,
                    AcquireReason::Consensus => 2u8,
                })
                .map(|(session, _)| *session);
            if let Some(preempt) = preempt {
                self.cancel_session(preempt, CancelReason::Explicit, &mut effects);
                would_exceed = false;
            }
        }
        let disposition = if exact.is_some() {
            "coalesced_exact"
        } else if promotion.is_some() {
            "promoted_known_sequence"
        } else if hash_only_coalesce.is_some() {
            "coalesced_hash_only"
        } else if would_exceed {
            "rejected_capacity"
        } else if replaceable.is_empty() {
            "new_session"
        } else {
            "replacing_conflicting_session"
        };
        if matches!(
            disposition,
            "new_session"
                | "replacing_conflicting_session"
                | "promoted_known_sequence"
                | "rejected_capacity"
        ) {
            tracing::info!(
                target: "acquisition_trace",
                event = "acquire_demand_disposition",
                target_hash = %target.hash(),
                target_seq = ?target.sequence(),
                ?reason,
                phase = ?self.state.phase,
                peer_count = self.state.peer_view.peers().len(),
                same_hash_sessions = same_hash.len(),
                replacement_count = replaceable.len(),
                live_sessions,
                max_sessions = self.state.budgets.max_sessions,
                disposition,
                "acquisition trace: target demand disposition"
            );
        } else {
            tracing::debug!(
                target: "acquisition_trace",
                event = "acquire_demand_coalesced",
                target_hash = %target.hash(),
                target_seq = ?target.sequence(),
                ?reason,
                disposition,
                "acquisition trace: target demand reused its existing live session"
            );
        }
        if would_exceed {
            if authoritative_recovery_demand {
                self.state.deferred_consensus_acquire = Some(target);
                if !matches!(
                    self.state.phase,
                    SyncPhase::Tracking { .. } | SyncPhase::Full { .. }
                ) {
                    let fact = TransitionFact::TargetRequired { target };
                    if let Ok(next) = self.state.phase.apply(fact)
                        && next != self.state.phase
                    {
                        self.state.phase = next;
                        effects.push(AcquisitionEffect::SetServicePhase(next));
                    }
                }
                tracing::info!(
                    target: "acquisition_trace",
                    event = "consensus_demand_deferred_capacity",
                    target_hash = %target.hash(),
                    target_seq = ?target.sequence(),
                    live_sessions,
                    max_sessions = self.state.budgets.max_sessions,
                    "acquisition trace: retained latest preferred-LCL demand until capacity is free"
                );
            } else if authoritative_validation_recovery_demand {
                // The exact validation-recovery latch is the retry owner. It
                // remains pending and will be retried after any terminal fact
                // frees capacity; it never changes the service phase.
            } else if !moving_preferred_observation {
                self.stats.rejected_events += 1;
            }
            return effects;
        }

        // Once an LCL is installed, every ordinary acquisition is phase-neutral:
        // Consensus, Generic, and History describe per-hash cache work, not an
        // actionable mismatch with the installed LCL. NetworkOps emits the
        // separate `PreferredLclDivergence` fact only after its serialized
        // checkLastClosedLedger path proves that mismatch. Initial
        // Connected/Syncing recovery still uses TargetRequired below.
        let phase_target = hash_only_coalesce
            .and_then(|session| self.state.sessions.get(&session).map(|state| state.target))
            .unwrap_or(target);
        let preserve_installed_lcl = matches!(
            self.state.phase,
            SyncPhase::Tracking { .. } | SyncPhase::Full { .. }
        );
        if !phase_neutral && !preserve_installed_lcl && !ordinary_demand_with_preferred {
            let fact = TransitionFact::TargetRequired {
                target: phase_target,
            };
            if let Ok(next) = self.state.phase.apply(fact) {
                if next != self.state.phase {
                    self.state.phase = next;
                    effects.push(AcquisitionEffect::SetServicePhase(next));
                }
            } else {
                self.stats.rejected_events += 1;
                return effects;
            }
        }

        if let Some(session) = exact.or(hash_only_coalesce) {
            self.touch_session_expiry(session, &mut effects);
            return effects;
        }
        if let Some(session) = promotion {
            if let Some(session_state) = self.state.sessions.get_mut(&session) {
                session_state.promote_target(target);
            }
            self.touch_session_expiry(session, &mut effects);
            return effects;
        }

        // Conflicting known sequences retain replacement behavior for normal
        // live sessions. DurablePending is intentionally absent from
        // `replaceable`: its handoff remains pending until acknowledgement.
        for old in replaceable {
            self.cancel_session(old, CancelReason::Replaced, &mut effects);
        }

        // Mint the session against the current storage generation.
        let session = SessionRef::new(
            self.state.run_epoch,
            self.state.ids.next_id(),
            target.hash(),
            self.state.ids.next_id(),
            self.state.storage_generation,
        );
        // rippled `InboundLedger::addPeers` starts through five scored peers
        // and triggers each selected peer. The coordinator's availability
        // snapshot is already ordered by the overlay adapter, so retain its
        // order and establish the same bounded initial fanout.
        let initial_peers = self
            .eligible_peers_for_target(target)
            .into_iter()
            .take(INITIAL_PEER_REQUEST_FANOUT)
            .collect::<Vec<_>>();
        tracing::info!(
            target: "acquisition_trace",
            event = "session_started",
            run_epoch = session.run_epoch().get(),
            session_id = session.session_id().get(),
            target_hash = %session.target_hash(),
            plan_epoch = session.plan_epoch().get(),
            store_generation = session.store_generation().get(),
            target_seq = ?target.sequence(),
            ?reason,
            initial_peer_count = initial_peers.len(),
            initial_peers = ?initial_peers,
            acquire_timeout_ms = self.state.budgets.acquire_timeout.as_millis(),
            "acquisition trace: exact target session started with initial Base fanout"
        );
        let admission = self.state.budgets.admission;
        self.state
            .sessions
            .insert(session, CoordinatorSession::new(target, reason, admission));
        let resident_seeded = self.try_install_resident_engine(session);
        self.stats.sessions_started += 1;
        // Bind delivery metadata to this exact session before the first
        // request. This preserves durable handoff identity when the session
        // was created by a deferred demand replay.
        effects.push(AcquisitionEffect::SessionStarted(session));
        // Request the Base/header ledger packet from each initially acquired
        // peer. An unknown sequence remains a header request with `None`;
        // target hashes are never misframed as tree-node requests. These are
        // intents only; the common emitter below mints their operation ids.
        for peer in initial_peers {
            if let Some(session_state) = self.state.sessions.get_mut(&session) {
                session_state.sent_peers.insert(peer);
            }
        }
        if !resident_seeded {
            let operation = OperationRef::new(
                session,
                OperationKind::HeaderRead,
                self.state.ids.next_id(),
                self.state.ids.next_id(),
            );
            if let Some(state) = self.state.sessions.get_mut(&session) {
                state.pending_header_read = Some(operation);
            }
            effects.push(AcquisitionEffect::SubmitRead(crate::io::ReadRequest::new(
                operation,
                basics::sha_map_hash::SHAMapHash::new(target.hash()),
                target.sequence().unwrap_or(0),
                session.store_generation(),
                Self::read_priority(reason),
            )));
        }

        // Arm the acquisition deadline. The wakeup returns as a typed
        // `TimerFired` matched exactly against this operation.
        let timer_operation = OperationRef::new(
            session,
            OperationKind::Timer,
            self.state.ids.next_id(),
            self.state.ids.next_id(),
        );
        if let Some(session_state) = self.state.sessions.get_mut(&session) {
            session_state.pending_timer = Some((TimerKind::AcquireTimeout, timer_operation));
        }
        self.stats.timers_armed += 1;
        effects.push(AcquisitionEffect::ArmTimer(TimerRequest::new(
            timer_operation,
            TimerKind::AcquireTimeout,
            self.state.budgets.acquire_timeout,
        )));
        self.touch_session_expiry(session, &mut effects);
        if resident_seeded {
            self.run_plan_turn(session, None, &mut effects);
        }
        effects
    }

    /// Coalesce peerless demand into two bounded priority classes. The exact
    /// unbound recovery anchor retains the preferred slot until replay; moving
    /// preferred observations remain `latest_consensus_target` metadata and
    /// cannot delete the only demand capable of binding that anchor. Ordinary
    /// cache demand continues to coalesce to its newest distinct target.
    fn retain_peerless_acquire(
        &mut self,
        target: LedgerTarget,
        reason: AcquireReason,
        preferred_target: bool,
        phase_neutral: bool,
    ) {
        let existing = self.state.deferred_acquires.remove(&target);
        let (mut retained_reason, mut retained_preferred, mut retained_phase_neutral) =
            existing.unwrap_or((reason, false, true));
        if preferred_target || !retained_preferred {
            retained_reason = reason;
        }
        retained_preferred |= preferred_target;
        // A phase-neutral cache request cannot weaken an already-retained
        // ordinary or preferred-LCL demand for the same exact target.
        retained_phase_neutral &= phase_neutral;

        // Keep only the newest entry in the resulting priority class. If an
        // ordinary target is promoted to preferred, this also retires the old
        // preferred target while leaving the other ordinary slot available.
        self.state
            .deferred_acquires
            .retain(|_, (_, is_preferred, _)| *is_preferred != retained_preferred);
        self.state.deferred_acquires.insert(
            target,
            (retained_reason, retained_preferred, retained_phase_neutral),
        );
        debug_assert!(
            self.state.deferred_acquires.len() <= MAX_DEFERRED_PEERLESS_ACQUIRES,
            "peerless deferred demand must remain bounded by policy class"
        );
    }

    fn try_install_resident_engine(&mut self, session: SessionRef) -> bool {
        if self
            .state
            .sessions
            .get(&session)
            .is_none_or(|state| state.plan.engine().is_some())
        {
            return false;
        }
        self.plan_seed
            .build_resident(session)
            .and_then(|engine| {
                self.state
                    .sessions
                    .get_mut(&session)
                    .map(|state| state.plan.install_engine(engine))
            })
            .unwrap_or(false)
    }

    fn on_packet(&mut self, packet: AdmittedLedgerPacket) -> Vec<AcquisitionEffect> {
        let session = packet.lease().session();
        let mut effects = Vec::new();
        let Some(session_state) = self.state.sessions.get_mut(&session) else {
            self.stats.stale_events += 1;
            return Vec::new();
        };
        if session_state.phase != SessionPhase::Active {
            self.stats.stale_events += 1;
            return Vec::new();
        }
        // A header packet seeds the uniquely owned engine once. The seed runs
        // outside state mutation and returns an engine or nothing.
        let packet_peer = packet.peer_id();
        let header = packet.packet().clone();
        let needs_seed = packet.packet().packet_type == ledger::InboundLedgerDataType::Base
            && session_state.plan.engine().is_none();
        let seeded = if needs_seed {
            self.plan_seed
                .build(session, &header)
                .map(|engine| session_state.plan.install_engine(engine))
                .unwrap_or(false)
        } else {
            false
        };
        if needs_seed {
            tracing::info!(
                target: "acquisition_trace",
                event = "base_seed_evaluated",
                run_epoch = session.run_epoch().get(),
                session_id = session.session_id().get(),
                target_hash = %session.target_hash(),
                plan_epoch = session.plan_epoch().get(),
                store_generation = session.store_generation().get(),
                peer_id = packet_peer.get(),
                packet_nodes = header.nodes.len(),
                seeded,
                "acquisition trace: Base packet evaluated for header/root plan seed"
            );
        }
        // Defensive mailbox bounds: ingress already reserved capacity through
        // the `AdmissionGate`, but a misconfigured or replaying ingress must
        // not overflow coordinator state. The plan's mailbox enforces the same
        // `128`-packet / `4 MiB` semantics.
        if !session_state.plan.push_packet(packet) {
            self.stats.packets_dropped += 1;
            tracing::info!(
                target: "acquisition_trace",
                event = "packet_dropped_mailbox_full",
                run_epoch = session.run_epoch().get(),
                session_id = session.session_id().get(),
                target_hash = %session.target_hash(),
                peer_id = packet_peer.get(),
                mailbox_packets = session_state.plan.packet_count(),
                mailbox_bytes = session_state.plan.packet_bytes(),
                "acquisition trace: admitted packet could not enter bounded session mailbox"
            );
            return Vec::new();
        }
        self.stats.packets_admitted += 1;
        // A Base packet only earns progress after the seed has verified and
        // retained its header/root data. Ordinary nodes earn progress later,
        // only when the engine reports a useful SHAMap addition.
        if seeded {
            session_state.plan.note_progress();
            session_state.plan.note_useful_peer(packet_peer, 1);
        }
        // XRPL ledger-data replies do not echo our OperationRef. After the
        // packet has passed exact SessionRef routing and entered this live
        // session's mailbox, conservatively settle only the oldest emitted
        // request for this same session and peer. This is resource accounting,
        // not lifecycle authorization; stale/replacement packets returned
        // above cannot release any current session credit. It restores
        // rippled's reply-driven trigger behavior instead of waiting for the
        // coarse acquire timeout to free the outbound window.
        self.release_oldest_request_credit_for_response(session, packet_peer);
        self.run_plan_turn(session, None, &mut effects);
        effects
    }

    fn on_timer(&mut self, operation: OperationRef, timer: TimerKind) -> Vec<AcquisitionEffect> {
        let session = operation.session();
        if timer == TimerKind::SessionExpiry {
            let matches = self
                .state
                .sessions
                .get(&session)
                .and_then(|state| state.pending_expiry_timer)
                .is_some_and(|expected| expected.is_expected_for(&operation));
            if !matches {
                self.stats.stale_events += 1;
                return Vec::new();
            }
            if self.state.recovery_anchor_session == Some(session)
                || self.state.validation_recovery_session == Some(session)
            {
                // The preferred LCL is deliberately stable while validation
                // and consensus tips move, so it may receive no repeated
                // registry demand. Keep its registry ownership alive; the
                // independent no-progress AcquireTimeout remains the bounded
                // authority that can fail and promote this recovery.
                let mut effects = Vec::new();
                self.touch_session_expiry(session, &mut effects);
                return effects;
            }
            if let Some(state) = self.state.sessions.get_mut(&session) {
                state.expiry_sweep_eligible = true;
                state.pending_expiry_timer = None;
            }
            return Vec::new();
        }
        let local_scan_scheduled = self.state.local_scan_owners.contains(&session)
            || self.state.local_scan_waiters.contains(&session);
        let Some(session_state) = self.state.sessions.get_mut(&session) else {
            self.stats.stale_events += 1;
            return Vec::new();
        };
        let Some((expected_kind, expected)) = session_state.pending_timer else {
            self.stats.stale_events += 1;
            return Vec::new();
        };
        if expected_kind != timer || !expected.is_expected_for(&operation) {
            // A rearmed, unknown, or otherwise unmatched timer is stale.
            self.stats.stale_events += 1;
            return Vec::new();
        }
        if timer == TimerKind::TerminalRetention {
            if !session_state.phase.is_terminal() {
                self.stats.stale_events += 1;
                return Vec::new();
            }
            let target = session_state.target;
            self.state.sessions.remove(&session);
            let target_reaped = !self
                .state
                .sessions
                .values()
                .any(|state| state.target == target);
            if target_reaped {
                self.state.target_peer_capabilities.remove(&target);
                self.plan_seed.session_reaped(session);
            }
            return Vec::new();
        }
        if session_state.phase != SessionPhase::Active
            && session_state.phase != SessionPhase::DurablePending
        {
            self.stats.stale_events += 1;
            return Vec::new();
        }
        // Exact identity matched: consume only the timer currently armed for
        // this session. Handoff retry is intentionally distinct from the plan
        // deadline and may re-publish only while the exact handoff remains
        // pending.
        session_state.pending_timer = None;
        if timer == TimerKind::HandoffRetry {
            if session_state.phase != SessionPhase::DurablePending
                || session_state.pending_handoff.is_none()
            {
                self.stats.stale_events += 1;
                return Vec::new();
            }
            let Some(ledger) = session_state.durable.clone() else {
                self.stats.stale_events += 1;
                return Vec::new();
            };
            let handoff = session_state
                .pending_handoff
                .expect("checked pending handoff");
            return vec![AcquisitionEffect::PublishDurable(DurableLedger::new(
                handoff, session, ledger,
            ))];
        }
        if timer != TimerKind::AcquireTimeout {
            self.stats.stale_events += 1;
            return Vec::new();
        }
        if session_state.local_reconstruction_in_flight() || local_scan_scheduled {
            // `SHAMap::getMissingNodes` waits for and processes successive
            // 512-read batches before returning to InboundLedger::onTimer.
            // A queued/running local-scan permit is the corresponding bounded
            // JtLedgerData job; rippled's TimeoutCounter::onDeadline defers its
            // timer job while that job class is at its limit. Our async
            // translation must therefore rearm without releasing request
            // credits, clearing recentNodes, or consuming the seven network
            // no-progress intervals while the same scan is active or queued.
            let pending_header_read = session_state.pending_header_read.is_some();
            let pending_reads = session_state.plan.pending_read_count();
            let read_backlog = session_state.plan.read_backlog_count();
            let timeout_budget = session_state.plan.timeouts();
            let timer_operation = OperationRef::new(
                session,
                OperationKind::Timer,
                self.state.ids.next_id(),
                self.state.ids.next_id(),
            );
            session_state.pending_timer = Some((TimerKind::AcquireTimeout, timer_operation));
            self.stats.timers_armed += 1;
            tracing::info!(
                target: "acquisition_trace",
                event = "acquisition_timeout_deferred_for_local_reconstruction",
                session_id = session.session_id().get(),
                target_hash = %session.target_hash(),
                pending_header_read,
                pending_reads,
                read_backlog,
                local_scan_scheduled,
                timeout_budget,
                "acquisition trace: local scan retained without consuming network timeout budget"
            );
            return vec![AcquisitionEffect::ArmTimer(TimerRequest::new(
                timer_operation,
                TimerKind::AcquireTimeout,
                self.state.budgets.acquire_timeout,
            ))];
        }
        if !session_state.network_admitted {
            // Recovery admission was withdrawn before this wakeup reached the
            // owner. Do not rearm or consume timeout budget while waiting.
            self.stats.stale_events += 1;
            return Vec::new();
        }
        // Structural completion moves a session into a storage-only boundary.
        // An earlier Active deadline must never consume retry budget, rearm,
        // or fail persistence while the exact write/fence is in flight.
        if session_state.phase != SessionPhase::Active {
            self.stats.stale_events += 1;
            return Vec::new();
        }
        if !self.state.peer_view.has_usable_peer_capability() {
            // Connectivity loss normally clears the expected timer before its
            // wakeup is delivered. Keep this defensive branch non-rearming so
            // an ordering edge cannot consume budget or create timer churn.
            self.stats.stale_events += 1;
            return Vec::new();
        }
        // A completed acquire interval is the conservative ownership point at
        // which this slice releases all requests emitted by this session. No
        // reply has an outbound operation id, so earlier release could permit
        // a retry storm; a later release would strand queued exact work.
        self.release_session_request_credits(session);
        let effects = Vec::new();
        let Some(session_state) = self.state.sessions.get_mut(&session) else {
            self.stats.stale_events += 1;
            return effects;
        };
        let timeout_before = session_state.plan.timeouts();
        let no_progress_interval = session_state.plan.take_no_progress_interval();
        // rippled clears recentNodes_ on every timer tick, including a tick
        // that observed progress. This permits a later trigger to rescan the
        // current tree without retaining a lifetime request-suppression set.
        session_state.plan.clear_recent_nodes();
        let seeded_before_timeout = session_state.plan.engine().is_some();
        let pending_network_before_timeout = session_state.plan.pending_network().len();
        let pending_reads_before_timeout = session_state.plan.pending_read_count();
        let read_backlog_before_timeout = session_state.plan.read_backlog_count();
        let timeout = session_state.plan.on_timeout(no_progress_interval);
        let timeout_after = session_state.plan.timeouts();
        match timeout {
            PlanTimeout::Continue => {
                tracing::info!(
                    target: "acquisition_trace",
                    event = "acquisition_timeout_interval",
                    run_epoch = session.run_epoch().get(),
                    session_id = session.session_id().get(),
                    target_hash = %session.target_hash(),
                    plan_epoch = session.plan_epoch().get(),
                    store_generation = session.store_generation().get(),
                    timeout_budget_before = timeout_before,
                    timeout_budget_after = timeout_after,
                    no_progress_interval,
                    recovery_dispatched = no_progress_interval,
                    seeded_before_timeout,
                    pending_network_before_timeout,
                    pending_reads_before_timeout,
                    read_backlog_before_timeout,
                    "acquisition trace: exact session deadline rearmed after one progress or no-progress interval"
                );
                // rippled `InboundLedger::onTimer` only rebuilds demand on a
                // no-progress interval (`rippled/src/xrpld/app/ledger/detail/
                // InboundLedger.cpp`, `onTimer`/`trigger`/`addPeers`). It
                // rechecks local storage, retargets
                // the retained frontier, and expands peer membership without
                // rebuilding the active traversal. The coordinator does the
                // same through brokered reprobes plus fresh exact effects.
                let mut effects = effects;
                if no_progress_interval {
                    let reason = self.state.sessions.get(&session).map(|state| state.reason);
                    let peers_before_add = self
                        .state
                        .sessions
                        .get(&session)
                        .map(|state| state.sent_peers.iter().copied().collect::<Vec<_>>())
                        .unwrap_or_default();
                    let added_peers = self.escalate_timeout_peers(session);
                    if seeded_before_timeout {
                        let nodes = self.next_timeout_frontier_batch(session);
                        self.submit_timeout_reprobes(session, &nodes, &mut effects);
                        // HISTORY adds peers before its one Timeout trigger.
                        // Other acquisition reasons first broadcast Timeout
                        // to the existing set, then issue one independent
                        // Added trigger to each newly selected peer.
                        let (timeout_peers, added_trigger_peers) = if reason
                            == Some(AcquireReason::History)
                        {
                            let all_peers = self
                                .state
                                .sessions
                                .get(&session)
                                .map(|state| state.sent_peers.iter().copied().collect::<Vec<_>>())
                                .unwrap_or_default();
                            (all_peers, Vec::new())
                        } else {
                            (peers_before_add, added_peers)
                        };
                        // `InboundLedger::trigger(Timeout)` performs a fresh
                        // getMissingNodes scan after clearing `recentNodes_`.
                        // Retrying only the actor's retained batch can be
                        // empty after a useful partial reply: the unanswered
                        // edges still live in the SHAMap continuation but the
                        // Reply scan suppressed them as recently requested.
                        // Re-enter the existing timeout lanes so that scan can
                        // re-publish those exact edges before another deadline.
                        if let Some(state) = self.state.sessions.get_mut(&session) {
                            state.plan.begin_timeout_scan(
                                timeout_peers.clone(),
                                added_trigger_peers.clone(),
                            );
                        }
                        self.send_timeout_frontier_requests_to_peers(
                            session,
                            &nodes,
                            timeout_after,
                            timeout_peers,
                            &mut effects,
                        );
                        for peer in added_trigger_peers {
                            // An Added trigger remains a normal node-id request
                            // even after existing peers cross the aggressive
                            // by-hash timeout threshold.
                            self.send_timeout_frontier_request_to_peer(
                                session,
                                &nodes,
                                AGGRESSIVE_TIMEOUT_THRESHOLD,
                                peer,
                                &mut effects,
                            );
                        }
                    } else if self.try_install_resident_engine(session) {
                        self.run_plan_turn(session, None, &mut effects);
                    } else {
                        self.send_base_request(session, &mut effects);
                    }
                }

                // Rearm the deadline with a fresh operation identity and let the
                // plan run again (queued packets may now be feedable).
                let timer_operation = OperationRef::new(
                    session,
                    OperationKind::Timer,
                    self.state.ids.next_id(),
                    self.state.ids.next_id(),
                );
                if let Some(session_state) = self.state.sessions.get_mut(&session) {
                    session_state.pending_timer =
                        Some((TimerKind::AcquireTimeout, timer_operation));
                }
                self.stats.timers_armed += 1;
                effects.push(AcquisitionEffect::ArmTimer(TimerRequest::new(
                    timer_operation,
                    TimerKind::AcquireTimeout,
                    self.state.budgets.acquire_timeout,
                )));
                self.run_plan_turn(session, None, &mut effects);
                effects
            }
            PlanTimeout::Fail => {
                tracing::info!(
                    target: "acquisition_trace",
                    event = "acquisition_timeout_exhausted",
                    run_epoch = session.run_epoch().get(),
                    session_id = session.session_id().get(),
                    target_hash = %session.target_hash(),
                    plan_epoch = session.plan_epoch().get(),
                    store_generation = session.store_generation().get(),
                    timeout_budget_before = timeout_before,
                    timeout_budget_after = timeout_after,
                    no_progress_interval,
                    seeded_before_timeout,
                    pending_network_before_timeout,
                    pending_reads_before_timeout,
                    read_backlog_before_timeout,
                    "acquisition trace: exact session exhausted its no-progress timeout budget on the seventh interval"
                );
                let mut effects = effects;
                self.fail_session(session, FailureReason::AcquisitionTimeout, &mut effects);
                effects
            }
        }
    }

    fn on_read(&mut self, completion: ReadCompletion) -> Vec<AcquisitionEffect> {
        if completion.operation().kind() == OperationKind::HeaderRead {
            let session = completion.operation().session();
            let Some(state) = self.state.sessions.get_mut(&session) else {
                self.stats.stale_events += 1;
                return Vec::new();
            };
            if state.phase != SessionPhase::Active
                || state.pending_header_read != Some(completion.operation())
            {
                self.stats.stale_events += 1;
                return Vec::new();
            }
            state.pending_header_read = None;
            // A peer Base may have won the race with the initial NodeStore
            // header probe. That probe still settles exactly once, but its
            // miss must not restart Base fanout or replace the already-rooted
            // private graph.
            if state.plan.engine().is_some() {
                let mut effects = Vec::new();
                self.run_plan_turn(session, None, &mut effects);
                return effects;
            }
            let engine = match completion.outcome() {
                crate::io::ReadOutcome::Settled { node: Some(data) } => {
                    self.plan_seed.build_stored_header(session, data)
                }
                _ => None,
            };
            let seeded = engine
                .map(|engine| state.plan.install_engine(engine))
                .unwrap_or(false);
            let mut effects = Vec::new();
            if seeded {
                self.run_plan_turn(session, None, &mut effects);
            } else {
                self.send_base_request(session, &mut effects);
            }
            return effects;
        }
        if !matches!(
            completion.operation().kind(),
            OperationKind::Read | OperationKind::RecoveryRead
        ) {
            self.stats.stale_events += 1;
            return Vec::new();
        }
        let operation_kind = completion.operation().kind();
        let session = completion.operation().session();
        let (outcome, pending_reads_after, pending_traversal_after, read_backlog_after) = {
            let Some(session_state) = self.state.sessions.get_mut(&session) else {
                self.stats.stale_events += 1;
                return Vec::new();
            };
            if session_state.phase != SessionPhase::Active {
                self.stats.stale_events += 1;
                return Vec::new();
            }
            let outcome = session_state.plan.on_read(&completion);
            (
                outcome,
                session_state.plan.pending_read_count(),
                session_state.plan.pending_traversal_read_count(),
                session_state.plan.read_backlog_count(),
            )
        };
        tracing::trace!(
            target: "acquisition_trace",
            event = "node_store_read_completed",
            run_epoch = session.run_epoch().get(),
            session_id = session.session_id().get(),
            target_hash = %session.target_hash(),
            plan_epoch = session.plan_epoch().get(),
            store_generation = session.store_generation().get(),
            outcome = ?completion.outcome(),
            plan_outcome = ?outcome,
            pending_reads_after,
            pending_traversal_after,
            read_backlog_after,
            "acquisition trace: brokered NodeStore read completion returned to session"
        );
        match outcome {
            PlanReadOutcome::Applied => {
                let mut effects = Vec::new();
                // One rippled JtLedgerData job retains its slot throughout the
                // synchronous getMissingNodes call. A partial deferred-read
                // batch therefore only settles its operation; the same owner
                // resumes once the complete traversal barrier drains.
                if operation_kind != OperationKind::Read || pending_traversal_after == 0 {
                    if !self.yield_ordinary_scan_to_recovery(session, true, &mut effects) {
                        self.run_plan_turn(session, None, &mut effects);
                    }
                }
                effects
            }
            PlanReadOutcome::Stale => {
                self.stats.stale_events += 1;
                Vec::new()
            }
        }
    }

    fn on_read_batch(&mut self, completions: Vec<ReadCompletion>) -> Vec<AcquisitionEffect> {
        let mut effects = Vec::new();
        let mut resume = BTreeSet::new();
        for completion in completions {
            if completion.operation().kind() == OperationKind::HeaderRead {
                effects.extend(self.on_read(completion));
                continue;
            }
            if !matches!(
                completion.operation().kind(),
                OperationKind::Read | OperationKind::RecoveryRead
            ) {
                self.stats.stale_events += 1;
                continue;
            }
            let session = completion.operation().session();
            let operation_kind = completion.operation().kind();
            let (outcome, pending_reads_after, pending_traversal_after, read_backlog_after) = {
                let Some(session_state) = self.state.sessions.get_mut(&session) else {
                    self.stats.stale_events += 1;
                    continue;
                };
                if session_state.phase != SessionPhase::Active {
                    self.stats.stale_events += 1;
                    continue;
                }
                let outcome = session_state.plan.on_read(&completion);
                (
                    outcome,
                    session_state.plan.pending_read_count(),
                    session_state.plan.pending_traversal_read_count(),
                    session_state.plan.read_backlog_count(),
                )
            };
            tracing::trace!(
                target: "acquisition_trace",
                event = "node_store_read_completed",
                run_epoch = session.run_epoch().get(),
                session_id = session.session_id().get(),
                target_hash = %session.target_hash(),
                plan_epoch = session.plan_epoch().get(),
                store_generation = session.store_generation().get(),
                outcome = ?completion.outcome(),
                plan_outcome = ?outcome,
                pending_reads_after,
                pending_traversal_after,
                read_backlog_after,
                "acquisition trace: batched brokered NodeStore read completion applied to session"
            );
            match outcome {
                PlanReadOutcome::Applied
                    if operation_kind == OperationKind::RecoveryRead
                        || pending_traversal_after == 0 =>
                {
                    resume.insert(session);
                }
                PlanReadOutcome::Applied => {}
                PlanReadOutcome::Stale => self.stats.stale_events += 1,
            }
        }
        for session in resume {
            if !self.yield_ordinary_scan_to_recovery(session, true, &mut effects) {
                self.run_plan_turn(session, None, &mut effects);
            }
        }
        effects
    }

    fn on_write(&mut self, completion: WriteCompletion) -> Vec<AcquisitionEffect> {
        if completion.operation().kind() != OperationKind::Write {
            self.stats.stale_events += 1;
            return Vec::new();
        }
        let session = completion.operation().session();
        let (outcome, persistence_after) = {
            let Some(session_state) = self.state.sessions.get_mut(&session) else {
                self.stats.stale_events += 1;
                return Vec::new();
            };
            if session_state.phase.is_terminal() || session_state.phase == SessionPhase::Dormant {
                self.stats.stale_events += 1;
                return Vec::new();
            }
            let outcome = session_state
                .plan
                .on_write(completion.operation(), completion.outcome());
            (outcome, session_state.plan.persistence().label())
        };
        tracing::trace!(
            target: "acquisition_trace",
            event = "node_store_write_completed",
            run_epoch = session.run_epoch().get(),
            session_id = session.session_id().get(),
            target_hash = %session.target_hash(),
            plan_epoch = session.plan_epoch().get(),
            store_generation = session.store_generation().get(),
            outcome = ?completion.outcome(),
            plan_outcome = ?outcome,
            persistence_after,
            "acquisition trace: NodeStore write completion returned to session"
        );
        let mut effects = Vec::new();
        match outcome {
            PlanWriteOutcome::IncrementalAccepted => {
                // The physical write is settled, so this is a safe scheduler
                // boundary equivalent to the end of rippled's JtLedgerData
                // continuation. Re-run strict priority selection before the
                // old owner resumes: an exact recovery session may have bound
                // while this write was in flight. Requeueing preserves the old
                // graph; only its now-idle scan permit changes hands.
                if !self.yield_ordinary_scan_to_recovery(session, true, &mut effects) {
                    self.run_plan_turn(session, None, &mut effects);
                }
            }
            PlanWriteOutcome::FinalAccepted => {}
            PlanWriteOutcome::Failed(reason) => self.fail_session(session, reason, &mut effects),
            PlanWriteOutcome::Cancelled(reason) => {
                self.cancel_session(session, reason, &mut effects)
            }
            PlanWriteOutcome::Stale => self.stats.stale_events += 1,
        }
        effects
    }

    fn on_durability(&mut self, completion: DurabilityCompletion) -> Vec<AcquisitionEffect> {
        if completion.operation().kind() != OperationKind::DurabilityFence {
            self.stats.stale_events += 1;
            return Vec::new();
        }
        let session = completion.operation().session();
        let outcome = {
            let Some(session_state) = self.state.sessions.get_mut(&session) else {
                self.stats.stale_events += 1;
                return Vec::new();
            };
            if session_state.phase.is_terminal() || session_state.phase == SessionPhase::Dormant {
                self.stats.stale_events += 1;
                return Vec::new();
            }
            session_state
                .plan
                .on_durability(completion.operation(), completion.outcome())
        };
        let mut effects = Vec::new();
        match outcome {
            PlanDurabilityOutcome::Durable => {
                // Validate the durable payload while the session is still
                // Persisting. A passed fence without a materialized ledger is
                // a terminal storage failure, never a DurablePending handoff
                // with no payload to retry or acknowledge.
                let durable = SessionPhase::DurablePending;
                let ledger = {
                    let Some(session_state) = self.state.sessions.get_mut(&session) else {
                        self.stats.stale_events += 1;
                        return effects;
                    };
                    if !session_phase_transition(&session_state.phase, &durable) {
                        self.stats.stale_events += 1;
                        return effects;
                    }
                    session_state.plan.durable_ledger()
                };
                let Some(ledger) = ledger else {
                    self.fail_session(session, FailureReason::DurabilityFenceFailed, &mut effects);
                    return effects;
                };
                let durable_hash = *ledger.header().hash.as_uint256();
                let durable_sequence = ledger.header().seq;
                let resolved = LedgerTarget::new(durable_hash, Some(durable_sequence));
                // Preferred-LCL selection can name a nonresident ledger by
                // hash before its sequence is known. The verified durable
                // header is the first authoritative identity boundary: refine
                // coordinator policy here so an accepted child can later
                // prove the recovered target is its ancestor.
                if let SyncPhase::Syncing { target } = self.state.phase
                    && target.hash() == durable_hash
                    && target.sequence().is_none()
                {
                    let next = SyncPhase::Syncing { target: resolved };
                    self.state.phase = next;
                    effects.push(AcquisitionEffect::SetServicePhase(next));
                }
                if self.state.latest_consensus_target.is_some_and(|target| {
                    target.hash() == durable_hash && target.sequence().is_none()
                }) {
                    self.state.latest_consensus_target = Some(resolved);
                }
                if self.state.recovery_anchor_target.is_some_and(|target| {
                    target.hash() == durable_hash && target.sequence().is_none()
                }) {
                    self.state.recovery_anchor_target = Some(resolved);
                }
                // Persisting -> DurablePending: NodeStore accepted the final
                // reconstructible payload and the unique handoff is now
                // present, so delivery may be retried exactly once by handoff
                // identity. It is never normal-adoptable before this ordered
                // acceptance fence; physical sync follows backend policy.
                let handoff = self.state.ids.next_id::<DurableHandoffId>();
                let Some(session_state) = self.state.sessions.get_mut(&session) else {
                    self.stats.stale_events += 1;
                    return effects;
                };
                if session_state.target.hash() == durable_hash
                    && session_state.target.sequence().is_none()
                {
                    session_state.promote_target(resolved);
                }
                session_state.phase = durable;
                tracing::info!(
                    target: "acquisition_trace",
                    event = "durability_fence_passed",
                    run_epoch = session.run_epoch().get(),
                    session_id = session.session_id().get(),
                    target_hash = %session.target_hash(),
                    plan_epoch = session.plan_epoch().get(),
                    store_generation = session.store_generation().get(),
                    handoff = handoff.get(),
                    ledger_hash = %ledger.header().hash,
                    ledger_seq = ledger.header().seq,
                    "acquisition trace: final NodeStore acceptance fence passed; publishing exact handoff"
                );
                session_state.pending_handoff = Some(handoff);
                // The acquisition deadline is no longer meaningful once the
                // fence passed; a later rejected handoff arms its own exact
                // retry timer instead.
                session_state.pending_timer = None;
                session_state.durable = Some(Arc::clone(&ledger));
                effects.push(AcquisitionEffect::PublishDurable(DurableLedger::new(
                    handoff, session, ledger,
                )));
            }
            PlanDurabilityOutcome::Failed(reason) => {
                self.fail_session(session, reason, &mut effects)
            }
            PlanDurabilityOutcome::Stale => self.stats.stale_events += 1,
        }
        effects
    }

    fn on_handoff_ack(&mut self, ack: DurableHandoffAcknowledgement) -> Vec<AcquisitionEffect> {
        let session = ack.session();
        let Some(session_state) = self.state.sessions.get_mut(&session) else {
            self.stats.stale_events += 1;
            return Vec::new();
        };
        if session_state.phase.is_terminal() {
            self.stats.stale_events += 1;
            return Vec::new();
        }
        if session_state.pending_handoff != Some(ack.handoff()) {
            // A stale or unknown handoff id never finalizes a session: an
            // earlier delivery may have been retried, but only the exact
            // pending id authorizes `DurablePending -> Complete`.
            self.stats.stale_events += 1;
            return Vec::new();
        }
        let complete = SessionPhase::Complete;
        if session_phase_transition(&session_state.phase, &complete) {
            tracing::info!(
                target: "acquisition_trace",
                event = "durable_handoff_acknowledged",
                run_epoch = session.run_epoch().get(),
                session_id = session.session_id().get(),
                target_hash = %session.target_hash(),
                plan_epoch = session.plan_epoch().get(),
                store_generation = session.store_generation().get(),
                handoff = ack.handoff().get(),
                "acquisition trace: durable handoff recipient completed persistence, registration, and acceptance dispatch"
            );
            session_state.phase = complete;
            session_state.pending_handoff = None;
            session_state.pending_timer = None;
            session_state.pending_expiry_timer = None;
            session_state.durable = None;
            session_state.plan.terminalize_retaining_engine();
            self.stats.sessions_completed += 1;
        }
        let mut effects = Vec::new();
        self.release_local_scan_permit(session, &mut effects);
        self.arm_terminal_retention(session, &mut effects);
        effects
    }

    /// Schedules one exact retry for a rejected durable handoff. Duplicate
    /// rejection events are stale while that retry is armed; the retry timer,
    /// not the rejection callback, performs the re-publish.
    fn on_handoff_rejected(
        &mut self,
        handoff: DurableHandoffId,
        session: SessionRef,
    ) -> Vec<AcquisitionEffect> {
        let valid = self
            .state
            .sessions
            .get(&session)
            .is_some_and(|session_state| {
                session_state.phase == SessionPhase::DurablePending
                    && session_state.pending_handoff == Some(handoff)
                    && session_state.pending_timer.is_none()
            });
        if !valid {
            self.stats.stale_events += 1;
            return Vec::new();
        }
        let operation = OperationRef::new(
            session,
            OperationKind::Timer,
            self.state.ids.next_id(),
            self.state.ids.next_id(),
        );
        let session_state = self
            .state
            .sessions
            .get_mut(&session)
            .expect("validated live handoff session");
        session_state.pending_timer = Some((TimerKind::HandoffRetry, operation));
        self.stats.handoff_rejections += 1;
        self.stats.timers_armed += 1;
        vec![AcquisitionEffect::ArmTimer(TimerRequest::new(
            operation,
            TimerKind::HandoffRetry,
            HANDOFF_RETRY_DELAY,
        ))]
    }

    fn on_lcl_installed(&mut self, identity: LedgerIdentity) -> Vec<AcquisitionEffect> {
        // NetworkOps republishes the current LCL during routine maintenance.
        // It is a meaningful causal fact only when the identity changes or it
        // changes coordinator state; logging each unchanged, nonmatching fact
        // at INFO would overwhelm the target-acquisition trace.
        let lcl_changed = self.state.last_installed_lcl != Some(identity);
        let phase_before = lcl_changed.then(|| format!("{:?}", self.state.phase));
        // This fact is serialized by NetworkOps and is the exact local-LCL
        // counterpart that authorizes a later in-place Full refresh.
        self.state.last_installed_lcl = Some(identity);
        if self
            .state
            .recovery_anchor_target
            .is_some_and(|target| target.hash() == identity.hash())
        {
            self.state.recovery_anchor_target = None;
            self.state.recovery_anchor_session = None;
        }
        if self
            .state
            .latest_consensus_target
            .is_some_and(|target| target.hash() == identity.hash())
        {
            self.state.latest_consensus_target = None;
        }
        // The LCL-install fact legalizes `Syncing -> Tracking` for the acquired
        // target and `Connected -> Tracking` for a locally resident preferred
        // LCL installed without acquisition (rippled switchLastClosedLedger
        // clearing needNetworkLedger). While Tracking, normal in-place
        // consensus keeps installing newer LCLs; refresh that identity so the
        // corresponding publication can satisfy `Tracking -> Full`.
        let mut effects = Vec::new();
        match self.state.phase {
            SyncPhase::Syncing { target } if target.hash() == identity.hash() => {
                let fact = TransitionFact::TargetInstalledAsLcl { lcl: identity };
                if let Ok(next) = self.state.phase.apply(fact) {
                    self.state.phase = next;
                    effects.push(AcquisitionEffect::SetServicePhase(next));
                }
            }
            SyncPhase::Connected => {
                let fact = TransitionFact::TargetInstalledAsLcl { lcl: identity };
                if let Ok(next) = self.state.phase.apply(fact) {
                    self.state.phase = next;
                    effects.push(AcquisitionEffect::SetServicePhase(next));
                }
            }
            SyncPhase::Tracking { lcl } if identity.sequence() > lcl.sequence() => {
                let next = SyncPhase::Tracking { lcl: identity };
                self.state.phase = next;
                effects.push(AcquisitionEffect::SetServicePhase(next));
            }
            // Rippled keeps operating mode separate from LedgerMaster's LCL
            // and publication pointers. Mirror that ownership here: a normal
            // accepted LCL advances Full's LCL identity in place without a
            // visible Full -> Tracking -> Full cycle, even when publication
            // is temporarily behind.
            SyncPhase::Full { lcl, published } if identity.sequence() > lcl.sequence() => {
                self.state.phase = SyncPhase::Full {
                    lcl: identity,
                    published,
                };
            }
            SyncPhase::Full { .. } => {}
            _ => {}
        }
        // A local LCL installation satisfies any pre-fence session for the
        // exact same target. Cancel it now so a stale timer cannot later turn
        // a locally successful consensus round into an acquisition timeout.
        // `cancel_session` rejects DurablePending, preserving the unique
        // durability handoff protocol for coordinator-owned completions.
        for session in self.live_sessions_for_hash(identity.hash()) {
            self.cancel_session(session, CancelReason::LclInstalled, &mut effects);
        }
        if lcl_changed || !effects.is_empty() {
            tracing::info!(
                target: "acquisition_trace",
                event = "lcl_installed_fact_applied",
                lcl_hash = %identity.hash(),
                lcl_seq = identity.sequence(),
                lcl_changed,
                phase_before = ?phase_before,
                phase_after = ?self.state.phase,
                emitted_effects = effects.len(),
                "acquisition trace: LCL installation fact changed coordinator state"
            );
        }
        effects
    }

    /// A publication advance. `Tracking -> Full` requires a fresh publication
    /// anchor whose contiguity to the tracked LCL has already been proven by
    /// the NetworkOps adapter. The anchor may be earlier or later: rippled
    /// `NetworkOPsImp::endConsensus` checks open-ledger freshness, not equality
    /// between the publication head and the newly installed LCL. While already
    /// `Full`, a newer matching publication refreshes only the publication
    /// head; the independent LCL identity advances on `LclInstalled`. Normal
    /// local consensus must not emit a redundant phase cycle. Freshness is
    /// promotion authority, not ownership of the observed publication head.
    fn on_publication(&mut self, identity: LedgerIdentity, fresh: bool) -> Vec<AcquisitionEffect> {
        match self.state.phase {
            SyncPhase::Full { lcl, published } if identity.sequence() > published.sequence() => {
                // The adapter proved the publication remains on the local
                // chain. It does not own the independently installed LCL.
                self.state.phase = SyncPhase::Full {
                    lcl,
                    published: identity,
                };
                Vec::new()
            }
            // NetworkOps only emits this fact after proving bidirectional
            // contiguity between `identity` and the tracked LCL.
            SyncPhase::Tracking { lcl } if fresh => {
                let fact = TransitionFact::ChainContiguous {
                    lcl,
                    published: identity,
                };
                if let Ok(next) = self.state.phase.apply(fact) {
                    self.state.phase = next;
                    return vec![AcquisitionEffect::SetServicePhase(next)];
                }
                Vec::new()
            }
            _ => Vec::new(),
        }
    }

    fn on_store_rotated(&mut self, generation: StoreGeneration) -> Vec<AcquisitionEffect> {
        if generation == self.state.storage_generation {
            return Vec::new();
        }
        self.state.storage_generation = generation;
        let mut effects = Vec::new();
        let stale: Vec<SessionRef> = self
            .state
            .sessions
            .keys()
            .filter(|session| session.store_generation() != generation)
            .copied()
            .collect();
        for session in stale {
            self.cancel_session(session, CancelReason::StoreRotated, &mut effects);
        }
        effects
    }

    /// A fetch-pack pass added by-hash node data to the shared fetch-pack
    /// cache. The fact names no session: re-advance every live session so its
    /// traversal's resident lookup can resolve the newly resident by-hash nodes
    /// without waiting for a peer reply (rippled `gotFetchPack` parity). Each
    /// re-advance is bounded by the same plan-turn limits as any other event;
    /// sessions without a rooted engine or already terminal are not touched.
    fn on_fetch_pack(&mut self) -> Vec<AcquisitionEffect> {
        let live: Vec<SessionRef> = self
            .state
            .sessions
            .iter()
            .filter(|(_, state)| state.phase == SessionPhase::Active)
            .map(|(session, _)| *session)
            .collect();
        let mut effects = Vec::new();
        for session in live {
            let has_engine = self.state.sessions.get(&session).is_some_and(|state| {
                state.phase == SessionPhase::Active && state.plan.engine().is_some()
            });
            if !has_engine {
                continue;
            }
            self.stats.fetch_pack_advances += 1;
            self.run_plan_turn(session, None, &mut effects);
        }
        effects
    }

    /// A periodic heartbeat. Mirrors rippled's `processHeartbeatTimer` mode
    /// reassertion: re-publishes the current phase so the phase port re-runs
    /// the validated-ledger-age / blocked normalization on `Connected` and
    /// `Syncing`. Recovery from `Disconnected` is owned by the connectivity
    /// fact, and `Tracking`/`Full` are never reasserted, matching
    /// `heartbeat_operating_mode_reassertion`.
    fn on_heartbeat(&mut self) -> Vec<AcquisitionEffect> {
        let mut effects = Vec::new();
        match self.state.phase {
            SyncPhase::Connected | SyncPhase::Syncing { .. } => {
                effects.push(AcquisitionEffect::SetServicePhase(self.state.phase));
            }
            _ => {}
        }
        effects
    }

    fn on_registry_sweep(&mut self) -> Vec<AcquisitionEffect> {
        let eligible = self
            .state
            .sessions
            .iter()
            .filter_map(|(session, state)| {
                (state.expiry_sweep_eligible
                    && matches!(state.phase, SessionPhase::Active | SessionPhase::Dormant))
                .then_some(*session)
            })
            .collect::<Vec<_>>();
        let mut effects = Vec::new();
        for session in eligible {
            let logical_scan_in_flight = self.state.swept_local_scan_owners.contains(&session)
                || self.state.local_scan_owners.contains(&session)
                // A queued JtLedgerData lambda captures shared_ptr<InboundLedger>;
                // registry erasure cannot destroy that queued scan owner.
                || self.state.local_scan_waiters.contains(&session)
                || self.state.sessions.get(&session).is_some_and(|state| {
                    matches!(
                        state.plan.persistence(),
                        crate::plan::SessionPersistence::IncrementalWritePending { .. }
                    )
                });
            if logical_scan_in_flight {
                self.state.swept_local_scan_owners.insert(session);
            } else {
                effects.extend(self.expire_idle_session(session));
            }
        }
        effects
    }

    /// Admit bounded local traversal work, not individual reads. At most three
    /// JtLedgerData-equivalent continuations may own a local scan. As in
    /// rippled, an owner retains its slot across successive 512-read batches
    /// until the synchronous-scan analogue reaches a natural boundary, except
    /// that consensus work may take the slot at an externalized read/write
    /// boundary.
    fn ensure_local_scan_permit(
        &mut self,
        session: SessionRef,
        effects: &mut Vec<AcquisitionEffect>,
    ) -> bool {
        let Some(state) = self.state.sessions.get(&session) else {
            return false;
        };
        if state.phase != SessionPhase::Active {
            return false;
        }
        // An incremental write externalizes one synchronous store step from
        // rippled's JtLedgerData job. Keep the existing owner permit while the
        // write is pending, but do not run it again until its exact
        // WriteCompleted event settles. The permit normally remains part of
        // the three-job bound, but consensus work may reclaim it below because
        // this session cannot submit another physical write before that exact
        // completion wakes it.
        if matches!(
            state.plan.persistence(),
            crate::plan::SessionPersistence::IncrementalWritePending { .. }
        ) {
            self.state
                .local_scan_waiters
                .retain(|candidate| *candidate != session);
            return false;
        }
        if self.state.local_scan_owners.contains(&session) {
            return true;
        }
        let consensus_caller = self
            .state
            .sessions
            .get(&session)
            .is_some_and(|state| self.scan_priority_rank(session, state) < 3);
        let recovery_to_admit = consensus_caller
            .then(|| self.best_consensus_scan_candidate(Some(session)))
            .flatten();
        let blocked_lower_priority = recovery_to_admit
            .filter(|_| self.state.local_scan_owners.len() >= MAX_LOCAL_SCAN_OWNERS)
            .and_then(|recovery| {
                let recovery_state = self.state.sessions.get(&recovery)?;
                let recovery_rank = self.scan_priority_rank(recovery, recovery_state);
                if recovery_rank == 2
                    && self.state.plain_consensus_scan_burst >= MAX_PLAIN_CONSENSUS_SCAN_BURST
                {
                    return None;
                }
                self.state
                    .local_scan_owners
                    .iter()
                    .copied()
                    .filter_map(|candidate| {
                        let candidate_state = self.state.sessions.get(&candidate)?;
                        let candidate_rank = self.scan_priority_rank(candidate, candidate_state);
                        (candidate_rank > recovery_rank
                            && matches!(
                                candidate_state.plan.persistence(),
                                crate::plan::SessionPersistence::IncrementalWritePending { .. }
                            ))
                        .then_some((candidate_rank, candidate))
                    })
                    .max_by_key(|(rank, _)| *rank)
                    .map(|(_, candidate)| candidate)
            });
        if let Some(blocked) = blocked_lower_priority {
            // A rippled JtLedgerData worker never remains occupied while an
            // external durability acknowledgement is pending. Quaxar splits
            // that synchronous job at the NodeStore boundary, so reclaim only
            // a lower-ranked owner that cannot currently execute. Its exact
            // WriteCompleted event is already the wake that will requeue it.
            self.state.local_scan_owners.remove(&blocked);
            let recovery_rank = recovery_to_admit
                .and_then(|recovery| {
                    self.state
                        .sessions
                        .get(&recovery)
                        .map(|state| self.scan_priority_rank(recovery, state))
                })
                .expect("admitted consensus recovery must remain live");
            if recovery_rank == 2 {
                self.state.plain_consensus_scan_burst =
                    self.state.plain_consensus_scan_burst.saturating_add(1);
            }
        }
        let owners = &mut self.state.local_scan_owners;
        let waiters = &mut self.state.local_scan_waiters;
        if let Some(recovery) = recovery_to_admit {
            if owners.contains(&recovery) {
                if recovery != session && !waiters.contains(&session) {
                    waiters.push_back(session);
                }
                return recovery == session;
            }
            if owners.len() < MAX_LOCAL_SCAN_OWNERS {
                waiters.retain(|candidate| *candidate != recovery);
                owners.insert(recovery);
                if recovery == session {
                    return true;
                }
                if !waiters.contains(&session) {
                    waiters.push_back(session);
                }
                self.run_plan_turn(recovery, None, effects);
                return false;
            }
        }
        if owners.len() < MAX_LOCAL_SCAN_OWNERS && waiters.is_empty() {
            owners.insert(session);
            return true;
        }
        if !waiters.contains(&session) {
            waiters.push_back(session);
        }
        false
    }

    /// At an async boundary, transfer one ordinary scan slot to the highest
    /// priority consensus waiter. rippled reaches the same boundary inside one
    /// synchronous JtLedgerData job; without this handoff, Quaxar can let a
    /// moving Generic scan repeatedly renew its 512-read/write continuation
    /// while the phase owner waits with useful peer data already retained.
    ///
    /// A read-barrier owner is queued behind recovery. An owner that has just
    /// submitted an incremental write is left unqueued because only its exact
    /// WriteCompleted event may resume that plan.
    fn yield_ordinary_scan_to_recovery(
        &mut self,
        session: SessionRef,
        requeue: bool,
        effects: &mut Vec<AcquisitionEffect>,
    ) -> bool {
        if !self.state.local_scan_owners.contains(&session)
            || self.state.sessions.get(&session).is_none_or(|state| {
                state.phase != SessionPhase::Active || state.plan.pending_read_count() != 0
            })
        {
            return false;
        }
        let recovery = self.best_consensus_scan_candidate(None);
        let Some(recovery) = recovery else {
            return false;
        };
        let owner_rank = self
            .state
            .sessions
            .get(&session)
            .map(|state| self.scan_priority_rank(session, state))
            .expect("scan owner must remain live");
        let recovery_rank = self
            .state
            .sessions
            .get(&recovery)
            .map(|state| self.scan_priority_rank(recovery, state))
            .expect("scan waiter must remain live");
        if recovery_rank >= owner_rank {
            return false;
        }
        if recovery_rank == 2
            && owner_rank == 3
            && self.state.plain_consensus_scan_burst >= MAX_PLAIN_CONSENSUS_SCAN_BURST
        {
            // Two plain-consensus grants have bypassed this ordinary waiter.
            // Keep the owner for one bounded continuation; its caller will run
            // the turn after this refusal. The next completed boundary may
            // yield again from a fresh burst.
            self.state.plain_consensus_scan_burst = 0;
            return false;
        }

        self.state.local_scan_owners.remove(&session);
        self.state
            .local_scan_waiters
            .retain(|candidate| *candidate != recovery && *candidate != session);
        if requeue {
            self.state.local_scan_waiters.push_back(session);
        }
        if recovery_rank == 2 && owner_rank == 3 {
            self.state.plain_consensus_scan_burst =
                self.state.plain_consensus_scan_burst.saturating_add(1);
        }
        self.state.local_scan_owners.insert(recovery);
        self.run_plan_turn(recovery, None, effects);
        true
    }

    fn scan_priority_rank(&self, session_ref: SessionRef, session: &CoordinatorSession) -> u8 {
        if self.state.recovery_anchor_session == Some(session_ref) {
            0
        } else if self.state.validation_recovery_session == Some(session_ref) {
            1
        } else if session.reason == AcquireReason::Consensus {
            2
        } else {
            3
        }
    }

    fn best_consensus_scan_candidate(&self, caller: Option<SessionRef>) -> Option<SessionRef> {
        self.state
            .local_scan_waiters
            .iter()
            .copied()
            .chain(caller)
            .enumerate()
            .filter_map(|(index, candidate)| {
                let state = self.state.sessions.get(&candidate)?;
                (state.phase == SessionPhase::Active
                    && self.scan_priority_rank(candidate, state) < 3)
                    .then_some((self.scan_priority_rank(candidate, state), index, candidate))
            })
            .min_by_key(|(rank, index, _)| (*rank, *index))
            .map(|(_, _, candidate)| candidate)
    }

    /// Select the stable anchor, validation recovery, then other consensus
    /// continuations before ordinary work, retaining FIFO within each class.
    /// rippled orders jobs of the same type by their monotonic job index.
    /// Existing executing owners remain non-preemptive until a safe async
    /// boundary.
    fn pop_scan_waiter(&mut self) -> Option<SessionRef> {
        let sessions = &self.state.sessions;
        let recovery_anchor = self.state.recovery_anchor_session;
        let validation_recovery = self.state.validation_recovery_session;
        let waiters = &mut self.state.local_scan_waiters;
        waiters.retain(|session| {
            sessions
                .get(session)
                .is_some_and(|state| state.phase == SessionPhase::Active)
        });
        let ranked = waiters
            .iter()
            .enumerate()
            .filter_map(|(index, session)| {
                let state = sessions.get(session)?;
                let rank = if recovery_anchor == Some(*session) {
                    0
                } else if validation_recovery == Some(*session) {
                    1
                } else if state.reason == AcquireReason::Consensus {
                    2
                } else {
                    3
                };
                Some((rank, index))
            })
            .collect::<Vec<_>>();
        let absolute = ranked
            .iter()
            .copied()
            .filter(|(rank, _)| *rank < 2)
            .min_by_key(|(rank, index)| (*rank, *index));
        let plain = ranked.iter().copied().find(|(rank, _)| *rank == 2);
        let ordinary = ranked.iter().copied().find(|(rank, _)| *rank == 3);
        let selected = absolute.or_else(|| match (plain, ordinary) {
            (Some(_), Some(ordinary))
                if self.state.plain_consensus_scan_burst >= MAX_PLAIN_CONSENSUS_SCAN_BURST =>
            {
                self.state.plain_consensus_scan_burst = 0;
                Some(ordinary)
            }
            (Some(plain), ordinary) => {
                if ordinary.is_some() {
                    self.state.plain_consensus_scan_burst =
                        self.state.plain_consensus_scan_burst.saturating_add(1);
                }
                Some(plain)
            }
            (None, Some(ordinary)) => {
                self.state.plain_consensus_scan_burst = 0;
                Some(ordinary)
            }
            (None, None) => None,
        });
        selected
            .and_then(|(_, index)| waiters.remove(index))
            .or_else(|| waiters.pop_front())
    }

    fn release_local_scan_permit(
        &mut self,
        session: SessionRef,
        effects: &mut Vec<AcquisitionEffect>,
    ) {
        let was_owner = self.state.local_scan_owners.remove(&session);
        self.state.swept_local_scan_owners.remove(&session);
        self.state
            .local_scan_waiters
            .retain(|candidate| *candidate != session);
        let next = was_owner.then(|| self.pop_scan_waiter()).flatten();
        if let Some(next) = next {
            self.state.local_scan_owners.insert(next);
            self.run_plan_turn(next, None, effects);
        }
    }

    /// End an executing scan at the same boundary where rippled's synchronous
    /// ledger-data job would release its final shared owner reference.
    fn release_local_scan_at_network_boundary(
        &mut self,
        session: SessionRef,
        effects: &mut Vec<AcquisitionEffect>,
    ) {
        let swept = self.state.swept_local_scan_owners.contains(&session);
        self.release_local_scan_permit(session, effects);
        if swept {
            effects.extend(self.expire_idle_session(session));
        }
    }

    /// Runs one bounded plan turn for `session` and appends its work effects.
    /// The tree engine is advanced only on this owner task; work commands are
    /// returned after state mutation and executed by adapters.
    fn run_plan_turn(
        &mut self,
        session: SessionRef,
        reply_peer: Option<PeerId>,
        effects: &mut Vec<AcquisitionEffect>,
    ) {
        if !self.ensure_local_scan_permit(session, effects) {
            return;
        }
        self.stats.plan_turns += 1;
        let Some(reason) = self.state.sessions.get(&session).map(|state| state.reason) else {
            return;
        };
        let priority = self.effective_read_priority(session, reason);
        let (turn, retained_reply_peer) = {
            let CoordinatorState { sessions, ids, .. } = &mut self.state;
            let Some(session_state) = sessions.get_mut(&session) else {
                return;
            };
            if session_state.phase != SessionPhase::Active {
                return;
            }
            let mut ctx = TurnContext {
                session,
                store_generation: session.store_generation(),
                priority,
                ids,
            };
            (
                session_state.plan.run_turn(&mut ctx),
                session_state.plan.network_lane(),
            )
        };
        match turn {
            PlanTurn::Reads(requests) => {
                tracing::trace!(
                    target: "acquisition_trace",
                    event = "node_store_reads_submitted",
                    run_epoch = session.run_epoch().get(),
                    session_id = session.session_id().get(),
                    target_hash = %session.target_hash(),
                    plan_epoch = session.plan_epoch().get(),
                    store_generation = session.store_generation().get(),
                    reads = requests.len(),
                    "acquisition trace: session requested brokered NodeStore reads before peer frontier work"
                );
                for request in requests {
                    effects.push(AcquisitionEffect::SubmitRead(request));
                }
            }
            PlanTurn::Network(_) | PlanTurn::Continue => {
                let (lane_peers, reply_semantics) = match retained_reply_peer.as_ref() {
                    Some(NetworkLane::Reply(peer)) => (Some(vec![*peer]), true),
                    Some(NetworkLane::Added(peer)) => (Some(vec![*peer]), false),
                    Some(NetworkLane::Timeout(peers)) => (Some(peers.clone()), false),
                    None => (None, false),
                };
                let request_peers = reply_peer.map(|peer| vec![peer]).or(lane_peers);
                let lane_undeliverable = retained_reply_peer.as_ref().is_some_and(|lane| {
                    let available = self.state.peer_view.peers();
                    match lane {
                        NetworkLane::Reply(peer) | NetworkLane::Added(peer) => {
                            !available.contains(peer)
                        }
                        NetworkLane::Timeout(peers) => {
                            !peers.iter().any(|peer| available.contains(peer))
                        }
                    }
                });
                let emitted = !lane_undeliverable
                    && self.emit_next_normal_network_request(
                        session,
                        request_peers,
                        reply_peer.is_some() || reply_semantics,
                        effects,
                    );
                let exhausted = self
                    .state
                    .sessions
                    .get(&session)
                    .is_some_and(|state| state.plan.network_lane_exhausted());
                if emitted || lane_undeliverable || exhausted {
                    let continue_reply_lanes =
                        self.state
                            .sessions
                            .get_mut(&session)
                            .is_some_and(|session_state| {
                                session_state.plan.finish_network_lane();
                                session_state.plan.network_lane().is_some()
                                    && session_state.plan.has_runnable_frontier()
                            });
                    if continue_reply_lanes {
                        self.run_plan_turn(session, None, effects);
                    }
                }
                let local_pending = self.state.sessions.get(&session).is_some_and(|state| {
                    state.plan.pending_read_count() != 0 || state.plan.read_backlog_count() != 0
                });
                if !local_pending {
                    self.release_local_scan_at_network_boundary(session, effects);
                }
            }
            PlanTurn::Persist(batch) => {
                let final_batch = batch.requires_fence();
                if final_batch {
                    self.release_local_scan_permit(session, effects);
                }
                tracing::trace!(
                    target: "acquisition_trace",
                    event = "persistence_batch_submitted",
                    run_epoch = session.run_epoch().get(),
                    session_id = session.session_id().get(),
                    target_hash = %session.target_hash(),
                    plan_epoch = session.plan_epoch().get(),
                    store_generation = session.store_generation().get(),
                    ledger_sequence = batch.ledger_sequence(),
                    nodes = batch.nodes().len(),
                    payload_bytes = batch.payload_bytes(),
                    final_batch,
                    "acquisition trace: accepted SHAMap nodes submitted for persistence"
                );
                if final_batch {
                    // Active -> Persisting: the tree is structurally complete
                    // and the final batch must pass its durability fence before
                    // any handoff. Incremental accepted-node batches leave the
                    // session active and carry no fence.
                    let persisting = SessionPhase::Persisting;
                    if let Some(session_state) = self.state.sessions.get_mut(&session)
                        && session_phase_transition(&session_state.phase, &persisting)
                    {
                        session_state.phase = persisting;
                        // The acquisition deadline governs only Active peer
                        // work. Once the final write starts, its exact
                        // write/fence identities exclusively govern progress.
                        // A late already-armed timeout is now stale.
                        session_state.pending_timer = None;
                    }
                    self.release_session_request_credits(session);
                    self.discard_session_request_intents(session);
                }
                effects.push(AcquisitionEffect::SubmitWrite(batch));
                if !final_batch {
                    self.yield_ordinary_scan_to_recovery(session, false, effects);
                }
                // A non-final batch normally retains this scan's existing
                // permit until its exact completion resumes the same owner.
                // The sole exception above transfers the idle slot to an
                // already-waiting exact recovery owner; this writer still
                // resumes only from its exact completion.
            }
            PlanTurn::Invalid => {
                self.release_local_scan_permit(session, effects);
                self.fail_session(session, FailureReason::InvalidTreePlan, effects);
            }
        }
    }

    /// Enqueues one exact request intent without minting an operation. A full
    /// queue returns `false`; callers that own plan work must check capacity
    /// before removing it, while Base retries retain their unseeded session and
    /// will retry from the next exact timeout/recovery fact.
    fn queue_request_intent(
        &mut self,
        session: SessionRef,
        peer: PeerId,
        request: LedgerDataRequest,
        source: &'static str,
    ) -> bool {
        let _ = source;
        self.prune_stale_request_intents();
        let intent = RequestIntent {
            session,
            peer,
            request,
        };
        // Timeout and recovery facts can rediscover the same retained
        // frontier while its earlier intent is waiting for a credit. Preserve
        // one exact copy instead of growing the queue once per timer interval.
        if self.state.outbound.intents.contains(&intent) {
            return true;
        }
        if self.state.outbound.intents.len() >= MAX_QUEUED_REQUEST_INTENTS {
            return false;
        }
        self.state.outbound.intents.push_back(intent);
        true
    }

    fn can_queue_request_intents(&mut self, session: SessionRef, count: usize) -> bool {
        self.prune_stale_request_intents();
        self.state
            .sessions
            .get(&session)
            .is_some_and(|state| state.phase == SessionPhase::Active)
            && self
                .state
                .outbound
                .intents
                .len()
                .checked_add(count)
                .is_some_and(|needed| needed <= MAX_QUEUED_REQUEST_INTENTS)
    }

    /// Remove intents whose exact session can never emit again. Temporarily
    /// paused sessions and unavailable peers remain retained: recovery owns
    /// retargeting those requests without reconstructing plan work.
    fn prune_stale_request_intents(&mut self) {
        let sessions = &self.state.sessions;
        self.state.outbound.intents.retain(|intent| {
            sessions
                .get(&intent.session)
                .is_some_and(|state| !state.phase.is_terminal())
        });
    }

    fn deduplicate_request_intents(&mut self) {
        let mut unique = VecDeque::with_capacity(self.state.outbound.intents.len());
        while let Some(intent) = self.state.outbound.intents.pop_front() {
            if !unique.contains(&intent) {
                unique.push_back(intent);
            }
        }
        self.state.outbound.intents = unique;
    }

    /// Emits requests only after the owning event has completed all lifecycle
    /// mutation. P0 is the latest active consensus target; other intents stay
    /// FIFO within their priority class. The returned request is the only site
    /// that mints an `OperationRef` for overlay delivery.
    fn emit_admitted_requests(&mut self) -> Vec<AcquisitionEffect> {
        let mut effects = Vec::new();
        while let Some(intent) = self.take_next_admissible_request_intent() {
            let operation = OperationRef::new(
                intent.session,
                OperationKind::PeerRequest,
                self.state.ids.next_id(),
                self.state.ids.next_id(),
            );
            self.state
                .outbound
                .outstanding
                .insert(operation, intent.peer);
            *self
                .state
                .outbound
                .outstanding_by_peer
                .entry(intent.peer)
                .or_insert(0) += 1;
            *self
                .state
                .outbound
                .outstanding_by_session
                .entry(intent.session)
                .or_insert(0) += 1;
            self.stats.peer_requests += 1;
            tracing::debug!(
                target: "acquisition_trace",
                event = "outbound_request_emitted",
                run_epoch = intent.session.run_epoch().get(),
                session_id = intent.session.session_id().get(),
                target_hash = %intent.session.target_hash(),
                plan_epoch = intent.session.plan_epoch().get(),
                store_generation = intent.session.store_generation().get(),
                peer_id = intent.peer.get(),
                operation_id = operation.operation_id().get(),
                global_outstanding = self.state.outbound.outstanding.len(),
                "acquisition trace: common coordinator emitter admitted a peer request"
            );
            effects.push(AcquisitionEffect::SendLedgerRequest(PeerRequest::new(
                intent.session,
                operation,
                intent.peer,
                intent.request,
            )));
        }
        effects
    }

    fn take_next_admissible_request_intent(&mut self) -> Option<RequestIntent> {
        self.prune_stale_request_intents();
        let mut selected: Option<(u8, usize)> = None;
        for (index, intent) in self.state.outbound.intents.iter().enumerate() {
            if !self.request_intent_is_admissible(intent) {
                continue;
            }
            let rank = self.request_intent_priority(intent);
            if selected.is_none_or(|(selected_rank, _)| rank < selected_rank) {
                selected = Some((rank, index));
                if rank == 0 {
                    break;
                }
            }
        }
        selected.and_then(|(_, index)| self.state.outbound.intents.remove(index))
    }

    fn request_intent_is_admissible(&self, intent: &RequestIntent) -> bool {
        let Some(session) = self.state.sessions.get(&intent.session) else {
            return false;
        };
        session.phase == SessionPhase::Active
            && session.network_admitted
            && self.state.peer_view.peers().contains(&intent.peer)
            && self.state.outbound.outstanding.len() < MAX_OUTBOUND_REQUESTS_GLOBAL
            && self
                .state
                .outbound
                .outstanding_by_peer
                .get(&intent.peer)
                .copied()
                .unwrap_or(0)
                < MAX_OUTBOUND_REQUESTS_PER_PEER
            && self
                .state
                .outbound
                .outstanding_by_session
                .get(&intent.session)
                .copied()
                .unwrap_or(0)
                < MAX_OUTBOUND_REQUESTS_PER_SESSION
    }

    #[cfg(test)]
    fn request_intent_is_p0(&self, intent: &RequestIntent) -> bool {
        self.request_intent_priority(intent) < 2
    }

    fn request_intent_priority(&self, intent: &RequestIntent) -> u8 {
        if self.state.recovery_anchor_session == Some(intent.session) {
            0
        } else if self.state.validation_recovery_session == Some(intent.session) {
            1
        } else {
            2
        }
    }

    /// Recovery may grant a new peer after the previous overlay snapshot was
    /// lost. Keep queued batches exact, but retarget only their delivery peer;
    /// dropping the intent would discard already-selected plan work.
    fn retarget_queued_request_intents(&mut self, session: SessionRef, peer: PeerId) {
        let available = self.state.peer_view.peers();
        for intent in self
            .state
            .outbound
            .intents
            .iter_mut()
            .filter(|intent| intent.session == session)
        {
            if !available.contains(&intent.peer) {
                intent.peer = peer;
            }
        }
        self.deduplicate_request_intents();
    }

    fn release_all_request_credits(&mut self) {
        self.state.outbound.outstanding.clear();
        self.state.outbound.outstanding_by_peer.clear();
        self.state.outbound.outstanding_by_session.clear();
    }

    /// Releases one already-emitted request by its complete operation identity.
    /// A missing operation is deliberately a no-op, so a stale timer or a
    /// terminal replacement cannot decrement a new session's credit.
    fn release_request_credit(&mut self, operation: OperationRef) {
        let Some(peer) = self.state.outbound.outstanding.remove(&operation) else {
            return;
        };
        let session = operation.session();
        if let Some(count) = self.state.outbound.outstanding_by_peer.get_mut(&peer) {
            *count -= 1;
            if *count == 0 {
                self.state.outbound.outstanding_by_peer.remove(&peer);
            }
        }
        if let Some(count) = self.state.outbound.outstanding_by_session.get_mut(&session) {
            *count -= 1;
            if *count == 0 {
                self.state.outbound.outstanding_by_session.remove(&session);
            }
        }
    }

    /// Ledger-data replies do not carry Quaxar's outbound operation identity.
    /// Settle at most one deterministic oldest credit for the already-validated
    /// `(SessionRef, peer)` route. An unsolicited, stale, or replacement
    /// packet finds no exact matching live operation and cannot affect another
    /// session's budget.
    fn release_oldest_request_credit_for_response(&mut self, session: SessionRef, peer: PeerId) {
        let operation =
            self.state
                .outbound
                .outstanding
                .iter()
                .find_map(|(operation, request_peer)| {
                    (operation.session() == session && *request_peer == peer).then_some(*operation)
                });
        if let Some(operation) = operation {
            self.release_request_credit(operation);
        }
    }

    /// Releases credits only for exact requests sent to peers absent from the
    /// newest availability snapshot. A session's other requests remain
    /// outstanding, and a replacement session cannot match these operations.
    fn release_request_credits_for_departed_peers(&mut self, departed_peers: &BTreeSet<PeerId>) {
        let operations = self
            .state
            .outbound
            .outstanding
            .iter()
            .filter_map(|(operation, peer)| departed_peers.contains(peer).then_some(*operation))
            .collect::<Vec<_>>();
        for operation in operations {
            self.release_request_credit(operation);
        }
    }

    /// Releases only requests that were actually emitted for this exact
    /// session. Timeout expiry uses this path, so queued exact normal-frontier
    /// work remains available for the next admission drain.
    fn release_session_request_credits(&mut self, session: SessionRef) {
        let operations = self
            .state
            .outbound
            .outstanding
            .keys()
            .filter(|operation| operation.session() == session)
            .copied()
            .collect::<Vec<_>>();
        for operation in operations {
            self.release_request_credit(operation);
        }
    }

    /// Discards unsent intents only after this session no longer has an active
    /// network plan: structural completion, failure, cancellation, replacement,
    /// or shutdown. It is deliberately separate from credit expiry so a timeout
    /// cannot lose a plan batch already moved into the bounded intent queue.
    fn discard_session_request_intents(&mut self, session: SessionRef) {
        self.state
            .outbound
            .intents
            .retain(|intent| intent.session != session);
    }

    /// Reconciles only the coordinator's selected-peer sets after a partial
    /// availability change. Full peer loss uses the pause/recovery path;
    /// this path preserves still-admitted sessions and never creates sends.
    fn reconcile_live_sessions_for_peer_view(&mut self) {
        let sessions = self
            .state
            .sessions
            .iter()
            .filter(|(_, state)| state.phase == SessionPhase::Active && state.network_admitted)
            .map(|(session, _)| *session)
            .collect::<Vec<_>>();
        for session in sessions {
            self.reconcile_selected_peers(session);
        }
    }

    /// Retargets retained work only after the selected-peer reconciliation has
    /// found a live peer for its exact active session. Terminal and paused
    /// sessions are left untouched here; their intents are removed by their
    /// lifecycle transition or handled by the explicit recovery grant.
    fn retarget_unavailable_queued_request_intents(&mut self) {
        let retargets = self
            .state
            .sessions
            .iter()
            .filter_map(|(session, state)| {
                (state.phase == SessionPhase::Active && state.network_admitted)
                    .then(|| {
                        state
                            .sent_peers
                            .iter()
                            .copied()
                            .find(|peer| self.state.peer_view.peers().contains(peer))
                            .map(|peer| (*session, peer))
                    })
                    .flatten()
            })
            .collect::<BTreeMap<_, _>>();
        for intent in &mut self.state.outbound.intents {
            if !self.state.peer_view.peers().contains(&intent.peer)
                && let Some(peer) = retargets.get(&intent.session)
            {
                intent.peer = *peer;
            }
        }
        self.deduplicate_request_intents();
    }

    /// Emits at most one normal frontier request per selected peer for this
    /// owner event. rippled `InboundLedger::filterNodes` (
    /// `src/xrpld/app/ledger/detail/InboundLedger.cpp:718-745`) truncates to
    /// one 12-node blind/local or 128-node reply request before PeerSet sends;
    /// the plan FIFO gives that behavior an owned, exact frontier boundary.
    ///
    /// Sequence and peer availability are checked before consuming the FIFO,
    /// so a temporarily unsendable owner event leaves all exact work queued for
    /// the next wake. Timeout retries deliberately use `retained_network`
    /// directly and never consume this normal-emission queue.
    fn emit_next_normal_network_request(
        &mut self,
        session: SessionRef,
        request_peers: Option<Vec<PeerId>>,
        reply_semantics: bool,
        _effects: &mut Vec<AcquisitionEffect>,
    ) -> bool {
        // Late admitted packets may still advance a retained plan after peer
        // loss. They may produce storage work, but must not consume the FIFO
        // frontier or send to peers absent from the current snapshot.
        if !self.state.peer_view.has_usable_peer_capability() {
            return false;
        }
        let available = self.state.peer_view.peers();
        let Some((target, sequence, timeout_count, peers)) =
            self.state.sessions.get(&session).and_then(|state| {
                (state.phase == SessionPhase::Active && state.network_admitted).then(|| {
                    let peers = match request_peers.as_ref() {
                        Some(requested) => requested
                            .iter()
                            .copied()
                            .filter(|peer| available.contains(peer))
                            .collect(),
                        None => state
                            .sent_peers
                            .iter()
                            .copied()
                            .filter(|peer| available.contains(peer))
                            .collect::<Vec<_>>(),
                    };
                    (
                        state.target,
                        state.plan.ledger_sequence(),
                        state.plan.timeouts(),
                        peers,
                    )
                })
            })
        else {
            return false;
        };
        let Some(sequence) = sequence else {
            return false;
        };
        if peers.is_empty() {
            return false;
        }
        let request_limit = if reply_semantics {
            REPLY_NODE_REQUEST_BATCH
        } else {
            BLIND_NODE_REQUEST_BATCH
        };
        // Never remove plan work until this bounded owner queue can retain a
        // request intent for every selected peer. A full queue therefore
        // delays a normal frontier batch instead of silently losing it.
        if !self.can_queue_request_intents(session, peers.len()) {
            tracing::debug!(
                target: "acquisition_trace",
                event = "network_frontier_retained_admission_full",
                run_epoch = session.run_epoch().get(),
                session_id = session.session_id().get(),
                target_hash = %session.target_hash(),
                queued_intents = self.state.outbound.intents.len(),
                "acquisition trace: normal frontier remains in the plan until outbound intent capacity is free"
            );
            return false;
        }
        let nodes = self
            .state
            .sessions
            .get_mut(&session)
            .filter(|state| state.phase == SessionPhase::Active && state.network_admitted)
            .map(|state| state.plan.take_next_normal_network_batch(request_limit))
            .unwrap_or_default();
        let Some(first) = nodes.first() else {
            return false;
        };
        let kind = first.kind();
        debug_assert!(nodes.iter().all(|node| node.kind() == kind));
        let node_ids = nodes.iter().map(|node| node.node_id()).collect::<Vec<_>>();
        tracing::trace!(
            target: "acquisition_trace",
            event = "network_frontier_requested",
            run_epoch = session.run_epoch().get(),
            session_id = session.session_id().get(),
            target_hash = %session.target_hash(),
            plan_epoch = session.plan_epoch().get(),
            store_generation = session.store_generation().get(),
            ledger_sequence = sequence,
            reply_peer = ?request_peers.as_ref().and_then(|peers| peers.first()).map(|peer| peer.get()),
            peer_count = peers.len(),
            nodes = node_ids.len(),
            ?kind,
            request_limit,
            "acquisition trace: requesting one FIFO SHAMap frontier batch from selected peers"
        );
        for peer in peers {
            let query_depth = if reply_semantics && self.peer_is_high_latency(target, peer) {
                2
            } else {
                u32::from(reply_semantics)
            };
            let queued = self.queue_request_intent(
                session,
                peer,
                LedgerDataRequest::GetLedgerNodes {
                    kind,
                    node_ids: node_ids.clone(),
                    sequence,
                    query_depth,
                    indirect: timeout_count != 0,
                },
                "normal_frontier",
            );
            debug_assert!(queued, "capacity was reserved before removing plan work");
        }
        true
    }

    /// Terminalizes a live session with a failure reason: the session phase
    /// becomes `Failed`, its plan is cancelled, and a cancellation effect is
    /// emitted so adapters release their resource-local state.
    fn fail_session(
        &mut self,
        session: SessionRef,
        reason: FailureReason,
        effects: &mut Vec<AcquisitionEffect>,
    ) {
        let Some(session_state) = self.state.sessions.get_mut(&session) else {
            return;
        };
        if session_state.phase.is_terminal() {
            return;
        }
        let failed = SessionPhase::Failed { reason };
        if session_phase_transition(&session_state.phase, &failed) {
            tracing::info!(
                target: "acquisition_trace",
                event = "session_failed",
                run_epoch = session.run_epoch().get(),
                session_id = session.session_id().get(),
                target_hash = %session.target_hash(),
                plan_epoch = session.plan_epoch().get(),
                store_generation = session.store_generation().get(),
                ?reason,
                phase_before = ?session_state.phase,
                plan_runs = session_state.plan.runs(),
                timeout_count = session_state.plan.timeouts(),
                pending_network = session_state.plan.pending_network().len(),
                pending_reads = session_state.plan.pending_read_count(),
                read_backlog = session_state.plan.read_backlog_count(),
                persistence = session_state.plan.persistence().label(),
                "acquisition trace: session terminalized with failure"
            );
            session_state.phase = failed;
            session_state.pending_timer = None;
            session_state.pending_expiry_timer = None;
            session_state.plan.terminalize_retaining_engine();
            self.release_local_scan_permit(session, effects);
            self.release_session_request_credits(session);
            self.discard_session_request_intents(session);
            self.stats.sessions_cancelled += 1;
            *self.stats.failed_by_reason.entry(reason).or_insert(0) += 1;
            effects.push(AcquisitionEffect::CancelSession(session));
            self.arm_terminal_retention(session, effects);
        }
    }

    fn arm_terminal_retention(
        &mut self,
        session: SessionRef,
        effects: &mut Vec<AcquisitionEffect>,
    ) {
        let operation = OperationRef::new(
            session,
            OperationKind::Timer,
            self.state.ids.next_id(),
            self.state.ids.next_id(),
        );
        let Some(state) = self.state.sessions.get_mut(&session) else {
            return;
        };
        if !state.phase.is_terminal() {
            return;
        }
        state.pending_timer = Some((TimerKind::TerminalRetention, operation));
        effects.push(AcquisitionEffect::ArmTimer(TimerRequest::new(
            operation,
            TimerKind::TerminalRetention,
            TERMINAL_RETENTION,
        )));
    }

    /// Replace the independent one-minute inactivity timer. Rippled touches an
    /// InboundLedger only in its constructor, `update`, and `done`; network
    /// progress deliberately does not keep a moving-tip acquisition registered.
    fn touch_session_expiry(&mut self, session: SessionRef, effects: &mut Vec<AcquisitionEffect>) {
        // A fresh same-hash demand revives a graph whose registry reference
        // was swept while its local scan was still executing. Quaxar coalesces
        // that demand into the retained owner, so the old deferred reap must
        // not cancel it when the scan reaches its boundary.
        self.state.swept_local_scan_owners.remove(&session);
        let operation = OperationRef::new(
            session,
            OperationKind::Timer,
            self.state.ids.next_id(),
            self.state.ids.next_id(),
        );
        let Some(state) = self.state.sessions.get_mut(&session) else {
            return;
        };
        if !matches!(state.phase, SessionPhase::Active | SessionPhase::Dormant) {
            return;
        }
        state.expiry_sweep_eligible = false;
        state.pending_expiry_timer = Some(operation);
        effects.push(AcquisitionEffect::ArmTimer(TimerRequest::new(
            operation,
            TimerKind::SessionExpiry,
            SESSION_IDLE_MINIMUM,
        )));
    }

    /// Remove an inactive live owner immediately, invalidating all exact async
    /// identities. Canonical nodes already admitted by its engine remain in the
    /// shared tree cache/NodeStore and can seed a later same-hash acquisition;
    /// retaining the private traversal would recreate the leak this sweep fixes.
    fn expire_idle_session(&mut self, session: SessionRef) -> Vec<AcquisitionEffect> {
        let Some(mut state) = self.state.sessions.remove(&session) else {
            self.stats.stale_events += 1;
            return Vec::new();
        };
        if !matches!(state.phase, SessionPhase::Active | SessionPhase::Dormant) {
            state.pending_expiry_timer = None;
            self.state.sessions.insert(session, state);
            self.stats.stale_events += 1;
            return Vec::new();
        }
        let target = state.target;
        state.plan.cancel();
        let mut effects = Vec::new();
        self.release_local_scan_permit(session, &mut effects);
        self.release_session_request_credits(session);
        self.discard_session_request_intents(session);
        self.plan_seed.session_reaped(session);
        if !self
            .state
            .sessions
            .values()
            .any(|candidate| candidate.target == target)
        {
            self.state.target_peer_capabilities.remove(&target);
        }
        self.stats.sessions_cancelled += 1;
        *self
            .stats
            .cancelled_by_reason
            .entry(CancelReason::IdleExpired)
            .or_insert(0) += 1;
        tracing::info!(
            target: "acquisition_trace",
            event = "session_idle_expired",
            run_epoch = session.run_epoch().get(),
            session_id = session.session_id().get(),
            target_hash = %session.target_hash(),
            plan_epoch = session.plan_epoch().get(),
            store_generation = session.store_generation().get(),
            "acquisition trace: swept live per-hash owner after one minute without repeated demand"
        );
        effects.push(AcquisitionEffect::CancelSession(session));
        effects
    }

    /// Grants bounded direct recovery work after peer capability returns. A
    /// grant is not a second scheduler: it is coordinator-owned session state
    /// that remains paused until a future connectivity fact assigns it a peer.
    ///
    /// The ordering is deterministic and avoids the `BTreeMap<SessionRef>`
    /// target-hash order: the exact recovery anchor wins, followed by other
    /// consensus sessions, Generic, then History. Each non-anchor class is
    /// FIFO, so moving tip observations cannot create a second priority lane.
    /// Only paused Active sessions participate: persisting work needs no peer
    /// grant and cannot displace a recoverable preferred target.
    fn resume_live_sessions_after_peer_recovery(&mut self, effects: &mut Vec<AcquisitionEffect>) {
        let priority = self.recovery_priority_sessions();
        if let Some(phase_target) = self
            .state
            .recovery_anchor_session
            .and_then(|anchor| self.state.sessions.get(&anchor).map(|state| state.target))
        {
            let fact = TransitionFact::TargetRequired {
                target: phase_target,
            };
            if let Ok(next) = self.state.phase.apply(fact)
                && next != self.state.phase
            {
                self.state.phase = next;
                effects.push(AcquisitionEffect::SetServicePhase(next));
            }
        }

        // Overlay peers are reusable across every per-hash InboundLedger.
        // Transport credits serialize actual sends; peer availability is not
        // an exclusive lease that may strand sessions beyond peer count.
        for session in priority {
            let Some(target) = self.state.sessions.get(&session).map(|state| state.target) else {
                continue;
            };
            if let Some(peer) = self.eligible_peers_for_target(target).into_iter().next() {
                self.grant_recovered_session(session, peer, effects);
            }
        }
    }

    fn recovery_priority_sessions(&self) -> Vec<SessionRef> {
        let mut sessions = self
            .state
            .sessions
            .iter()
            .filter(|(_, state)| state.phase == SessionPhase::Active && !state.network_admitted)
            .map(|(session, _)| *session)
            .collect::<Vec<_>>();
        sessions.sort_by(|left, right| {
            let left_state = self
                .state
                .sessions
                .get(left)
                .expect("recovery priority session must remain live");
            let right_state = self
                .state
                .sessions
                .get(right)
                .expect("recovery priority session must remain live");
            self.recovery_priority_rank(*left, left_state)
                .cmp(&self.recovery_priority_rank(*right, right_state))
                // Preserve FIFO within each non-anchor class. A moving
                // validation or consensus observation must not become an
                // implicit second priority channel.
                .then_with(|| left.session_id().cmp(&right.session_id()))
                .then_with(|| left.cmp(right))
        });
        sessions
    }

    fn recovery_priority_rank(&self, session_ref: SessionRef, session: &CoordinatorSession) -> u8 {
        match session.reason {
            _ if self.state.recovery_anchor_session == Some(session_ref)
                || self.state.validation_recovery_session == Some(session_ref) =>
            {
                0
            }
            AcquireReason::Consensus => 1,
            AcquireReason::Generic => 2,
            AcquireReason::History => 3,
        }
    }

    fn pause_live_sessions_for_peer_loss(&mut self) {
        // A connectivity loss is an explicit ownership boundary: no wire reply
        // can now prove an emitted request is still outstanding. Drop credits
        // but retain exact queued intents; recovery retargets them to the peer
        // newly granted by the coordinator.
        self.release_all_request_credits();
        for state in self.state.sessions.values_mut() {
            if state.phase == SessionPhase::Active {
                state.network_admitted = false;
                // The timer port has no cancellation effect. Dropping the
                // expected identity makes an already queued wakeup stale and
                // freezes timeout accounting until a recovery grant rearms it.
                state.pending_timer = None;
            }
        }
    }

    fn grant_recovered_session(
        &mut self,
        session: SessionRef,
        peer: PeerId,
        effects: &mut Vec<AcquisitionEffect>,
    ) {
        self.reconcile_selected_peers(session);
        self.retarget_queued_request_intents(session, peer);
        let Some((seeded, timeout_budget, selected_peers)) =
            self.state.sessions.get_mut(&session).and_then(|state| {
                (state.phase == SessionPhase::Active && !state.network_admitted).then(|| {
                    state.network_admitted = true;
                    state.sent_peers.insert(peer);
                    (
                        state.plan.engine().is_some(),
                        state.plan.timeouts(),
                        state.sent_peers.len(),
                    )
                })
            })
        else {
            return;
        };
        tracing::info!(
            target: "acquisition_trace",
            event = "peer_capability_recovered_session_granted",
            run_epoch = session.run_epoch().get(),
            session_id = session.session_id().get(),
            target_hash = %session.target_hash(),
            plan_epoch = session.plan_epoch().get(),
            store_generation = session.store_generation().get(),
            peer_id = peer.get(),
            seeded,
            timeout_budget,
            selected_peers,
            "acquisition trace: bounded recovery grant resumed one retained session"
        );
        if seeded {
            let nodes = self.next_timeout_frontier_batch(session);
            self.submit_timeout_reprobes(session, &nodes, effects);
            self.send_timeout_frontier_request_to_peer(
                session,
                &nodes,
                timeout_budget,
                peer,
                effects,
            );
        } else {
            self.send_base_request_to_peer(session, peer, effects);
        }
        self.ensure_acquire_timeout_armed(session, effects);
    }

    /// Removes unavailable selected peers and fills the same bounded window
    /// from the current overlay snapshot. It only changes coordinator-owned
    /// selection state; no transport or plan work occurs here.
    fn reconcile_selected_peers(&mut self, session: SessionRef) {
        let available = self.state.peer_view.peers().to_vec();
        let Some(state) = self.state.sessions.get_mut(&session) else {
            return;
        };
        if state.phase != SessionPhase::Active {
            return;
        }
        state.sent_peers.retain(|peer| available.contains(peer));
    }

    /// Keeps one exact acquisition deadline outstanding through recovery. A
    /// pre-outage timer remains authoritative; a missing timer is armed only
    /// here by the serialized coordinator, avoiding a timer replacement race.
    fn ensure_acquire_timeout_armed(
        &mut self,
        session: SessionRef,
        effects: &mut Vec<AcquisitionEffect>,
    ) {
        let should_arm = self.state.sessions.get(&session).is_some_and(|state| {
            state.phase == SessionPhase::Active
                && state.network_admitted
                && state.pending_timer.is_none()
        });
        if !should_arm {
            return;
        }
        let timer_operation = OperationRef::new(
            session,
            OperationKind::Timer,
            self.state.ids.next_id(),
            self.state.ids.next_id(),
        );
        if let Some(state) = self.state.sessions.get_mut(&session) {
            state.pending_timer = Some((TimerKind::AcquireTimeout, timer_operation));
        }
        self.stats.timers_armed += 1;
        effects.push(AcquisitionEffect::ArmTimer(TimerRequest::new(
            timer_operation,
            TimerKind::AcquireTimeout,
            self.state.budgets.acquire_timeout,
        )));
    }

    /// Adds at most `TIMEOUT_PEER_ESCALATION` currently available, previously
    /// unselected peers without exceeding the per-session selected-peer
    /// window. The set is the coordinator's replacement for rippled's PeerSet
    /// membership; it never owns transport or retains every responder.
    fn escalate_timeout_peers(&mut self, session: SessionRef) -> Vec<PeerId> {
        let Some((target, selected, remaining)) = self
            .state
            .sessions
            .get(&session)
            .filter(|state| state.phase == SessionPhase::Active)
            .map(|state| {
                (
                    state.target,
                    state.sent_peers.clone(),
                    MAX_SELECTED_PEERS.saturating_sub(state.sent_peers.len()),
                )
            })
        else {
            return Vec::new();
        };
        let additions = self
            .eligible_peers_for_target(target)
            .into_iter()
            .filter(|peer| !selected.contains(peer))
            .take(TIMEOUT_PEER_ESCALATION.min(remaining))
            .collect::<Vec<_>>();
        if let Some(state) = self.state.sessions.get_mut(&session) {
            state.sent_peers.extend(additions.iter().copied());
        }
        additions
    }

    /// Selects one rotating exact frontier batch for one no-progress timeout.
    /// The resulting records are reused for both local reprobes and peer
    /// resends, so neither port can repeatedly select only the first batch.
    fn next_timeout_frontier_batch(&mut self, session: SessionRef) -> Vec<PlanNetworkNeed> {
        self.state
            .sessions
            .get_mut(&session)
            .filter(|state| state.phase == SessionPhase::Active)
            .map(|state| state.plan.next_timeout_recovery_batch())
            .unwrap_or_default()
    }

    /// Reprobe one exact timeout frontier batch through the asynchronous
    /// NodeStore port. No plan or coordinator lock performs physical storage
    /// I/O.
    fn submit_timeout_reprobes(
        &mut self,
        session: SessionRef,
        nodes: &[PlanNetworkNeed],
        effects: &mut Vec<AcquisitionEffect>,
    ) {
        let Some(reason) = self.state.sessions.get(&session).map(|state| state.reason) else {
            return;
        };
        let priority = self.effective_read_priority(session, reason);
        let requests = {
            let CoordinatorState { sessions, ids, .. } = &mut self.state;
            let Some(state) = sessions.get_mut(&session) else {
                return;
            };
            if state.phase != SessionPhase::Active {
                return;
            }
            let mut ctx = TurnContext {
                session,
                store_generation: session.store_generation(),
                priority,
                ids,
            };
            state.plan.reprobe_network_batch(nodes, &mut ctx)
        };
        for request in requests {
            effects.push(AcquisitionEffect::SubmitRead(request));
        }
    }

    /// Resends the retained exact frontier with fresh operation identities.
    /// Normal retries preserve node ids and tree kind via `GetLedgerNodes`;
    /// only the rippled `> 4` timeout threshold switches to bounded by-hash
    /// requests. The session/plan/store identity is unchanged throughout.
    /// Sends one exact retained frontier batch to only the peer granted by a
    /// recovery event. The ordinary timeout path above remains unchanged and
    /// may still use the complete selected-peer window.
    fn send_timeout_frontier_request_to_peer(
        &mut self,
        session: SessionRef,
        nodes: &[PlanNetworkNeed],
        timeout_count: u32,
        peer: PeerId,
        effects: &mut Vec<AcquisitionEffect>,
    ) {
        self.send_timeout_frontier_requests_to_peers(
            session,
            nodes,
            timeout_count,
            vec![peer],
            effects,
        );
    }

    fn send_timeout_frontier_requests_to_peers(
        &mut self,
        session: SessionRef,
        nodes: &[PlanNetworkNeed],
        timeout_count: u32,
        peers: Vec<PeerId>,
        _effects: &mut Vec<AcquisitionEffect>,
    ) {
        debug_assert!(nodes.len() <= TIMEOUT_FRONTIER_REQUEST_LIMIT);
        let sequence = self.state.sessions.get(&session).and_then(|state| {
            (state.phase == SessionPhase::Active && state.network_admitted)
                .then(|| state.plan.ledger_sequence())
                .flatten()
        });
        let Some(sequence) = sequence else {
            return;
        };
        if nodes.is_empty() || peers.is_empty() {
            return;
        }
        let aggressive = timeout_count > AGGRESSIVE_TIMEOUT_THRESHOLD;
        if aggressive {
            for kind in [ledger::TreeKind::State, ledger::TreeKind::Transaction] {
                let nodes = nodes
                    .iter()
                    .filter(|node| node.kind() == kind)
                    .map(|node| LedgerNodeRequest::new(node.hash(), kind))
                    .collect::<Vec<_>>();
                if nodes.is_empty() {
                    continue;
                }
                for peer in &peers {
                    let _ = self.queue_request_intent(
                        session,
                        *peer,
                        LedgerDataRequest::GetNodes {
                            nodes: nodes.clone(),
                            sequence: Some(sequence),
                        },
                        "timeout_by_hash",
                    );
                }
            }
            return;
        }
        for kind in [ledger::TreeKind::State, ledger::TreeKind::Transaction] {
            let node_ids = nodes
                .iter()
                .filter(|node| node.kind() == kind)
                .map(|node| node.node_id())
                .collect::<Vec<_>>();
            if node_ids.is_empty() {
                continue;
            }
            for peer in &peers {
                let _ = self.queue_request_intent(
                    session,
                    *peer,
                    LedgerDataRequest::GetLedgerNodes {
                        kind,
                        node_ids: node_ids.clone(),
                        sequence,
                        query_depth: 0,
                        indirect: true,
                    },
                    "timeout_frontier",
                );
            }
        }
    }

    /// Reissues an unseeded Base/header request on an exact live session.
    ///
    /// The target and session identity never change across retries. Prefer a
    /// peer that has not received a request from this session yet, then cycle
    /// over the current availability snapshot. This models rippled's timeout
    /// trigger plus peer-set expansion without restoring the legacy peer-set
    /// lifecycle as a second owner.
    fn send_base_request(&mut self, session: SessionRef, effects: &mut Vec<AcquisitionEffect>) {
        let peers = self
            .state
            .sessions
            .get(&session)
            .filter(|state| state.phase == SessionPhase::Active && state.network_admitted)
            .map(|state| state.sent_peers.iter().copied().collect::<Vec<_>>())
            .unwrap_or_default();
        for peer in peers {
            self.send_base_request_to_peer(session, peer, effects);
        }
    }

    fn send_base_request_to_peer(
        &mut self,
        session: SessionRef,
        peer: PeerId,
        _effects: &mut Vec<AcquisitionEffect>,
    ) {
        let Some(target) = self.state.sessions.get(&session).and_then(|state| {
            (state.phase == SessionPhase::Active
                && state.network_admitted
                && state.plan.engine().is_none())
            .then_some(state.target)
        }) else {
            return;
        };
        let _ = self.queue_request_intent(
            session,
            peer,
            LedgerDataRequest::GetLedger {
                sequence: target.sequence(),
            },
            "base_retry_or_recovery",
        );
    }

    /// Derives the NodeStore read admission priority from the acquisition
    /// reason: consensus/validation/recovery demand preempts history fill.
    const fn read_priority(reason: AcquireReason) -> ReadPriority {
        match reason {
            AcquireReason::Consensus => ReadPriority::Consensus,
            AcquireReason::Generic | AcquireReason::History => ReadPriority::History,
        }
    }

    fn effective_read_priority(&self, session: SessionRef, reason: AcquireReason) -> ReadPriority {
        if self.state.recovery_anchor_session == Some(session)
            || self.state.validation_recovery_session == Some(session)
        {
            ReadPriority::Consensus
        } else {
            Self::read_priority(reason)
        }
    }

    fn live_sessions_for_hash(&self, hash: Uint256) -> Vec<SessionRef> {
        self.state
            .sessions
            .iter()
            .filter(|(session, state)| session.target_hash() == hash && !state.phase.is_terminal())
            .map(|(session, _)| *session)
            .collect()
    }

    fn cancel_all(&mut self, reason: CancelReason, effects: &mut Vec<AcquisitionEffect>) {
        let live: Vec<SessionRef> = self
            .state
            .sessions
            .iter()
            .filter(|(_, state)| !state.phase.is_terminal())
            .map(|(session, _)| *session)
            .collect();
        for session in live {
            self.cancel_session(session, reason, effects);
        }
    }

    fn cancel_session(
        &mut self,
        session: SessionRef,
        reason: CancelReason,
        effects: &mut Vec<AcquisitionEffect>,
    ) {
        let Some(session_state) = self.state.sessions.get_mut(&session) else {
            return;
        };
        if session_state.phase.is_terminal() {
            return;
        }
        let cancelled = SessionPhase::Cancelled { reason };
        if session_phase_transition(&session_state.phase, &cancelled) {
            tracing::info!(
                target: "acquisition_trace",
                event = "session_cancelled",
                run_epoch = session.run_epoch().get(),
                session_id = session.session_id().get(),
                target_hash = %session.target_hash(),
                plan_epoch = session.plan_epoch().get(),
                store_generation = session.store_generation().get(),
                ?reason,
                phase_before = ?session_state.phase,
                plan_runs = session_state.plan.runs(),
                timeout_count = session_state.plan.timeouts(),
                pending_network = session_state.plan.pending_network().len(),
                pending_reads = session_state.plan.pending_read_count(),
                read_backlog = session_state.plan.read_backlog_count(),
                persistence = session_state.plan.persistence().label(),
                "acquisition trace: session cancelled before durable completion"
            );
            session_state.phase = cancelled;
            session_state.pending_timer = None;
            session_state.pending_expiry_timer = None;
            if reason == CancelReason::Shutdown {
                session_state.plan.cancel();
            } else {
                session_state.plan.terminalize_retaining_engine();
            }
            self.release_local_scan_permit(session, effects);
            self.release_session_request_credits(session);
            self.discard_session_request_intents(session);
            self.stats.sessions_cancelled += 1;
            *self.stats.cancelled_by_reason.entry(reason).or_insert(0) += 1;
            effects.push(AcquisitionEffect::CancelSession(session));
            if reason != CancelReason::Shutdown {
                self.arm_terminal_retention(session, effects);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn default_budget_uses_the_bounded_medium_session_cap() {
        assert_eq!(super::BudgetState::default().max_sessions(), 16);
    }

    use super::*;
    use crate::TreeEngine;
    use crate::TreePlanId;
    use crate::handoff::HandoffRejectReason;
    use crate::id::{DurableHandoffId, OperationGeneration, OperationId, PlanEpoch, SessionId};
    use crate::ingress::{AdmissionGate, BackpressureOutcome};
    use crate::io::{ReadOutcome, WriteOutcome};
    use crate::plan::{PlanNetworkNeed, PlanReadNeed, ScriptedEngine, ScriptedStep};
    use basics::sha_map_hash::SHAMapHash;
    use shamap::node_id::SHAMapNodeId;
    use std::collections::VecDeque;
    use std::sync::Arc;

    fn connect(runner: &mut CoordinatorRunner) {
        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Connected)]
        );
    }

    fn acquire(runner: &mut CoordinatorRunner, seq: u32) -> SessionRef {
        let effects = acquire_with_effects(runner, seq);
        peer_request_session(&effects)
    }

    fn peer_request_session(effects: &[AcquisitionEffect]) -> SessionRef {
        effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request.session()),
                AcquisitionEffect::SubmitRead(request)
                    if request.operation().kind() == OperationKind::HeaderRead =>
                {
                    Some(request.operation().session())
                }
                _ => None,
            })
            .expect("an acquisition read or peer request must be emitted")
    }

    fn timer_operation(effects: &[AcquisitionEffect]) -> OperationRef {
        effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::ArmTimer(request) => Some(request.clone().operation()),
                _ => None,
            })
            .expect("an arm timer effect must be emitted")
    }

    fn expiry_operation(effects: &[AcquisitionEffect]) -> OperationRef {
        effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::ArmTimer(request)
                    if request.timer() == TimerKind::SessionExpiry =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("a live session expiry must be armed")
    }

    fn target(seq: u32) -> LedgerTarget {
        LedgerTarget::new(Uint256::from(u64::from(seq)), Some(seq))
    }

    fn identity(seq: u32) -> LedgerIdentity {
        LedgerIdentity::new(Uint256::from(u64::from(seq)), seq)
    }

    #[test]
    fn repeated_demand_invalidates_stale_expiry_and_global_sweep_reaps_session() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let started = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&started);
        let first_expiry = expiry_operation(&started);

        let repeated = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(10),
            reason: AcquireReason::Consensus,
        });
        let replacement_expiry = expiry_operation(&repeated);
        assert_ne!(first_expiry, replacement_expiry);

        let stale = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: first_expiry,
            timer: TimerKind::SessionExpiry,
        });
        assert!(stale.is_empty());
        assert!(runner.session(session).is_some());

        let eligible = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: replacement_expiry,
            timer: TimerKind::SessionExpiry,
        });
        assert!(eligible.is_empty());
        assert!(runner.session(session).is_some());

        // A touch just before the global sweep clears eligibility.
        let touched = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(10),
            reason: AcquireReason::Consensus,
        });
        let touched_expiry = expiry_operation(&touched);
        assert!(
            runner
                .handle_event(AcquisitionEvent::RegistrySweep)
                .is_empty()
        );
        assert!(runner.session(session).is_some());

        assert!(
            runner
                .handle_event(AcquisitionEvent::TimerFired {
                    operation: touched_expiry,
                    timer: TimerKind::SessionExpiry,
                })
                .is_empty()
        );
        let expired = runner.handle_event(AcquisitionEvent::RegistrySweep);
        assert_eq!(expired, vec![AcquisitionEffect::CancelSession(session)]);
        assert!(runner.session(session).is_none());
        assert_eq!(
            runner.snapshot().cancelled_by_reason(),
            &BTreeMap::from([(CancelReason::IdleExpired, 1)])
        );
    }

    #[test]
    fn useful_reply_after_idle_eligibility_completes_before_global_sweep() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![
                ScriptedStep::NeedsNetwork(vec![(SHAMapNodeId::default(), Uint256::from(3))]),
                ScriptedStep::Complete,
            ])),
        );
        connect(&mut runner);
        let started = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&started);
        let expiry = expiry_operation(&started);

        let frontier = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        assert!(
            frontier
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
        );
        assert!(
            runner
                .handle_event(AcquisitionEvent::TimerFired {
                    operation: expiry,
                    timer: TimerKind::SessionExpiry,
                })
                .is_empty()
        );

        let completed = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        assert!(completed.iter().any(|effect| {
            matches!(effect, AcquisitionEffect::SubmitWrite(batch) if batch.requires_fence())
        }));
        assert!(matches!(
            runner.session(session).expect("same graph owner").phase(),
            SessionPhase::Persisting
        ));
        let swept = runner.handle_event(AcquisitionEvent::RegistrySweep);
        assert!(!swept.contains(&AcquisitionEffect::CancelSession(session)));
        assert!(runner.session(session).is_some());
    }

    #[test]
    fn fresh_same_hash_demand_clears_deferred_scan_reap() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let started = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&started);
        runner.state.local_scan_owners.insert(session);
        runner.state.swept_local_scan_owners.insert(session);

        let touched = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(10),
            reason: AcquireReason::Consensus,
        });
        assert!(touched
            .iter()
            .any(|effect| matches!(effect, AcquisitionEffect::ArmTimer(request) if request.timer() == TimerKind::SessionExpiry)));
        assert!(!runner.state.swept_local_scan_owners.contains(&session));
        assert!(runner.live_sessions().any(|candidate| candidate == session));

        let mut boundary = Vec::new();
        runner.release_local_scan_at_network_boundary(session, &mut boundary);
        assert!(!boundary.contains(&AcquisitionEffect::CancelSession(session)));
        assert!(runner.session(session).is_some());
    }

    fn admitted_packet(
        session: SessionRef,
        gate_budget: AdmissionBudget,
        bytes: u64,
    ) -> AdmittedLedgerPacket {
        admitted_packet_from_peer(session, PeerId::new(1), gate_budget, bytes)
    }

    fn admitted_packet_from_peer(
        session: SessionRef,
        peer: PeerId,
        gate_budget: AdmissionBudget,
        bytes: u64,
    ) -> AdmittedLedgerPacket {
        let gate = Arc::new(AdmissionGate::new(gate_budget, session));
        let lease = match gate.try_reserve(1, bytes) {
            BackpressureOutcome::Admitted(lease) => lease,
            other => panic!("expected admission, got {other:?}"),
        };
        AdmittedLedgerPacket::new(
            lease,
            session,
            peer,
            ledger::InboundLedgerPacket::new(
                ledger::InboundLedgerDataType::Base,
                vec![ledger::InboundLedgerNodeData::new(
                    None,
                    vec![0; bytes as usize],
                )],
            ),
        )
        .expect("matching lease must admit")
    }

    #[test]
    fn connectivity_establishes_connected_then_demotes_to_disconnected() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        assert_eq!(runner.phase(), &SyncPhase::Disconnected);

        // An empty snapshot changes nothing.
        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));
        assert!(effects.is_empty());
        assert_eq!(runner.phase(), &SyncPhase::Disconnected);

        // A usable peer promotes Disconnected -> Connected.
        connect(&mut runner);

        // An unchanged snapshot changes nothing.
        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        assert!(effects.is_empty());
        assert_eq!(runner.phase(), &SyncPhase::Connected);
    }

    #[test]
    fn startup_mode_seeds_and_republishes_the_initial_phase() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));

        // Networked startup intent seeds Connected before any peer capability
        // exists and publishes it through the phase port.
        let effects = runner.handle_event(AcquisitionEvent::StartupMode {
            phase: SyncPhase::Connected,
        });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Connected)]
        );
        assert_eq!(runner.phase(), &SyncPhase::Connected);

        // Repeating the same seed is a no-op.
        let effects = runner.handle_event(AcquisitionEvent::StartupMode {
            phase: SyncPhase::Connected,
        });
        assert!(effects.is_empty());
        assert_eq!(runner.phase(), &SyncPhase::Connected);

        // A different seed re-publishes the new phase without touching state.
        let effects = runner.handle_event(AcquisitionEvent::StartupMode {
            phase: SyncPhase::Full {
                lcl: identity(5),
                published: identity(5),
            },
        });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Full {
                lcl: identity(5),
                published: identity(5),
            })]
        );
        assert_eq!(runner.snapshot().session_count(), 0);
        assert_eq!(runner.snapshot().rejected_events(), 0);
    }

    #[test]
    fn startup_mode_seed_is_not_a_transition_and_never_mints_a_session() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));

        // A start_valid seed lands on Full directly, as the legacy bootstrap
        // write did, without any transition-table fact or session mint.
        let effects = runner.handle_event(AcquisitionEvent::StartupMode {
            phase: SyncPhase::Full {
                lcl: identity(5),
                published: identity(5),
            },
        });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Full {
                lcl: identity(5),
                published: identity(5),
            })]
        );
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl: identity(5),
                published: identity(5)
            }
        );
        assert_eq!(runner.snapshot().session_count(), 0);
        assert_eq!(runner.snapshot().rejected_events(), 0);
    }

    #[test]
    fn peer_loss_demotes_but_preserves_active_and_persisting_session_resources() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::Complete])),
        );
        connect(&mut runner);
        let persisting = acquire(&mut runner, 10);
        let persist_effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(
            admitted_packet(persisting, AdmissionBudget::new(1, 256), 8),
        ));
        assert!(matches!(
            runner
                .session(persisting)
                .expect("persisting session")
                .phase(),
            SessionPhase::Persisting
        ));
        assert!(persist_effects.iter().any(|effect| {
            matches!(effect, AcquisitionEffect::SubmitWrite(batch) if batch.requires_fence())
        }));

        let active_effects = acquire_with_effects(&mut runner, 11);
        let active = peer_request_session(&active_effects);
        let _active_timer = timer_operation(&active_effects);
        let _ = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            active,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let active_packets = runner
            .session(active)
            .expect("active session")
            .packet_count();
        let active_plan_runs = runner
            .session(active)
            .expect("active session")
            .plan()
            .runs();
        assert!(
            runner
                .session(active)
                .expect("active session")
                .plan()
                .engine()
                .is_some()
        );

        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Disconnected)]
        );
        assert_eq!(runner.phase(), &SyncPhase::Disconnected);
        assert!(matches!(
            runner.session(active).expect("active session").phase(),
            SessionPhase::Active
        ));
        assert_eq!(
            runner
                .session(active)
                .expect("active session")
                .packet_count(),
            active_packets
        );
        assert_eq!(
            runner
                .session(active)
                .expect("active session")
                .plan()
                .runs(),
            active_plan_runs
        );
        assert!(
            runner
                .session(active)
                .expect("active session")
                .plan()
                .engine()
                .is_some()
        );
        assert_eq!(
            runner
                .session(active)
                .expect("active session")
                .pending_timer(),
            None,
            "peer loss pauses active acquisition timers without cancelling the session"
        );
        assert!(matches!(
            runner
                .session(persisting)
                .expect("persisting session")
                .phase(),
            SessionPhase::Persisting
        ));
        assert_eq!(
            runner
                .session(persisting)
                .expect("persisting session")
                .pending_timer(),
            None,
            "the final write/fence boundary invalidates the Active acquisition deadline"
        );
        assert_eq!(runner.live_sessions().collect::<Vec<_>>(), vec![active]);
        assert_eq!(runner.snapshot().sessions_cancelled(), 0);
    }

    #[test]
    fn peerless_acquire_timeout_is_paused_without_consuming_plan_budget_or_dispatching_work() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let initial = preferred_with_effects(&mut runner, 10);
        let session = peer_request_session(&initial);
        let timer = timer_operation(&initial);
        let (timeouts, plan_turns, peer_requests) = (
            runner
                .session(session)
                .expect("live session")
                .plan()
                .timeouts(),
            runner.snapshot().plan_turns(),
            runner.snapshot().peer_requests(),
        );
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));

        // Peer loss invalidates only the expected deadline operation. The
        // queued wakeup is stale, produces no rearm, and cannot spend timeout
        // budget while the session waits for a recovery grant.
        let effects = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: timer,
            timer: TimerKind::AcquireTimeout,
        });
        assert!(effects.is_empty());
        assert_eq!(
            runner
                .session(session)
                .expect("live session")
                .plan()
                .timeouts(),
            timeouts
        );
        assert_eq!(runner.snapshot().plan_turns(), plan_turns);
        assert_eq!(runner.snapshot().peer_requests(), peer_requests);
        assert_eq!(
            runner
                .session(session)
                .expect("live session")
                .pending_timer(),
            None
        );
    }

    #[test]
    fn peer_recovery_reconciles_and_resumes_seeded_frontier_on_the_same_session() {
        let node = PlanNetworkNeed::new(
            SHAMapNodeId::default(),
            Uint256::from(0x77),
            ledger::TreeKind::Transaction,
        );
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsNetworkWithKind(
                vec![node],
            )])),
        );
        connect(&mut runner);
        let initial = preferred_with_effects(&mut runner, 10);
        let session = peer_request_session(&initial);
        let initial_timer = timer_operation(&initial);
        let timeout_budget = runner
            .session(session)
            .expect("live session")
            .plan()
            .timeouts();
        let _ = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));

        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(2), PeerId::new(3)]),
        ));
        assert!(effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Connected)));
        assert!(
            effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                target: target(10)
            }))
        );
        assert!(effects.iter().all(|effect| {
            !matches!(
                effect,
                AcquisitionEffect::SessionStarted(_) | AcquisitionEffect::CancelSession(_)
            )
        }));
        let recovery_timer = timer_operation(&effects);
        let reads = read_effects(&effects);
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].operation().session(), session);
        let resumed = effects
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(resumed.len(), 1);
        assert!(resumed.iter().all(|request| {
            request.session() == session
                && request.peer_id() == PeerId::new(2)
                && matches!(request.request(), LedgerDataRequest::GetLedgerNodes { .. })
        }));
        assert_eq!(
            runner
                .session(session)
                .expect("resumed session")
                .sent_peers(),
            &BTreeSet::from([PeerId::new(2)])
        );
        assert_eq!(runner.snapshot().session_count(), 1);
        assert_eq!(runner.snapshot().sessions_started(), 1);
        assert_eq!(
            runner
                .session(session)
                .expect("resumed session")
                .pending_timer(),
            Some((TimerKind::AcquireTimeout, recovery_timer))
        );
        assert_ne!(recovery_timer, initial_timer);
        assert_eq!(
            runner
                .session(session)
                .expect("resumed session")
                .plan()
                .timeouts(),
            timeout_budget
        );
    }

    #[test]
    fn peer_recovery_resumes_unseeded_base_on_the_same_session() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let initial = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&initial);
        let initial_timer = timer_operation(&initial);
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));

        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(2)]),
        ));
        let resumed = effects
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(resumed.len(), 1);
        assert_eq!(resumed[0].session(), session);
        assert_eq!(resumed[0].peer_id(), PeerId::new(2));
        assert_eq!(
            resumed[0].request(),
            &LedgerDataRequest::GetLedger { sequence: Some(10) }
        );
        assert!(effects.iter().all(|effect| {
            !matches!(
                effect,
                AcquisitionEffect::SessionStarted(_) | AcquisitionEffect::CancelSession(_)
            )
        }));
        let recovery_timer = timer_operation(&effects);
        assert_eq!(runner.snapshot().session_count(), 1);
        assert_eq!(runner.snapshot().sessions_started(), 1);
        assert_eq!(
            runner
                .session(session)
                .expect("resumed session")
                .pending_timer(),
            Some((TimerKind::AcquireTimeout, recovery_timer))
        );
        assert_ne!(recovery_timer, initial_timer);
    }

    #[test]
    fn peer_recovery_resumes_all_retained_hashes_through_one_available_peer() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let sessions = (1..=16)
            .map(|sequence| peer_request_session(&preferred_with_effects(&mut runner, sequence)))
            .collect::<Vec<_>>();
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));

        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(9)]),
        ));
        let requests = effects
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(requests.len(), 16);
        assert!(
            requests
                .iter()
                .all(|request| request.peer_id() == PeerId::new(9))
        );
        assert_eq!(
            requests
                .iter()
                .map(|request| request.session())
                .collect::<BTreeSet<_>>(),
            sessions.iter().copied().collect::<BTreeSet<_>>()
        );
        assert_eq!(runner.snapshot().session_count(), 16);
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(1) });
        for session in sessions {
            let state = runner.session(session).expect("retained session");
            assert_eq!(state.phase(), &SessionPhase::Active);
            assert!(state.network_admitted);
            assert!(state.pending_timer().is_some());
        }
    }

    #[test]
    fn peer_recovery_prioritizes_consensus_before_generic() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let generic = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(1),
            reason: AcquireReason::Generic,
        });
        let generic_session = peer_request_session(&generic);
        let consensus_session = peer_request_session(&preferred_with_effects(&mut runner, 2));
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));

        let recovered = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(9)]),
        ));
        let request = recovered
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .expect("one recovery grant");
        assert_eq!(request.session(), consensus_session);
        assert_ne!(request.session(), generic_session);
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(2) });
    }

    #[test]
    fn peer_recovery_keeps_the_latched_consensus_anchor_over_moving_targets() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let earliest_session = peer_request_session(&preferred_with_effects(&mut runner, 1));
        let _ = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(100),
            reason: AcquireReason::Generic,
        });
        let latest_session = peer_request_session(&preferred_with_effects(&mut runner, 2));
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));

        let recovered = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(9)]),
        ));
        let request = recovered
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .expect("one recovery grant");
        assert_eq!(request.session(), earliest_session);
        assert_ne!(request.session(), latest_session);
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(1) });
    }

    #[test]
    fn peer_recovery_prioritizes_the_latest_consensus_fact_after_coalescing() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let first_session = peer_request_session(&acquire_with_effects(&mut runner, 1));
        let newer_session = peer_request_session(&acquire_with_effects(&mut runner, 2));

        // The latest preferred target is an exact duplicate of the older
        // session. It coalesces without cancellation, but its newer consensus
        // fact must outrank the later-created target during scarce recovery.
        let coalesced = runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(target(1), AcquireReason::Consensus),
        ));
        assert!(coalesced.iter().all(|effect| {
            !matches!(
                effect,
                AcquisitionEffect::CancelSession(_) | AcquisitionEffect::SendLedgerRequest(_)
            )
        }));
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));

        let recovered = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(9)]),
        ));
        let request = recovered
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .expect("one recovery grant");
        assert_eq!(request.session(), first_session);
        assert_ne!(request.session(), newer_session);
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(1) });
        assert!(
            recovered
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::CancelSession(_)))
        );
    }

    #[test]
    fn acquire_from_connected_emits_peer_request_and_timer() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);

        let effects = acquire_with_effects(&mut runner, 9);
        assert!(
            effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                target: target(9)
            }))
        );

        let request = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .expect("a peer request effect must be emitted");
        assert_eq!(request.peer_id(), PeerId::new(1));
        assert_eq!(
            request.request(),
            &LedgerDataRequest::GetLedger { sequence: Some(9) }
        );
        let session = request.session();
        assert_eq!(session.target_hash(), Uint256::from(9));
        assert_eq!(session.run_epoch(), RunEpoch::new(1));

        let timer = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::ArmTimer(request) => Some(request),
                _ => None,
            })
            .expect("an arm timer effect must be emitted");
        assert_eq!(timer.clone().timer(), TimerKind::AcquireTimeout);
        assert_eq!(timer.clone().operation().session(), session);

        assert_eq!(
            runner.session(session).expect("live session").phase(),
            &SessionPhase::Active
        );
        let snapshot = runner.snapshot();
        assert_eq!(
            snapshot.active_by_reason().get(&AcquireReason::Consensus),
            Some(&1)
        );
        assert_eq!(snapshot.peer_requests(), 1);
        assert_eq!(snapshot.timers_armed(), 1);
        assert_eq!(snapshot.session_count(), 1);
    }

    #[test]
    fn acquire_while_disconnected_replays_exactly_once_when_peers_return() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        let target = target(10);

        let deferred = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target,
            reason: AcquireReason::Consensus,
        });
        assert!(deferred.is_empty());
        assert_eq!(runner.phase(), &SyncPhase::Disconnected);
        assert_eq!(runner.snapshot().session_count(), 0);
        assert_eq!(runner.snapshot().rejected_events(), 0);

        // rippled's heartbeat resumes acquisition-demand processing after peer
        // capability returns (NetworkOPs.cpp:1230-1301); a resolver miss is
        // then routed through InboundLedgers::acquire
        // (LedgerMaster.cpp:886-916). Keep the exact demand on this sole
        // coordinator owner until the capability fact arrives.
        let mut replay = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        if let Some(operation) = replay.iter().find_map(|effect| match effect {
            AcquisitionEffect::SubmitRead(request)
                if request.operation().kind() == OperationKind::HeaderRead =>
            {
                Some(request.operation())
            }
            _ => None,
        }) {
            replay.extend(runner.handle_event(AcquisitionEvent::ReadCompleted(
                ReadCompletion::new(operation, ReadOutcome::Settled { node: None }),
            )));
        }
        assert_eq!(
            replay
                .iter()
                .filter(|effect| matches!(effect, AcquisitionEffect::SetServicePhase(_)))
                .count(),
            2,
            "reconnect must publish Connected then Syncing"
        );
        assert!(
            replay.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                target
            }))
        );
        let session = peer_request_session(&replay);
        let session_started_at = replay
            .iter()
            .position(|effect| matches!(effect, AcquisitionEffect::SessionStarted(started) if *started == session))
            .expect("replay must bind the exact session before dispatch");
        let request_at = replay
            .iter()
            .position(|effect| matches!(effect, AcquisitionEffect::SendLedgerRequest(request) if request.session() == session))
            .expect("replay must emit one peer request");
        assert!(session_started_at < request_at);
        assert_eq!(session.target_hash(), target.hash());
        assert_eq!(
            replay
                .iter()
                .filter(|effect| matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
                .count(),
            1
        );
        assert_eq!(
            replay
                .iter()
                .filter(|effect| matches!(
                    effect,
                    AcquisitionEffect::ArmTimer(request)
                        if request.timer() == TimerKind::AcquireTimeout
                            && request.operation().session() == session
                ))
                .count(),
            1
        );
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target });
        assert_eq!(runner.snapshot().session_count(), 1);
        assert_eq!(runner.snapshot().peer_requests(), 1);
        assert_eq!(runner.snapshot().timers_armed(), 1);

        let duplicate_connectivity = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        assert!(duplicate_connectivity.is_empty());
        assert_eq!(runner.snapshot().session_count(), 1);
        assert_eq!(runner.snapshot().peer_requests(), 1);
        assert_eq!(runner.snapshot().timers_armed(), 1);
    }

    #[test]
    fn peerless_moving_preferred_keeps_exact_unbound_anchor_replayable() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        let old_ordinary = target(40);
        let latest_ordinary = target(41);
        let old_preferred = target(50);
        let latest_preferred = target(51);

        let _ = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: old_ordinary,
            reason: AcquireReason::History,
        });
        let _ = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: latest_ordinary,
            reason: AcquireReason::Generic,
        });
        let _ = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            old_preferred,
            AcquireReason::Consensus,
        )));
        let _ = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            latest_preferred,
            AcquireReason::Consensus,
        )));

        assert_eq!(
            runner.state.deferred_acquires.len(),
            MAX_DEFERRED_PEERLESS_ACQUIRES
        );
        assert!(!runner.state.deferred_acquires.contains_key(&old_ordinary));
        assert!(runner.state.deferred_acquires.contains_key(&old_preferred));
        assert_eq!(
            runner.state.deferred_acquires.get(&latest_ordinary),
            Some(&(AcquireReason::Generic, false, false))
        );
        assert_eq!(
            runner.state.deferred_acquires.get(&old_preferred),
            Some(&(AcquireReason::Consensus, true, false))
        );
        assert!(
            !runner
                .state
                .deferred_acquires
                .contains_key(&latest_preferred)
        );
        assert_eq!(runner.state.recovery_anchor_target, Some(old_preferred));
        assert_eq!(runner.state.latest_consensus_target, Some(latest_preferred));

        let resumed = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        let started = resumed
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(session.target_hash()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            started,
            BTreeSet::from([latest_ordinary.hash(), old_preferred.hash()])
        );
        assert!(runner.state.deferred_acquires.is_empty());
        assert_eq!(
            runner.phase(),
            &SyncPhase::Syncing {
                target: old_preferred
            }
        );
    }

    #[test]
    fn consensus_target_creates_a_consensus_session() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            target(5),
            AcquireReason::Consensus,
        )));
        let session = peer_request_session(&effects);
        assert_eq!(
            runner.session(session).expect("live session").reason(),
            AcquireReason::Consensus
        );
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(5) });
    }

    #[test]
    fn completed_hash_is_reused_until_terminal_retention_expires() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let completed = target(6);
        let session =
            peer_request_session(&runner.handle_event(AcquisitionEvent::AcquireRequested {
                target: completed,
                reason: AcquireReason::Generic,
            }));
        runner
            .state
            .sessions
            .get_mut(&session)
            .expect("completed session")
            .phase = SessionPhase::Complete;
        let mut retention_effects = Vec::new();
        runner.arm_terminal_retention(session, &mut retention_effects);
        let retention = runner
            .session(session)
            .expect("completed tombstone")
            .pending_timer()
            .expect("terminal retention timer")
            .1;
        let sessions_before = runner.state.sessions.len();

        for event in [
            AcquisitionEvent::AcquireRequested {
                target: completed,
                reason: AcquireReason::Generic,
            },
            AcquisitionEvent::ValidationTarget(completed),
            AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
                completed,
                AcquireReason::Consensus,
            )),
        ] {
            let effects = runner.handle_event(event);
            assert!(effects.iter().all(|effect| !matches!(
                effect,
                AcquisitionEffect::SessionStarted(_) | AcquisitionEffect::SendLedgerRequest(_)
            )));
            assert_eq!(runner.state.sessions.len(), sessions_before);
        }

        let retained_retry = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: retention,
            timer: TimerKind::TerminalRetention,
        });
        assert!(runner.session(session).is_none());
        assert!(
            retained_retry
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SessionStarted(_)))
        );
        assert_eq!(runner.state.validation_recovery_target, None);

        let fresh = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: completed,
            reason: AcquireReason::Generic,
        });
        assert!(
            fresh
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SessionStarted(_)))
        );
    }

    #[test]
    fn terminal_preferred_target_keeps_phase_ownership_until_lcl_install() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let preferred = target(10);
        let session =
            peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
                ConsensusTarget::new(preferred, AcquireReason::Consensus),
            )));
        // Model the post-handoff-ack interval: the acquisition is terminal but
        // its exact target intentionally remains authoritative until
        // NetworkOps reports LclInstalled.
        runner
            .state
            .sessions
            .get_mut(&session)
            .expect("preferred session")
            .phase = SessionPhase::Complete;
        assert_eq!(runner.state.latest_consensus_target, Some(preferred));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: preferred });

        for (target, reason) in [
            (target(20), AcquireReason::Consensus),
            (target(30), AcquireReason::Generic),
        ] {
            let effects =
                runner.handle_event(AcquisitionEvent::AcquireRequested { target, reason });
            assert!(effects.iter().all(|effect| !matches!(
                effect,
                AcquisitionEffect::SetServicePhase(SyncPhase::Syncing { target })
                    if *target != preferred
            )));
            assert_eq!(runner.phase(), &SyncPhase::Syncing { target: preferred });
        }

        let installed = LedgerIdentity::new(preferred.hash(), 10);
        let effects = runner.handle_event(AcquisitionEvent::LclInstalled(installed));
        assert!(
            effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Tracking {
                lcl: installed,
            }))
        );
        assert_eq!(runner.state.latest_consensus_target, None);
        assert_eq!(runner.phase(), &SyncPhase::Tracking { lcl: installed });
    }

    #[test]
    fn ordinary_consensus_request_coalesces_without_changing_preferred_policy() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let old = peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(target(10), AcquireReason::Consensus),
        )));
        let current =
            peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
                ConsensusTarget::new(target(20), AcquireReason::Consensus),
            )));
        assert_eq!(
            runner.session(old).expect("old session").phase(),
            &SessionPhase::Active
        );
        assert_eq!(
            runner.session(current).expect("current session").phase(),
            &SessionPhase::Active
        );

        let coalesced = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(20),
            reason: AcquireReason::Consensus,
        });
        assert!(coalesced.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::SessionStarted(_) | AcquisitionEffect::CancelSession(_)
        )));
        assert_eq!(
            runner.session(current).expect("current session").phase(),
            &SessionPhase::Active
        );

        let effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(10),
            reason: AcquireReason::Consensus,
        });
        assert!(effects.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::SessionStarted(_) | AcquisitionEffect::CancelSession(_)
        )));
        assert_eq!(runner.state.latest_consensus_target, Some(target(20)));
        assert_eq!(
            runner.phase(),
            &SyncPhase::Syncing { target: target(10) },
            "moving preferred policy must not replace the recoverable anchor"
        );
        assert_eq!(
            runner.session(old).expect("old session").phase(),
            &SessionPhase::Active
        );
        assert_eq!(
            runner.session(current).expect("current session").phase(),
            &SessionPhase::Active
        );
    }

    #[test]
    fn ordinary_consensus_demand_runs_concurrently_without_replacing_preferred_policy() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let preferred =
            peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
                ConsensusTarget::new(target(20), AcquireReason::Consensus),
            )));

        let effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(10),
            reason: AcquireReason::Consensus,
        });
        let retained = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("ordinary consensus demand is retained");

        assert!(
            effects
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::CancelSession(_)))
        );
        assert_eq!(runner.state.latest_consensus_target, Some(target(20)));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(20) });
        assert_eq!(
            runner
                .session(preferred)
                .expect("preferred session")
                .phase(),
            &SessionPhase::Active
        );
        assert_eq!(
            runner.session(retained).expect("retained session").phase(),
            &SessionPhase::Active
        );
    }

    #[test]
    fn startup_consensus_demands_advance_as_concurrent_per_hash_acquisitions() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let first =
            peer_request_session(&runner.handle_event(AcquisitionEvent::AcquireRequested {
                target: target(10),
                reason: AcquireReason::Consensus,
            }));

        let effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(20),
            reason: AcquireReason::Consensus,
        });
        let second = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("later startup demand starts its own hash acquisition");

        assert_eq!(runner.state.latest_consensus_target, None);
        assert_eq!(
            runner.session(first).expect("first session").phase(),
            &SessionPhase::Active
        );
        assert_eq!(
            runner.session(second).expect("second session").phase(),
            &SessionPhase::Active
        );
        assert!(effects.iter().any(|effect| matches!(
            effect,
            AcquisitionEffect::SubmitRead(request) if request.operation().session() == second
                && request.operation().kind() == OperationKind::HeaderRead
        )));
        assert!(effects.iter().any(|effect| matches!(
            effect,
            AcquisitionEffect::ArmTimer(timer) if timer.operation().session() == second
        )));
        assert_eq!(
            runner
                .snapshot()
                .active_by_reason()
                .get(&AcquireReason::Consensus),
            Some(&2)
        );
    }

    #[test]
    fn new_consensus_targets_run_concurrently_behind_a_stable_recovery_anchor() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsNetwork(
                (100..140)
                    .map(|hash| (SHAMapNodeId::default(), Uint256::from(hash)))
                    .collect(),
            )])),
        );
        connect(&mut runner);
        let first_target = LedgerTarget::new(Uint256::from(10), None);
        let second_target = LedgerTarget::new(Uint256::from(20), None);
        let newest_target = LedgerTarget::new(Uint256::from(30), None);
        let active = peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(first_target, AcquireReason::Consensus),
        )));
        let _ = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            active,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let second = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            second_target,
            AcquireReason::Consensus,
        )));
        let newest = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            newest_target,
            AcquireReason::Consensus,
        )));

        let second_session = peer_request_session(&second);
        let newest_session = peer_request_session(&newest);
        assert_eq!(runner.state.latest_consensus_target, Some(newest_target));
        assert_eq!(runner.state.deferred_consensus_acquire, None);
        assert_eq!(
            runner.phase(),
            &SyncPhase::Syncing {
                target: first_target
            }
        );
        assert_eq!(
            runner.session(active).expect("stable owner").phase(),
            &SessionPhase::Active
        );
        assert_eq!(runner.snapshot().session_count(), 3);
        assert_eq!(
            runner.session(second_session).expect("second").phase(),
            &SessionPhase::Active
        );
        assert_eq!(
            runner.session(newest_session).expect("newest").phase(),
            &SessionPhase::Active
        );
        assert_eq!(
            runner.recovery_priority_rank(
                active,
                runner.session(active).expect("latched P0 session"),
            ),
            0,
            "the exact recovery anchor receives request priority"
        );
        assert_eq!(
            runner.recovery_priority_rank(
                newest_session,
                runner
                    .session(newest_session)
                    .expect("moving policy session"),
            ),
            1,
            "a moving policy target cannot preempt the latched owner"
        );
    }

    #[test]
    fn recovery_anchor_survives_mode_oscillation_until_exact_installation() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let anchor_target = target(10);
        let next_target = target(11);
        let validation_target = target(12);
        let anchor = peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(anchor_target, AcquireReason::Consensus),
        )));
        let next = peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(next_target, AcquireReason::Consensus),
        )));
        let validation = peer_request_session(
            &runner.handle_event(AcquisitionEvent::ValidationTarget(validation_target)),
        );
        let next_expiry = runner
            .session(next)
            .expect("moving consensus session")
            .pending_expiry_timer();
        let validation_expiry = runner
            .session(validation)
            .expect("validation session")
            .pending_expiry_timer();

        for phase in [
            SyncPhase::Full {
                lcl: identity(9),
                published: identity(9),
            },
            SyncPhase::Tracking { lcl: identity(9) },
            SyncPhase::Connected,
        ] {
            runner.state.phase = phase;
            let effects = runner.handle_event(AcquisitionEvent::Heartbeat);
            assert!(
                effects
                    .iter()
                    .all(|effect| !matches!(effect, AcquisitionEffect::CancelSession(_)))
            );
            assert_eq!(
                runner.phase(),
                &SyncPhase::Syncing {
                    target: anchor_target
                }
            );
            assert_eq!(runner.state.recovery_anchor_session, Some(anchor));
            assert!(runner.request_intent_is_p0(&RequestIntent {
                session: anchor,
                peer: PeerId::new(1),
                request: LedgerDataRequest::GetLedger { sequence: Some(10) },
            }));
            assert!(!runner.request_intent_is_p0(&RequestIntent {
                session: next,
                peer: PeerId::new(1),
                request: LedgerDataRequest::GetLedger { sequence: Some(11) },
            }));
            assert!(!runner.request_intent_is_p0(&RequestIntent {
                session: validation,
                peer: PeerId::new(1),
                request: LedgerDataRequest::GetLedger { sequence: Some(12) },
            }));
        }
        assert_eq!(
            runner
                .session(next)
                .expect("moving consensus survives")
                .pending_expiry_timer(),
            next_expiry
        );
        assert_eq!(
            runner
                .session(validation)
                .expect("validation survives")
                .pending_expiry_timer(),
            validation_expiry
        );

        let effects = runner.handle_event(AcquisitionEvent::LclInstalled(identity(10)));
        assert!(effects.contains(&AcquisitionEffect::CancelSession(anchor)));
        assert_eq!(runner.state.recovery_anchor_target, None);
        assert_eq!(runner.state.recovery_anchor_session, None);
        assert_eq!(runner.phase(), &SyncPhase::Tracking { lcl: identity(10) });
        assert!(runner.session(validation).is_some());
    }

    #[test]
    fn pending_divergence_anchor_binds_only_its_matching_session() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let anchor_target = target(9);
        let _ = runner.handle_event(AcquisitionEvent::PreferredLclDivergence {
            target: anchor_target,
        });
        assert_eq!(runner.state.recovery_anchor_target, Some(anchor_target));
        assert_eq!(runner.state.recovery_anchor_session, None);

        let validation = peer_request_session(
            &runner.handle_event(AcquisitionEvent::ValidationTarget(target(99))),
        );
        let moving = peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(target(10), AcquireReason::Consensus),
        )));
        assert_eq!(runner.state.recovery_anchor_target, Some(anchor_target));
        assert_eq!(runner.state.recovery_anchor_session, None);

        let anchor =
            peer_request_session(&runner.handle_event(AcquisitionEvent::AcquireRequested {
                target: anchor_target,
                reason: AcquireReason::Consensus,
            }));
        assert_eq!(runner.state.recovery_anchor_session, Some(anchor));
        assert_eq!(
            runner.phase(),
            &SyncPhase::Syncing {
                target: anchor_target
            }
        );
        assert!(runner.session(validation).is_some());
        assert!(runner.session(moving).is_some());
    }

    #[test]
    fn nonmatching_lcl_and_publication_cannot_escape_live_anchor_syncing() {
        let full = SyncPhase::Full {
            lcl: identity(1),
            published: identity(1),
        };
        let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), full);
        let anchor_target = target(10);
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        let _ = runner.handle_event(AcquisitionEvent::PreferredLclDivergence {
            target: anchor_target,
        });
        let anchor = peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(anchor_target, AcquireReason::Consensus),
        )));
        assert_eq!(
            runner.phase(),
            &SyncPhase::Syncing {
                target: anchor_target
            }
        );

        let lcl_effects = runner.handle_event(AcquisitionEvent::LclInstalled(identity(2)));
        assert!(lcl_effects
            .iter()
            .all(|effect| !matches!(effect, AcquisitionEffect::CancelSession(session) if *session == anchor)));
        assert_eq!(
            runner.phase(),
            &SyncPhase::Syncing {
                target: anchor_target
            }
        );
        let publication_effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(2),
            fresh: true,
        });
        assert!(publication_effects.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::SetServicePhase(SyncPhase::Full { .. })
        )));
        assert_eq!(
            runner.phase(),
            &SyncPhase::Syncing {
                target: anchor_target
            }
        );
        assert_eq!(runner.state.recovery_anchor_session, Some(anchor));
    }

    #[test]
    fn preferred_lcl_divergence_demotes_full_and_tracking_to_syncing_without_a_session() {
        for phase in [
            SyncPhase::Full {
                lcl: identity(1),
                published: identity(1),
            },
            SyncPhase::Tracking { lcl: identity(1) },
            SyncPhase::Connected,
        ] {
            let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), phase);
            let effects =
                runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: target(9) });
            assert_eq!(
                runner.phase(),
                &SyncPhase::Syncing { target: target(9) },
                "phase {:?} must demote to Syncing",
                phase
            );
            assert_eq!(
                effects,
                vec![AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                    target: target(9)
                })]
            );
            // The divergence fact never mints a session: the acquisition demand
            // arrives as a separate AcquireRequested fact.
            assert_eq!(runner.snapshot().session_count(), 0);
        }
    }

    #[test]
    fn consensus_view_change_demotes_full_and_tracking_without_pinning_a_target() {
        for phase in [
            SyncPhase::Full {
                lcl: identity(1),
                published: identity(1),
            },
            SyncPhase::Tracking { lcl: identity(1) },
        ] {
            let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), phase);
            let effects = runner.handle_event(AcquisitionEvent::ConsensusViewChange);
            assert_eq!(runner.phase(), &SyncPhase::Connected);
            assert_eq!(
                effects,
                vec![AcquisitionEffect::SetServicePhase(SyncPhase::Connected)]
            );
            assert_eq!(runner.snapshot().session_count(), 0);
            assert_eq!(runner.state.latest_consensus_target, None);
        }
    }

    #[test]
    fn consensus_quorum_loss_changes_mode_without_discarding_transport_or_sessions() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let _ = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(9),
            reason: AcquireReason::Consensus,
        });
        let sessions = runner.snapshot().session_count();
        let peers = runner.snapshot().peer_count();

        let effects = runner.handle_event(AcquisitionEvent::ConsensusQuorumLost);
        assert_eq!(runner.phase(), &SyncPhase::Disconnected);
        assert_eq!(runner.snapshot().peer_count(), peers);
        assert_eq!(runner.snapshot().session_count(), sessions);
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Disconnected)]
        );

        let effects = runner.handle_event(AcquisitionEvent::ConsensusQuorumAvailable);
        assert_eq!(runner.phase(), &SyncPhase::Connected);
        assert_eq!(runner.snapshot().peer_count(), peers);
        assert_eq!(runner.snapshot().session_count(), sessions);
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Connected)]
        );
    }

    #[test]
    fn below_quorum_connectivity_heartbeats_do_not_republish_connected() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));

        assert!(
            runner
                .handle_event(AcquisitionEvent::ConsensusQuorumLost)
                .is_empty()
        );
        for _ in 0..2 {
            assert!(
                runner
                    .handle_event(AcquisitionEvent::Connectivity(
                        PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
                    ))
                    .is_empty()
            );
            assert_eq!(runner.phase(), &SyncPhase::Disconnected);
            assert_eq!(runner.snapshot().peer_count(), 1);
        }

        let effects = runner.handle_event(AcquisitionEvent::ConsensusQuorumAvailable);
        assert_eq!(runner.phase(), &SyncPhase::Connected);
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Connected)]
        );
    }

    #[test]
    fn quorum_available_defensively_recovers_after_transport_disconnect() {
        let lcl = identity(9);
        let mut runner = CoordinatorRunner::with_phase(
            RunEpoch::new(1),
            SyncPhase::Full {
                lcl,
                published: lcl,
            },
        );

        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(Vec::new()),
        ));
        assert_eq!(runner.phase(), &SyncPhase::Disconnected);
        assert_eq!(runner.snapshot().peer_count(), 0);
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Disconnected)]
        );

        // Keep recovery defensive if adapters ever deliver phase-bearing
        // transport loss and quorum availability out of order. The normal
        // start-valid heartbeat uses phase-neutral TransportConnectivity.
        let effects = runner.handle_event(AcquisitionEvent::ConsensusQuorumAvailable);
        assert_eq!(runner.phase(), &SyncPhase::Connected);
        assert_eq!(runner.snapshot().peer_count(), 0);
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Connected)]
        );

        assert!(
            runner
                .handle_event(AcquisitionEvent::Connectivity(
                    PeerAvailabilitySnapshot::new(Vec::new()),
                ))
                .is_empty()
        );
        assert_eq!(runner.phase(), &SyncPhase::Connected);
    }

    #[test]
    fn phase_neutral_transport_loss_pauses_and_recovers_full_session() {
        let lcl = identity(9);
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let _ = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(10),
            reason: AcquireReason::Generic,
        });
        // Model a session that remains active when later publication promotes
        // the service. Transport membership must not undo that Full phase.
        runner.state.phase = SyncPhase::Full {
            lcl,
            published: lcl,
        };
        let sessions = runner.snapshot().session_count();
        assert_eq!(sessions, 1);
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl,
                published: lcl
            }
        );

        let lost = runner.handle_event(AcquisitionEvent::TransportConnectivity(
            PeerAvailabilitySnapshot::new(Vec::new()),
        ));
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl,
                published: lcl
            }
        );
        assert_eq!(runner.snapshot().peer_count(), 0);
        assert_eq!(runner.snapshot().session_count(), sessions);
        assert!(
            !lost
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
        );

        let recovered = runner.handle_event(AcquisitionEvent::TransportConnectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl,
                published: lcl
            }
        );
        assert_eq!(runner.snapshot().peer_count(), 1);
        assert_eq!(runner.snapshot().session_count(), sessions);
        assert!(
            recovered
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
        );
        assert!(
            !recovered
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SetServicePhase(_)))
        );
    }

    #[test]
    fn preferred_lcl_divergence_does_not_mint_a_session_for_a_resident_switch() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let effects =
            runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: target(9) });
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(9) });
        assert!(
            !effects
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
        );
        assert_eq!(runner.snapshot().peer_requests(), 0);
        assert_eq!(runner.snapshot().session_count(), 0);
    }

    #[test]
    fn preferred_lcl_divergence_without_latch_uses_explicit_target() {
        let mut runner = CoordinatorRunner::with_phase(
            RunEpoch::new(1),
            SyncPhase::Syncing { target: target(1) },
        );
        let effects =
            runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: target(9) });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                target: target(9),
            })]
        );
        assert_eq!(runner.state.recovery_anchor_target, Some(target(9)));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(9) });
        assert_eq!(runner.snapshot().rejected_events(), 0);
    }

    #[test]
    fn moving_consensus_policy_preserves_anchor_until_it_is_installed() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let anchor = target(10);
        let latest = target(12);

        let _ = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            anchor,
            AcquireReason::Consensus,
        )));
        let effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            latest,
            AcquireReason::Consensus,
        )));

        assert_eq!(runner.state.latest_consensus_target, Some(latest));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: anchor });
        assert!(effects.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::SetServicePhase(SyncPhase::Syncing { target })
                if *target == latest
        )));

        let installed = LedgerIdentity::new(anchor.hash(), 10);
        let effects = runner.handle_event(AcquisitionEvent::LclInstalled(installed));
        assert!(
            effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Tracking {
                lcl: installed
            }))
        );
        assert_eq!(runner.state.recovery_anchor_target, None);
        assert_eq!(runner.state.recovery_anchor_session, None);
        assert_eq!(runner.phase(), &SyncPhase::Tracking { lcl: installed });
        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: installed,
            fresh: true,
        });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Full {
                lcl: installed,
                published: installed,
            })]
        );
    }

    #[test]
    fn terminal_anchor_failure_promotes_latest_viable_consensus_target() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let anchor = target(10);
        let latest = target(20);
        let started = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            anchor,
            AcquireReason::Consensus,
        )));
        let anchor_session = peer_request_session(&started);
        let mut timeout = timer_operation(&started);
        let header_read = started
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SubmitRead(request)
                    if request.operation().kind() == OperationKind::HeaderRead =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("anchor starts with a local header probe");
        runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            header_read,
            ReadOutcome::Settled { node: None },
        )));

        runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            latest,
            AcquireReason::Consensus,
        )));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: anchor });

        for _ in 0..6 {
            let effects = runner.handle_event(AcquisitionEvent::TimerFired {
                operation: timeout,
                timer: TimerKind::AcquireTimeout,
            });
            timeout = timer_operation(&effects);
        }
        let effects = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: timeout,
            timer: TimerKind::AcquireTimeout,
        });

        let anchor_phase = runner
            .session(anchor_session)
            .expect("failed anchor retained for stale-event accounting")
            .phase();
        assert!(
            matches!(
                anchor_phase,
                SessionPhase::Failed {
                    reason: FailureReason::AcquisitionTimeout
                }
            ),
            "unexpected anchor phase: {anchor_phase:?}"
        );
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: latest });
        assert!(
            effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                target: latest
            }))
        );
    }

    #[test]
    fn next_consensus_target_relatches_unresolved_syncing_after_anchor_invalidation() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let installed = identity(9);
        runner.handle_event(AcquisitionEvent::LclInstalled(installed));

        let old_anchor = target(10);
        runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: old_anchor });
        let old_session =
            peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
                ConsensusTarget::new(old_anchor, AcquireReason::Consensus),
            )));
        runner.handle_event(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));
        assert!(matches!(
            runner
                .session(old_session)
                .expect("invalidated anchor retained")
                .phase(),
            SessionPhase::Cancelled {
                reason: CancelReason::StoreRotated
            }
        ));
        assert_eq!(runner.state.recovery_anchor_target, None);
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: old_anchor });

        let next = target(20);
        let next_session = peer_request_session(&runner.handle_event(
            AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(next, AcquireReason::Consensus)),
        ));
        assert_eq!(runner.state.recovery_anchor_target, Some(next));
        assert_eq!(runner.state.recovery_anchor_session, Some(next_session));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: next });
        assert!(runner.request_intent_is_p0(&RequestIntent {
            session: next_session,
            peer: PeerId::new(1),
            request: LedgerDataRequest::GetLedger { sequence: Some(20) },
        }));
    }

    #[test]
    fn idle_expiry_rearms_live_anchor_and_leaves_failure_to_acquire_timeout() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let anchor = target(10);
        let latest = target(20);
        let started = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            anchor,
            AcquireReason::Consensus,
        )));
        let anchor_session = peer_request_session(&started);
        let expiry = expiry_operation(&started);
        runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            latest,
            AcquireReason::Consensus,
        )));

        let rearmed = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: expiry,
            timer: TimerKind::SessionExpiry,
        });
        let next_expiry = rearmed
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::ArmTimer(request)
                    if request.timer() == TimerKind::SessionExpiry =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("live recovery anchor rearms its registry lifetime");
        assert_ne!(next_expiry, expiry);
        let effects = runner.handle_event(AcquisitionEvent::RegistrySweep);

        assert!(effects.is_empty());
        assert!(runner.session(anchor_session).is_some());
        assert_eq!(runner.state.recovery_anchor_session, Some(anchor_session));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: anchor });
    }

    #[test]
    fn cancelled_anchor_promotes_newly_admitted_consensus_target() {
        let budget = BudgetState::new(1, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let anchor = target(10);
        let latest = target(20);
        let started = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: anchor,
            reason: AcquireReason::Generic,
        });
        let anchor_session = peer_request_session(&started);
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: anchor });

        let effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            latest,
            AcquireReason::Consensus,
        )));

        assert!(matches!(
            runner
                .session(anchor_session)
                .expect("cancelled anchor retained for stale-event accounting")
                .phase(),
            SessionPhase::Cancelled {
                reason: CancelReason::Explicit
            }
        ));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: latest });
        assert!(
            effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                target: latest
            }))
        );
    }

    #[test]
    fn pending_divergence_anchor_is_not_replaced_by_inadmissible_latest_target() {
        let budget = BudgetState::new(1, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        // Validation acquisition is phase-neutral but consumes the only slot.
        let validation = peer_request_session(
            &runner.handle_event(AcquisitionEvent::ValidationTarget(target(5))),
        );
        let anchor = target(10);
        let latest = target(20);
        runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: anchor });
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: anchor });
        let deferred_anchor = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: anchor,
            reason: AcquireReason::Consensus,
        });
        assert!(
            deferred_anchor
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SessionStarted(_)))
        );
        assert_eq!(runner.state.deferred_consensus_acquire, Some(anchor));

        let effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            latest,
            AcquireReason::Consensus,
        )));

        assert_eq!(runner.state.deferred_consensus_acquire, Some(anchor));
        assert_eq!(runner.state.recovery_anchor_target, Some(anchor));
        assert_eq!(runner.state.recovery_anchor_session, None);
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: anchor });
        assert!(effects.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::SetServicePhase(SyncPhase::Syncing { target }) if *target == latest
        )));

        let mut cancellation = Vec::new();
        runner.cancel_session(validation, CancelReason::Explicit, &mut cancellation);
        let resumed = runner.handle_event(AcquisitionEvent::Heartbeat);
        let anchor_session = resumed
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session)
                    if session.target_hash() == anchor.hash() =>
                {
                    Some(*session)
                }
                _ => None,
            })
            .expect("capacity release admits the exact pending anchor");
        assert_eq!(runner.state.recovery_anchor_session, Some(anchor_session));
        assert!(runner.request_intent_is_p0(&RequestIntent {
            session: anchor_session,
            peer: PeerId::new(1),
            request: LedgerDataRequest::GetLedger {
                sequence: anchor.sequence(),
            },
        }));
    }

    #[test]
    fn preferred_lcl_divergence_while_disconnected_is_rejected() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        let rejected = runner.snapshot().rejected_events();
        let effects =
            runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: target(9) });
        assert!(effects.is_empty());
        assert_eq!(runner.phase(), &SyncPhase::Disconnected);
        assert_eq!(runner.snapshot().rejected_events(), rejected + 1);
    }

    #[test]
    fn preferred_lcl_reconciliation_retires_stale_target_and_restores_full() {
        let local = identity(7);
        let stale = target(9);
        let mut runner = CoordinatorRunner::with_phase(
            RunEpoch::new(1),
            SyncPhase::Full {
                lcl: local,
                published: local,
            },
        );
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        let validation_recovery = target(8);
        let _ = runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(
            validation_recovery,
        )));
        assert_eq!(
            runner.state.validation_recovery_target,
            Some(validation_recovery)
        );
        let _ = runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: stale });
        let _ = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            stale,
            AcquireReason::Consensus,
        )));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: stale });

        let effects = runner.handle_event(AcquisitionEvent::PreferredLclReconciled { lcl: local });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Tracking {
                lcl: local
            })]
        );
        assert_eq!(runner.state.latest_consensus_target, None);
        assert_eq!(runner.state.deferred_consensus_acquire, None);
        assert_eq!(runner.state.validation_recovery_target, None);
        assert_eq!(runner.state.validation_recovery_session, None);
        assert_eq!(runner.state.validation_recovery_candidate, None);

        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: local,
            fresh: true,
        });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Full {
                lcl: local,
                published: local,
            })]
        );
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl: local,
                published: local,
            }
        );
    }

    #[test]
    fn preferred_lcl_divergence_requires_usable_peers() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        let effects =
            runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: target(9) });
        assert!(effects.is_empty());
        assert_eq!(runner.phase(), &SyncPhase::Disconnected);
        assert_eq!(runner.snapshot().rejected_events(), 1);
    }

    #[test]
    fn preferred_lcl_divergence_then_acquire_mints_the_session() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let _effects =
            runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: target(9) });
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(9) });
        // The strand's missing/incomplete path feeds the acquisition demand
        // after the demotion; the coordinator then mints the session.
        let acquire = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(9),
            reason: AcquireReason::Consensus,
        });
        let session = peer_request_session(&acquire);
        assert_eq!(session.target_hash(), Uint256::from(9));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(9) });
        assert_eq!(runner.snapshot().session_count(), 1);
        assert_eq!(runner.snapshot().rejected_events(), 0);
    }

    #[test]
    fn blocked_with_no_target_demotes_full_to_connected() {
        let mut runner = CoordinatorRunner::with_phase(
            RunEpoch::new(1),
            SyncPhase::Full {
                lcl: identity(1),
                published: identity(1),
            },
        );
        let effects = runner.handle_event(AcquisitionEvent::BlockedWithNoTarget);
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Connected)]
        );
        assert_eq!(runner.phase(), &SyncPhase::Connected);
        assert_eq!(runner.snapshot().rejected_events(), 0);
    }

    #[test]
    fn blocked_with_no_target_is_rejected_outside_full() {
        for phase in [
            SyncPhase::Connected,
            SyncPhase::Syncing { target: target(1) },
            SyncPhase::Tracking { lcl: identity(1) },
            SyncPhase::Disconnected,
        ] {
            let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), phase);
            let rejected = runner.snapshot().rejected_events();
            let effects = runner.handle_event(AcquisitionEvent::BlockedWithNoTarget);
            assert!(effects.is_empty(), "phase {:?} must reject the fact", phase);
            assert_eq!(runner.phase(), &phase, "phase {:?} must not change", phase);
            assert_eq!(runner.snapshot().rejected_events(), rejected + 1);
        }
    }

    #[test]
    fn repeated_targets_coalesce_without_weakening_known_sequence_and_safe_unknown_sequence_promotes()
     {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);

        let effects_a = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(9),
            reason: AcquireReason::Consensus,
        });
        let session_a = peer_request_session(&effects_a);
        let timer_a = timer_operation(&effects_a);

        // The same exact target coalesces with the active owner: it produces no
        // cancellation, second peer request, or replacement session.
        let effects_b = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(9),
            reason: AcquireReason::Consensus,
        });
        assert!(!effects_b.contains(&AcquisitionEffect::CancelSession(session_a)));
        assert!(
            !effects_b
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
        );
        assert_eq!(runner.snapshot().session_count(), 1);
        assert_eq!(runner.snapshot().sessions_cancelled(), 0);
        assert_eq!(
            runner
                .session(session_a)
                .expect("coalesced session")
                .phase(),
            &SessionPhase::Active
        );

        // A hash-only follow-up is weaker than the live verified target. It
        // must coalesce without replacing the session, changing its target,
        // or weakening the coordinator's syncing target.
        let known = LedgerTarget::new(Uint256::from(98), Some(98));
        let known_effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: known,
            reason: AcquireReason::Generic,
        });
        let known_session = peer_request_session(&known_effects);
        let hash_only_effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: LedgerTarget::new(Uint256::from(98), None),
            reason: AcquireReason::Consensus,
        });
        assert!(hash_only_effects.iter().all(|effect| {
            !matches!(
                effect,
                AcquisitionEffect::CancelSession(_) | AcquisitionEffect::SendLedgerRequest(_)
            )
        }));
        assert_eq!(
            runner
                .session(known_session)
                .expect("known session")
                .target(),
            known
        );
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(9) });
        assert_eq!(runner.snapshot().sessions_cancelled(), 0);

        // Unknown sequence can promote safely without changing the same-hash
        // session. The same session is retained and the coordinator phase
        // gains the newly known sequence without a replacement send.
        let unknown = LedgerTarget::new(Uint256::from(99), None);
        let unknown_effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: unknown,
            reason: AcquireReason::Consensus,
        });
        let unknown_session = peer_request_session(&unknown_effects);
        assert!(unknown_effects.iter().any(|effect| matches!(
            effect,
            AcquisitionEffect::SubmitRead(request)
                if request.operation().session() == unknown_session
                    && request.operation().kind() == OperationKind::HeaderRead
        )));
        let promotion = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: LedgerTarget::new(Uint256::from(99), Some(99)),
            reason: AcquireReason::Consensus,
        });
        assert!(promotion.iter().all(|effect| {
            !matches!(
                effect,
                AcquisitionEffect::CancelSession(_) | AcquisitionEffect::SendLedgerRequest(_)
            )
        }));
        assert_eq!(
            runner
                .session(unknown_session)
                .expect("promoted")
                .target()
                .sequence(),
            Some(99)
        );
        assert_eq!(runner.snapshot().sessions_cancelled(), 0);
        assert_eq!(timer_a.session(), session_a);
    }

    #[test]
    fn known_sequence_promotes_a_hash_only_session_after_base_seeds_its_plan() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsNetwork(vec![])])),
        );
        connect(&mut runner);

        let hash_only = LedgerTarget::new(Uint256::from(99), None);
        let initial = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: hash_only,
            reason: AcquireReason::Consensus,
        });
        let session = peer_request_session(&initial);
        let packet = admitted_packet(session, AdmissionBudget::new(1, 256), 8);
        let _ = runner.handle_event(AcquisitionEvent::PacketAdmitted(packet));
        assert!(
            runner
                .session(session)
                .expect("seeded session")
                .plan()
                .engine()
                .is_some()
        );

        let known = LedgerTarget::new(Uint256::from(99), Some(99));
        let effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: known,
            reason: AcquireReason::Generic,
        });
        assert!(effects.iter().all(|effect| {
            !matches!(
                effect,
                AcquisitionEffect::CancelSession(_) | AcquisitionEffect::SendLedgerRequest(_)
            )
        }));
        assert_eq!(runner.session(session).expect("promoted").target(), known);
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: known });
        assert_eq!(runner.snapshot().sessions_started(), 1);
        assert_eq!(runner.snapshot().sessions_cancelled(), 0);
    }

    #[test]
    fn live_sessions_excludes_terminal_sessions() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        assert_eq!(
            runner.live_sessions().collect::<Vec<_>>(),
            Vec::<SessionRef>::new()
        );

        let session = acquire(&mut runner, 10);
        assert_eq!(runner.live_sessions().collect::<Vec<_>>(), vec![session]);

        // Peer loss demotes service phase but keeps the exact live session in
        // the routing set so a later capability fact can resume its demand.
        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));
        assert!(effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Disconnected)));
        assert_eq!(runner.live_sessions().collect::<Vec<_>>(), vec![session]);
        assert!(runner.session(session).is_some());
    }

    #[test]
    fn store_rotation_cancels_old_generation_and_isolates_new_reads() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let session_a = acquire(&mut runner, 10);
        assert_eq!(session_a.store_generation(), StoreGeneration::new(1));

        let effects = runner.handle_event(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));
        assert!(effects.contains(&AcquisitionEffect::CancelSession(session_a)));
        assert_eq!(runner.storage_generation(), StoreGeneration::new(2));
        assert_eq!(
            runner
                .session(session_a)
                .expect("cancelled session")
                .phase(),
            &SessionPhase::Cancelled {
                reason: CancelReason::StoreRotated
            }
        );

        assert_eq!(
            runner.snapshot().cancelled_by_reason(),
            &BTreeMap::from([(CancelReason::StoreRotated, 1)])
        );

        // A session minted after the rotation is isolated to generation 2.
        let session_b = acquire(&mut runner, 11);
        assert_eq!(session_b.store_generation(), StoreGeneration::new(2));
        assert_ne!(session_b, session_a);

        // A duplicate rotation is idempotent.
        let effects = runner.handle_event(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));
        assert!(effects.is_empty());
    }

    #[test]
    fn packet_admission_respects_session_mailbox_bounds() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 100), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let session = acquire(&mut runner, 10);

        // A lease the ingress gate granted but whose byte count exceeds the
        // coordinator's defensive mailbox budget is dropped without mutation.
        let packet = admitted_packet(session, AdmissionBudget::new(1, 256), 200);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(packet));
        assert!(effects.is_empty());
        assert_eq!(runner.snapshot().packets_dropped(), 1);
        assert_eq!(
            runner
                .session(session)
                .expect("live session")
                .packet_count(),
            0
        );

        // A within-budget lease is routed and accounted.
        let packet = admitted_packet(session, AdmissionBudget::new(1, 64), 8);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(packet));
        assert!(effects.is_empty());
        assert_eq!(runner.snapshot().packets_admitted(), 1);
        assert_eq!(
            runner
                .session(session)
                .expect("live session")
                .packet_count(),
            1
        );
        assert_eq!(
            runner
                .session(session)
                .expect("live session")
                .packet_bytes(),
            8
        );
    }

    #[test]
    fn timer_fired_matches_the_exact_expected_operation() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let effects = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&effects);
        let timer_op = timer_operation(&effects);

        // The exact armed operation fires once and re-arms the deadline with a
        // fresh operation identity (the plan consumed one timeout budget).
        let effects = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: timer_op,
            timer: TimerKind::AcquireTimeout,
        });
        let retry = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .expect("an unseeded acquisition must retry its Base request");
        assert_eq!(retry.session(), session);
        assert_eq!(retry.peer_id(), PeerId::new(1));
        assert_eq!(
            retry.request(),
            &LedgerDataRequest::GetLedger { sequence: Some(10) }
        );
        let rearm = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::ArmTimer(request) => Some(request.clone().operation()),
                _ => None,
            })
            .expect("the deadline must be rearmed");
        assert_ne!(rearm, timer_op);
        assert_eq!(runner.snapshot().stale_events(), 0);

        // The consumed wakeup cannot fire again (the pending timer was rearmed
        // with a new identity, so the old operation is stale).
        let effects = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: timer_op,
            timer: TimerKind::AcquireTimeout,
        });
        assert!(effects.is_empty());
        assert_eq!(runner.snapshot().stale_events(), 1);

        // A different timer kind on a fresh session's armed timer is stale.
        let effects_b = acquire_with_effects(&mut runner, 11);
        let timer_op_b = timer_operation(&effects_b);
        let effects = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: timer_op_b,
            timer: TimerKind::ReadRetry,
        });
        assert!(effects.is_empty());
        assert_eq!(runner.snapshot().stale_events(), 2);
    }

    #[test]
    fn moving_consensus_tip_starts_concurrent_work_and_preserves_the_recovery_anchor() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsNetwork(
                (100..140)
                    .map(|hash| (SHAMapNodeId::default(), Uint256::from(hash)))
                    .collect(),
            )])),
        );
        connect(&mut runner);
        let first_target = LedgerTarget::new(Uint256::from(1), None);
        let second_target = LedgerTarget::new(Uint256::from(2), None);
        let first_effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(first_target, AcquireReason::Consensus),
        ));
        let first = peer_request_session(&first_effects);
        let first_timer = timer_operation(&first_effects);
        let _ = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            first,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let second_effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(second_target, AcquireReason::Consensus),
        ));

        assert_eq!(
            runner.session(first).expect("first retained").phase(),
            &SessionPhase::Active
        );
        assert_eq!(
            runner
                .session(first)
                .expect("first retained")
                .pending_timer(),
            Some((TimerKind::AcquireTimeout, first_timer))
        );
        let second = peer_request_session(&second_effects);
        assert_eq!(
            runner.session(second).expect("second").phase(),
            &SessionPhase::Active
        );
        assert_eq!(runner.live_sessions().count(), 2);
        assert_eq!(runner.state.latest_consensus_target, Some(second_target));
        assert_eq!(runner.state.deferred_consensus_acquire, None);
        assert_eq!(
            runner.phase(),
            &SyncPhase::Syncing {
                target: first_target
            }
        );
    }

    #[test]
    fn validation_recovery_latch_coalesces_moving_consensus_observations() {
        let full = SyncPhase::Full {
            lcl: identity(40),
            published: identity(40),
        };
        let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), full);
        let recovery = target(90);
        let started =
            runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(recovery)));
        let owner = peer_request_session(&started);

        for seq in 91..191 {
            let moving = target(seq);
            let effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(
                ConsensusTarget::new(moving, AcquireReason::Consensus),
            ));
            assert!(effects.iter().all(|effect| !matches!(
                effect,
                AcquisitionEffect::SessionStarted(_) | AcquisitionEffect::SendLedgerRequest(_)
            )));
            assert_eq!(runner.state.latest_consensus_target, Some(moving));

            let direct = runner.handle_event(AcquisitionEvent::AcquireRequested {
                target: moving,
                reason: AcquireReason::Consensus,
            });
            assert!(direct.iter().all(|effect| !matches!(
                effect,
                AcquisitionEffect::SessionStarted(_) | AcquisitionEffect::SendLedgerRequest(_)
            )));

            let validation = runner.handle_event(AcquisitionEvent::ValidationTarget(moving));
            assert!(validation.iter().all(|effect| !matches!(
                effect,
                AcquisitionEffect::SessionStarted(_) | AcquisitionEffect::SendLedgerRequest(_)
            )));
        }

        assert_eq!(runner.live_sessions().collect::<Vec<_>>(), vec![owner]);
        assert_eq!(runner.state.validation_recovery_target, Some(recovery));
        assert_eq!(runner.state.validation_recovery_session, Some(owner));
    }

    #[test]
    fn concurrent_consensus_sessions_accept_independent_read_and_plan_work() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsReads(vec![
                PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(7)),
                    1,
                    SHAMapNodeId::default(),
                    0,
                ),
            ])])),
        );
        connect(&mut runner);
        let first_effects = acquire_with_effects(&mut runner, 1);
        let first = peer_request_session(&first_effects);
        let first_timer = timer_operation(&first_effects);
        let seeded = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            first,
            AdmissionBudget::new(1, 64),
            8,
        )));
        let read = read_effects(&seeded)[0].operation();
        let plan_turns = runner.snapshot().plan_turns();

        let second = peer_request_session(&acquire_with_effects(&mut runner, 2));
        assert_eq!(
            runner.session(first).expect("first").phase(),
            &SessionPhase::Active
        );
        assert_eq!(
            runner.session(second).expect("second").phase(),
            &SessionPhase::Active
        );
        let _ = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            read,
            ReadOutcome::Settled { node: None },
        )));
        assert!(runner.snapshot().plan_turns() > plan_turns);
        assert_eq!(runner.snapshot().stale_events(), 0);
        assert_eq!(
            runner.session(first).expect("first").pending_timer(),
            Some((TimerKind::AcquireTimeout, first_timer))
        );
    }

    #[test]
    fn newest_preferred_consensus_is_deferred_when_all_concurrent_slots_are_active() {
        let budget = BudgetState::new(2, AdmissionBudget::default(), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let first = acquire(&mut runner, 1);
        let second = acquire(&mut runner, 2);
        assert_eq!(
            runner.session(first).expect("first").phase(),
            &SessionPhase::Active
        );

        let third_effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(target(3), AcquireReason::Consensus),
        ));
        assert!(third_effects.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::CancelSession(_) | AcquisitionEffect::SessionStarted(_)
        )));
        assert!(runner.has_deferred_consensus_target(target(3)));
        assert_eq!(
            runner.session(first).expect("first").phase(),
            &SessionPhase::Active
        );
        assert_eq!(
            runner.session(second).expect("second").phase(),
            &SessionPhase::Active
        );
        assert_eq!(runner.state.latest_consensus_target, Some(target(3)));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(3) });
    }

    #[test]
    fn persisting_consensus_session_is_never_dormant_or_cancelled_by_new_target() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::Complete])),
        );
        connect(&mut runner);
        let persisting = acquire(&mut runner, 1);
        let _ = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            persisting,
            AdmissionBudget::new(1, 64),
            8,
        )));
        assert_eq!(
            runner.session(persisting).expect("persisting").phase(),
            &SessionPhase::Persisting
        );

        let next = acquire_with_effects(&mut runner, 2);
        assert!(next.iter().all(|effect| {
            !matches!(effect, AcquisitionEffect::CancelSession(session) if *session == persisting)
        }));
        assert_eq!(
            runner.session(persisting).expect("persisting").phase(),
            &SessionPhase::Persisting
        );
    }

    fn acquire_with_effects(runner: &mut CoordinatorRunner, seq: u32) -> Vec<AcquisitionEffect> {
        let mut effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(seq),
            reason: AcquireReason::Consensus,
        });
        if let Some(operation) = effects.iter().find_map(|effect| match effect {
            AcquisitionEffect::SubmitRead(request)
                if request.operation().kind() == OperationKind::HeaderRead =>
            {
                Some(request.operation())
            }
            _ => None,
        }) {
            effects.extend(runner.handle_event(AcquisitionEvent::ReadCompleted(
                ReadCompletion::new(operation, ReadOutcome::Settled { node: None }),
            )));
        }
        effects
    }

    fn preferred_with_effects(runner: &mut CoordinatorRunner, seq: u32) -> Vec<AcquisitionEffect> {
        let mut effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(target(seq), AcquireReason::Consensus),
        ));
        if let Some(operation) = effects.iter().find_map(|effect| match effect {
            AcquisitionEffect::SubmitRead(request)
                if request.operation().kind() == OperationKind::HeaderRead =>
            {
                Some(request.operation())
            }
            _ => None,
        }) {
            effects.extend(runner.handle_event(AcquisitionEvent::ReadCompleted(
                ReadCompletion::new(operation, ReadOutcome::Settled { node: None }),
            )));
        }
        effects
    }

    #[test]
    fn outbound_admission_bounds_global_credits_and_prioritizes_latched_anchor() {
        // This test isolates the 256-request outbound credit pool, so give it
        // enough explicit session capacity rather than inheriting the bounded
        // medium production default.
        let mut runner = CoordinatorRunner::with_budget(
            RunEpoch::new(1),
            BudgetState::new(64, AdmissionBudget::default(), Duration::from_secs(120)),
        );
        let peers = (1..=5).map(PeerId::new).collect::<Vec<_>>();
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(peers),
        ));

        // Fifty-two Generic sessions fill the global 256-credit pool (fifty-one
        // full five-peer Base fanouts plus one request from the last), leaving
        // its remaining Base intents queued. Generic cache work cannot mint a
        // recovery anchor; the authoritative consensus target claims the next
        // released credits.
        let mut first_timer = None;
        for sequence in 1..=52 {
            let mut effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
                target: target(sequence),
                reason: AcquireReason::Generic,
            });
            if sequence == 1 {
                first_timer = Some(timer_operation(&effects));
            }
            if let Some(operation) = effects.iter().find_map(|effect| match effect {
                AcquisitionEffect::SubmitRead(request)
                    if request.operation().kind() == OperationKind::HeaderRead =>
                {
                    Some(request.operation())
                }
                _ => None,
            }) {
                effects.extend(runner.handle_event(AcquisitionEvent::ReadCompleted(
                    ReadCompletion::new(operation, ReadOutcome::Settled { node: None }),
                )));
            }
        }
        assert_eq!(
            runner.state.outbound.outstanding.len(),
            MAX_OUTBOUND_REQUESTS_GLOBAL
        );
        assert!(runner.state.outbound.intents.len() >= 3);

        let mut consensus = runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(target(99), AcquireReason::Consensus),
        ));
        let consensus_session = consensus
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("consensus session must be created even while credits are full");
        let consensus_header = consensus
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SubmitRead(request)
                    if request.operation().kind() == OperationKind::HeaderRead =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("latest consensus acquisition probes the resident header");
        consensus.extend(runner.handle_event(AcquisitionEvent::ReadCompleted(
            ReadCompletion::new(consensus_header, ReadOutcome::Settled { node: None }),
        )));
        assert!(
            consensus
                .iter()
                .all(|effect| { !matches!(effect, AcquisitionEffect::SendLedgerRequest(_)) })
        );

        // Expiring one Generic deadline is the conservative release point.
        // The exact consensus recovery anchor consumes all five released slots.
        let released = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: first_timer.expect("first Generic timer"),
            timer: TimerKind::AcquireTimeout,
        });
        let requests = released
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(requests.len(), 5);
        assert!(
            requests
                .iter()
                .all(|request| request.session() == consensus_session)
        );
        assert_eq!(
            runner.state.outbound.outstanding.len(),
            MAX_OUTBOUND_REQUESTS_GLOBAL
        );
        assert!(
            runner
                .state
                .outbound
                .outstanding_by_peer
                .values()
                .all(|count| *count <= MAX_OUTBOUND_REQUESTS_PER_PEER)
        );
        assert!(
            runner
                .state
                .outbound
                .outstanding_by_session
                .values()
                .all(|count| *count <= MAX_OUTBOUND_REQUESTS_PER_SESSION)
        );
    }

    #[test]
    fn validation_target_is_phase_neutral_and_does_not_replace_lcl_policy() {
        let full = SyncPhase::Full {
            lcl: identity(40),
            published: identity(40),
        };
        let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), full);
        let preferred = target(41);
        runner.state.latest_consensus_target = Some(preferred);

        let validation = target(99);
        let generic = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: validation,
            reason: AcquireReason::Generic,
        });
        let generic_session = generic
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("generic cache demand starts the exact session");
        let hash_only_validation = LedgerTarget::new(validation.hash(), None);
        let effects = runner.handle_event(AcquisitionEvent::ValidationTarget(hash_only_validation));

        assert_eq!(runner.phase(), &full);
        assert_eq!(runner.state.latest_consensus_target, Some(preferred));
        assert_eq!(
            runner.state.latest_validation_target,
            Some(hash_only_validation)
        );
        assert_eq!(
            runner.state.latest_validation_session,
            Some(generic_session)
        );
        assert!(
            effects
                .iter()
                .all(|effect| { !matches!(effect, AcquisitionEffect::SetServicePhase(_)) })
        );
        assert!(
            effects
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SessionStarted(_)))
        );
        assert_eq!(
            runner
                .session(generic_session)
                .expect("exact session is reused")
                .reason(),
            AcquireReason::Generic
        );
        assert!(!runner.request_intent_is_p0(&RequestIntent {
            session: generic_session,
            peer: PeerId::new(1),
            request: LedgerDataRequest::GetLedger { sequence: Some(99) },
        }));
    }

    #[test]
    fn validation_priority_does_not_survive_its_exact_session() {
        let full = SyncPhase::Full {
            lcl: identity(40),
            published: identity(40),
        };
        let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), full);
        let validation = target(99);
        let started = runner.handle_event(AcquisitionEvent::ValidationTarget(validation));
        let validation_session = peer_request_session(&started);
        assert_eq!(
            runner.state.latest_validation_session,
            Some(validation_session)
        );

        runner.handle_event(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));
        assert_eq!(runner.state.latest_validation_target, None);
        assert_eq!(runner.state.latest_validation_session, None);

        let replacement = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: validation,
            reason: AcquireReason::Generic,
        });
        let replacement_session = peer_request_session(&replacement);
        assert!(!runner.request_intent_is_p0(&RequestIntent {
            session: replacement_session,
            peer: PeerId::new(1),
            request: LedgerDataRequest::GetLedger { sequence: Some(99) },
        }));
    }

    #[test]
    fn validation_recovery_latches_exact_owner_phase_neutrally_and_promotes_on_terminal() {
        let full = SyncPhase::Full {
            lcl: identity(40),
            published: identity(40),
        };
        let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), full);
        let first = target(90);
        let next = target(91);

        let started = runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(first)));
        let first_session = started
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("first recovery owner starts");
        assert_eq!(runner.phase(), &full);
        assert_eq!(runner.state.validation_recovery_target, Some(first));
        assert_eq!(
            runner.state.validation_recovery_session,
            Some(first_session)
        );
        assert_eq!(runner.snapshot().validation_recovery_target(), Some(first));
        assert_eq!(
            runner.snapshot().validation_recovery_session(),
            Some(first_session)
        );
        assert!(runner.request_intent_is_p0(&RequestIntent {
            session: first_session,
            peer: PeerId::new(1),
            request: LedgerDataRequest::GetLedger { sequence: Some(90) },
        }));

        let moving = runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(next)));
        assert!(moving.iter().all(|effect| {
            !matches!(
                effect,
                AcquisitionEffect::SessionStarted(_) | AcquisitionEffect::SetServicePhase(_)
            )
        }));
        assert_eq!(runner.state.validation_recovery_target, Some(first));
        assert_eq!(runner.state.validation_recovery_candidate, Some(next));

        let rotated = runner.handle_event(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));
        let next_session = rotated
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session)
                    if session.target_hash() == next.hash() =>
                {
                    Some(*session)
                }
                _ => None,
            })
            .expect("terminal boundary promotes the newest observed candidate");
        assert_eq!(runner.phase(), &full);
        assert_eq!(runner.state.validation_recovery_target, Some(next));
        assert_eq!(runner.state.validation_recovery_session, Some(next_session));
    }

    #[test]
    fn validation_recovery_promotes_before_replaying_deferred_consensus() {
        let full = SyncPhase::Full {
            lcl: identity(40),
            published: identity(40),
        };
        let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), full);
        runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        let first = target(190);
        let next = target(191);
        let moving = target(192);

        let first_session = peer_request_session(
            &runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(first))),
        );
        let candidate = runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(next)));
        assert!(
            candidate
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SessionStarted(_)))
        );

        // Entering Syncing must not weaken the exact validation-recovery
        // ownership. The moving preferred target remains bounded metadata.
        runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: moving });
        let deferred = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: moving,
            reason: AcquireReason::Consensus,
        });
        assert!(
            deferred
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SessionStarted(_)))
        );
        assert_eq!(runner.state.deferred_consensus_acquire, Some(moving));

        let rotated = runner.handle_event(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));
        let started = rotated
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(started.len(), 1);
        assert_eq!(started[0].target_hash(), next.hash());
        assert_ne!(started[0], first_session);
        assert_eq!(runner.state.validation_recovery_target, Some(next));
        assert_eq!(runner.state.validation_recovery_session, Some(started[0]));
        assert_eq!(runner.state.deferred_consensus_acquire, Some(moving));
        assert!(
            runner
                .state
                .sessions
                .iter()
                .all(|(session, state)| session.target_hash() != moving.hash()
                    || state.phase().is_terminal())
        );
    }

    #[test]
    fn failed_validation_recovery_waits_for_terminal_retention_then_retries() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let recovery = target(199);
        let failed_session = peer_request_session(
            &runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(recovery))),
        );

        let mut failure_effects = Vec::new();
        runner.fail_session(
            failed_session,
            FailureReason::AcquisitionTimeout,
            &mut failure_effects,
        );
        let retention = runner
            .session(failed_session)
            .expect("failed actor remains registered")
            .pending_timer()
            .expect("failed actor has a retention timer")
            .1;

        let immediate =
            runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(recovery)));
        assert!(
            immediate
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SessionStarted(_)))
        );
        assert_eq!(runner.state.validation_recovery_target, Some(recovery));
        assert_eq!(runner.state.validation_recovery_session, None);
        assert!(matches!(
            runner
                .session(failed_session)
                .expect("failed tombstone remains until its sweep")
                .phase(),
            SessionPhase::Failed { .. }
        ));

        let retried = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: retention,
            timer: TimerKind::TerminalRetention,
        });
        let replacement = retried
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("retained recovery demand retries after the failed tombstone is swept");
        assert_ne!(replacement, failed_session);
        assert_eq!(replacement.target_hash(), recovery.hash());
        assert!(runner.session(failed_session).is_none());
        assert_eq!(runner.state.validation_recovery_target, Some(recovery));
        assert_eq!(runner.state.validation_recovery_session, Some(replacement));
    }

    #[test]
    fn failed_preferred_anchor_restarts_after_terminal_retention() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let recovery = target(209);
        let failed_session =
            peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
                ConsensusTarget::new(recovery, AcquireReason::Consensus),
            )));
        assert_eq!(runner.state.recovery_anchor_target, Some(recovery));
        assert_eq!(runner.state.recovery_anchor_session, Some(failed_session));

        let mut failure_effects = Vec::new();
        runner.fail_session(
            failed_session,
            FailureReason::AcquisitionTimeout,
            &mut failure_effects,
        );
        let retention = runner
            .session(failed_session)
            .expect("failed actor remains registered")
            .pending_timer()
            .expect("failed actor has a retention timer")
            .1;
        // Model the normal terminal event boundary before NetworkOps repeats
        // its still-authoritative preferred target.
        runner.reconcile_recovery_anchor();
        assert_eq!(runner.state.recovery_anchor_target, None);

        let immediate = runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(recovery, AcquireReason::Consensus),
        ));
        assert!(
            immediate
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SessionStarted(_)))
        );
        assert_eq!(runner.state.recovery_anchor_target, Some(recovery));
        assert_eq!(runner.state.recovery_anchor_session, None);
        assert_eq!(runner.state.deferred_consensus_acquire, Some(recovery));

        let retried = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: retention,
            timer: TimerKind::TerminalRetention,
        });
        let replacement = retried
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("preferred recovery retries when its failed actor leaves the hash registry");
        assert_ne!(replacement, failed_session);
        assert_eq!(replacement.target_hash(), recovery.hash());
        assert_eq!(runner.state.deferred_consensus_acquire, None);
        assert_eq!(runner.state.recovery_anchor_target, Some(recovery));
        assert_eq!(runner.state.recovery_anchor_session, Some(replacement));
        assert!(runner.request_intent_is_p0(&RequestIntent {
            session: replacement,
            peer: PeerId::new(1),
            request: LedgerDataRequest::GetLedger {
                sequence: recovery.sequence(),
            },
        }));
    }

    #[test]
    fn validation_recovery_preempts_lower_priority_and_survives_peerless_start() {
        let budget = BudgetState::new(1, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        let recovery = target(99);

        // The exact target is retained without a session while peerless.
        let peerless =
            runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(recovery)));
        assert!(peerless.is_empty());
        assert_eq!(runner.state.validation_recovery_target, Some(recovery));
        assert_eq!(runner.state.validation_recovery_session, None);

        let connected = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        let recovery_session = connected
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("peer recovery starts the retained exact target");
        assert_eq!(
            runner.state.validation_recovery_session,
            Some(recovery_session)
        );

        // Release that owner, withdraw any successor, and fill the only slot
        // with lower-priority work before observing a new recovery target.
        let _ = runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(None));
        let _ = runner.handle_event(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));
        let generic = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(100),
            reason: AcquireReason::Generic,
        });
        let generic_session = generic
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("generic fills capacity");

        let replacement = target(101);
        let effects = runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(
            replacement,
        )));
        assert!(effects.iter().any(
            |effect| matches!(effect, AcquisitionEffect::CancelSession(session) if *session == generic_session)
        ));
        assert!(effects.iter().any(
            |effect| matches!(effect, AcquisitionEffect::SessionStarted(session) if session.target_hash() == replacement.hash())
        ));
        assert!(
            effects
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SetServicePhase(_)))
        );
    }

    #[test]
    fn preferred_lcl_recovery_defers_behind_active_validation_recovery_owner() {
        let budget = BudgetState::new(1, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let validation = target(200);
        let validation_effects =
            runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(validation)));
        let validation_session = validation_effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("validation recovery starts");

        let header_read = validation_effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SubmitRead(request)
                    if request.operation().kind() == OperationKind::HeaderRead =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("validation recovery starts with a header probe");
        runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            header_read,
            ReadOutcome::Settled { node: None },
        )));

        let preferred = target(201);
        runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: preferred });
        let deferred = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: preferred,
            reason: AcquireReason::Consensus,
        });
        assert!(deferred.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::CancelSession(_) | AcquisitionEffect::SessionStarted(_)
        )));
        assert_eq!(runner.state.validation_recovery_target, Some(validation));
        assert_eq!(
            runner.state.validation_recovery_session,
            Some(validation_session)
        );
        assert_eq!(runner.state.deferred_consensus_acquire, Some(preferred));
        assert_eq!(runner.snapshot().sessions_cancelled(), 0);

        let mut terminal = Vec::new();
        for _ in 0..8 {
            let operation = runner
                .session(validation_session)
                .expect("validation owner retained until timeout")
                .pending_timer()
                .expect("validation owner keeps its acquisition timer")
                .1;
            terminal = runner.handle_event(AcquisitionEvent::TimerFired {
                operation,
                timer: TimerKind::AcquireTimeout,
            });
            if runner
                .session(validation_session)
                .is_some_and(|state| state.phase().is_terminal())
            {
                break;
            }
        }
        assert!(terminal.iter().any(|effect| {
            matches!(effect, AcquisitionEffect::SessionStarted(session) if session.target_hash() == preferred.hash())
        }));
        assert_eq!(runner.state.deferred_consensus_acquire, None);
        assert_eq!(runner.state.recovery_anchor_target, Some(preferred));
    }

    #[test]
    fn dormant_recovery_owners_are_not_evicted_by_new_preferred_demand() {
        let budget = BudgetState::new(1, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let validation = target(220);
        let validation_session = peer_request_session(
            &runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(validation))),
        );
        runner
            .state
            .sessions
            .get_mut(&validation_session)
            .expect("validation owner")
            .phase = SessionPhase::Dormant;

        let preferred = target(221);
        runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: preferred });
        let deferred = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: preferred,
            reason: AcquireReason::Consensus,
        });
        assert!(deferred.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::CancelSession(_) | AcquisitionEffect::SessionStarted(_)
        )));
        assert_eq!(runner.state.validation_recovery_target, Some(validation));
        assert_eq!(
            runner.state.validation_recovery_session,
            Some(validation_session)
        );
        assert_eq!(
            runner
                .session(validation_session)
                .expect("dormant owner remains live")
                .phase(),
            &SessionPhase::Dormant
        );
        assert_eq!(runner.state.deferred_consensus_acquire, Some(preferred));
        assert_eq!(runner.snapshot().sessions_cancelled(), 0);

        let terminal = runner.handle_event(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));
        assert!(terminal.iter().any(|effect| {
            matches!(effect, AcquisitionEffect::CancelSession(session) if *session == validation_session)
        }));
        assert!(terminal.iter().any(|effect| {
            matches!(effect, AcquisitionEffect::SessionStarted(session) if session.target_hash() == preferred.hash())
        }));

        let mut anchor_runner = CoordinatorRunner::with_budget(
            RunEpoch::new(2),
            BudgetState::new(1, AdmissionBudget::new(4, 1024), Duration::from_secs(1)),
        );
        connect(&mut anchor_runner);
        let anchor = target(230);
        let anchor_session = peer_request_session(&anchor_runner.handle_event(
            AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
                anchor,
                AcquireReason::Consensus,
            )),
        ));
        anchor_runner
            .state
            .sessions
            .get_mut(&anchor_session)
            .expect("recovery anchor")
            .phase = SessionPhase::Dormant;
        let mut eviction = Vec::new();
        assert!(!anchor_runner.evict_oldest_dormant_consensus(&mut eviction));
        assert!(eviction.is_empty());
        assert_eq!(
            anchor_runner.state.recovery_anchor_session,
            Some(anchor_session)
        );
    }

    #[test]
    fn authoritative_request_and_scan_rank_above_validation_recovery() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let authoritative =
            peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
                ConsensusTarget::new(target(211), AcquireReason::Consensus),
            )));
        let validation = peer_request_session(&runner.handle_event(
            AcquisitionEvent::ValidationRecoveryTarget(Some(target(210))),
        ));
        let request = |session| RequestIntent {
            session,
            peer: PeerId::new(1),
            request: LedgerDataRequest::GetLedger {
                sequence: Some(211),
            },
        };
        assert_eq!(runner.request_intent_priority(&request(authoritative)), 0);
        assert_eq!(runner.request_intent_priority(&request(validation)), 1);

        runner.state.local_scan_waiters = VecDeque::from([validation, authoritative]);
        assert_eq!(runner.pop_scan_waiter(), Some(authoritative));
        assert_eq!(runner.pop_scan_waiter(), Some(validation));
    }

    #[test]
    fn unseeded_same_hash_owner_guards_app_origin_until_plan_construction() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let target = target(220);
        let session =
            peer_request_session(&runner.handle_event(AcquisitionEvent::AcquireRequested {
                target,
                reason: AcquireReason::Generic,
            }));
        assert!(runner.retains_session_origin_for_hash(target.hash()));
        assert!(
            runner
                .state
                .sessions
                .get_mut(&session)
                .expect("live")
                .plan
                .install_engine(Box::new(ScriptedEngine::new(
                    TreePlanId::new(220),
                    VecDeque::new(),
                    Vec::new(),
                )))
        );
        assert!(!runner.retains_session_origin_for_hash(target.hash()));
    }

    #[test]
    fn peerless_ordinary_origin_survives_same_hash_candidate_replacement() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let _ = runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(target(
            230,
        ))));
        let _ = runner.handle_event(AcquisitionEvent::TransportConnectivity(
            PeerAvailabilitySnapshot::new(Vec::new()),
        ));
        let ordinary = target(231);
        let _ = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: ordinary,
            reason: AcquireReason::Generic,
        });
        let _ = runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(ordinary)));
        let replacement = target(232);
        let _ = runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(
            replacement,
        )));

        assert!(runner.retains_session_origin_for_hash(ordinary.hash()));
        assert!(runner.retains_session_origin_for_hash(replacement.hash()));
        assert_eq!(
            runner.state.validation_recovery_candidate,
            Some(replacement)
        );
    }

    #[test]
    fn phase_neutral_validation_cannot_weaken_deferred_preferred_lcl_demand() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        let preferred = target(77);

        let _ = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            preferred,
            AcquireReason::Consensus,
        )));
        let _ = runner.handle_event(AcquisitionEvent::ValidationTarget(preferred));

        assert_eq!(
            runner.state.deferred_acquires.get(&preferred),
            Some(&(AcquireReason::Consensus, true, false))
        );
    }

    #[test]
    fn newest_validation_target_does_not_beat_fifo_when_outbound_credits_are_saturated() {
        let full = SyncPhase::Full {
            lcl: identity(40),
            published: identity(40),
        };
        let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), full);
        let peers = (1..=5).map(PeerId::new).collect::<Vec<_>>();
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(peers),
        ));

        let first = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(1),
            reason: AcquireReason::Generic,
        });
        let first_timer = timer_operation(&first);
        let first_session = peer_request_session(&first);
        let first_header = first
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SubmitRead(request)
                    if request.operation().kind() == OperationKind::HeaderRead =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("first acquisition probes the resident header");
        let _ = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            first_header,
            ReadOutcome::Settled { node: None },
        )));
        runner.release_session_request_credits(first_session);
        let synthetic_sessions = [
            first_session,
            SessionRef::new(
                RunEpoch::new(1),
                SessionId::new(100_001),
                Uint256::from(100_001),
                PlanEpoch::new(100_001),
                StoreGeneration::new(1),
            ),
            SessionRef::new(
                RunEpoch::new(1),
                SessionId::new(100_002),
                Uint256::from(100_002),
                PlanEpoch::new(100_002),
                StoreGeneration::new(1),
            ),
            SessionRef::new(
                RunEpoch::new(1),
                SessionId::new(100_003),
                Uint256::from(100_003),
                PlanEpoch::new(100_003),
                StoreGeneration::new(1),
            ),
        ];
        let mut synthetic_id = 200_000u64;
        for session in synthetic_sessions {
            for offset in 0..MAX_OUTBOUND_REQUESTS_PER_SESSION {
                let peer = PeerId::new((offset % 5 + 1) as u64);
                let operation = OperationRef::new(
                    session,
                    OperationKind::PeerRequest,
                    OperationId::new(synthetic_id),
                    OperationGeneration::new(synthetic_id),
                );
                runner.state.outbound.outstanding.insert(operation, peer);
                *runner
                    .state
                    .outbound
                    .outstanding_by_peer
                    .entry(peer)
                    .or_default() += 1;
                *runner
                    .state
                    .outbound
                    .outstanding_by_session
                    .entry(session)
                    .or_default() += 1;
                synthetic_id += 1;
            }
        }
        runner.state.outbound.intents.push_back(RequestIntent {
            session: first_session,
            peer: PeerId::new(1),
            request: LedgerDataRequest::GetLedger { sequence: Some(1) },
        });
        assert_eq!(
            runner.state.outbound.outstanding.len(),
            MAX_OUTBOUND_REQUESTS_GLOBAL
        );
        assert!(!runner.state.outbound.intents.is_empty());

        let older_validation =
            runner.handle_event(AcquisitionEvent::ValidationTarget(target(9_000)));
        let older_header = older_validation
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SubmitRead(request)
                    if request.operation().kind() == OperationKind::HeaderRead =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("older validation target starts behind the full window");
        let _ = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            older_header,
            ReadOutcome::Settled { node: None },
        )));

        let validation = target(10_000);
        let queued = runner.handle_event(AcquisitionEvent::ValidationTarget(validation));
        let validation_session = queued
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("validation session starts behind the full credit window");
        let validation_header = queued
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SubmitRead(request)
                    if request.operation().kind() == OperationKind::HeaderRead =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("validation acquisition probes the resident header first");
        assert!(queued.iter().all(|effect| {
            !matches!(effect, AcquisitionEffect::SendLedgerRequest(_))
                && !matches!(effect, AcquisitionEffect::SetServicePhase(_))
        }));
        assert_eq!(runner.phase(), &full);

        let queued_base = runner.handle_event(AcquisitionEvent::ReadCompleted(
            ReadCompletion::new(validation_header, ReadOutcome::Settled { node: None }),
        ));
        assert!(
            queued_base
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
        );
        assert_eq!(
            runner
                .state
                .outbound
                .intents
                .iter()
                .filter(|intent| intent.session == validation_session)
                .count(),
            5
        );

        let released = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: first_timer,
            timer: TimerKind::AcquireTimeout,
        });
        let requests = released
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(requests.len() >= 5);
        assert_eq!(
            requests.first().map(|request| request.session()),
            Some(first_session)
        );
        assert!(
            requests
                .iter()
                .any(|request| request.session() == validation_session)
        );
        assert_eq!(runner.phase(), &full);
    }

    #[test]
    fn stale_intent_backlog_does_not_block_a_live_normal_frontier() {
        let node = state_network_need(0x77);
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsNetworkWithKind(
                vec![node],
            )])),
        );
        connect(&mut runner);
        let session = acquire(&mut runner, 10);
        let queued_session = SessionRef::new(
            RunEpoch::new(99),
            SessionId::new(99),
            Uint256::from(99),
            PlanEpoch::new(99),
            StoreGeneration::new(99),
        );
        for _ in 0..MAX_QUEUED_REQUEST_INTENTS {
            runner.state.outbound.intents.push_back(RequestIntent {
                session: queued_session,
                peer: PeerId::new(1),
                request: LedgerDataRequest::GetLedger { sequence: Some(99) },
            });
        }

        // The arbiter is credit-bounded, not count-bounded by stale intents.
        // Invalid old routes cannot prevent live per-hash work from entering
        // and being selected by the common emitter.
        let emitted = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        assert_eq!(
            normal_ledger_node_requests(&emitted),
            vec![(PeerId::new(1), vec![node.node_id()])]
        );
        assert_eq!(
            runner
                .session(session)
                .expect("live session")
                .plan()
                .retained_network(),
            &[node]
        );
    }

    #[test]
    fn stale_terminal_timer_cannot_release_a_replacement_sessions_credit() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let first = acquire_with_effects(&mut runner, 10);
        let first_session = peer_request_session(&first);
        let first_timer = timer_operation(&first);
        let _ = runner.handle_event(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));

        let replacement = acquire_with_effects(&mut runner, 10);
        let replacement_session = peer_request_session(&replacement);
        assert_ne!(first_session, replacement_session);
        assert_eq!(runner.state.outbound.outstanding.len(), 1);

        // The old timer is terminal/stale and returns before any release path.
        // Its SessionRef cannot match the replacement's exact credit key.
        let stale = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: first_timer,
            timer: TimerKind::AcquireTimeout,
        });
        assert!(stale.is_empty());
        assert_eq!(runner.state.outbound.outstanding.len(), 1);
        assert!(
            runner
                .state
                .outbound
                .outstanding
                .keys()
                .all(|operation| operation.session() == replacement_session)
        );
    }

    #[test]
    fn peer_loss_releases_credits_and_pauses_requests_until_a_recovery_grant() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1), PeerId::new(2)]),
        ));
        let initial = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&initial);
        assert_eq!(runner.state.outbound.outstanding.len(), 2);

        let lost = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));
        assert!(
            lost.iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
        );
        assert!(runner.state.outbound.outstanding.is_empty());
        assert!(
            !runner
                .session(session)
                .expect("paused session")
                .network_admitted
        );

        let recovered = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(9)]),
        ));
        assert!(recovered.iter().any(|effect| {
            matches!(effect, AcquisitionEffect::SendLedgerRequest(request)
                if request.session() == session && request.peer_id() == PeerId::new(9))
        }));
        assert_eq!(runner.state.outbound.outstanding.len(), 1);
    }

    #[test]
    fn validation_recovery_replays_after_reconnect_before_peer_ledger_ranges_refresh() {
        let full = SyncPhase::Full {
            lcl: identity(40),
            published: identity(40),
        };
        let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), full);
        let recovery = target(90);
        runner.update_target_peer_capabilities(
            recovery,
            vec![PeerTargetCapability::new(PeerId::new(1), false)],
        );
        let _ = runner.handle_event(AcquisitionEvent::TransportConnectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        let started =
            runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(recovery)));
        let session = peer_request_session(&started);

        let lost = runner.handle_event(AcquisitionEvent::TransportConnectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));
        assert!(lost.is_empty(), "transport loss remains phase-neutral");
        assert_eq!(runner.phase(), &full);
        assert!(runner.state.outbound.outstanding.is_empty());
        assert!(
            !runner
                .session(session)
                .expect("retained recovery owner")
                .network_admitted
        );

        // A newly connected peer may not have published a fresh status/range
        // yet. rippled still scores and admits that peer; exact `hasLedger`
        // knowledge only puts a peer first.
        runner.update_target_peer_capabilities(recovery, vec![]);
        let recovered = runner.handle_event(AcquisitionEvent::TransportConnectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(9)]),
        ));
        assert_eq!(runner.phase(), &full);
        assert!(
            recovered
                .iter()
                .all(|effect| { !matches!(effect, AcquisitionEffect::SetServicePhase(_)) })
        );
        assert!(recovered.iter().any(|effect| {
            matches!(effect, AcquisitionEffect::SendLedgerRequest(request)
                if request.session() == session && request.peer_id() == PeerId::new(9))
        }));
        assert!(recovered.iter().any(|effect| {
            matches!(effect, AcquisitionEffect::ArmTimer(timer)
                if timer.operation().session() == session
                    && timer.timer() == TimerKind::AcquireTimeout)
        }));
        let retained = runner.session(session).expect("rearmed recovery owner");
        assert!(retained.network_admitted);
        assert!(retained.sent_peers().contains(&PeerId::new(9)));
    }

    #[test]
    fn unseeded_base_timeout_cycles_after_initial_peer_fanout() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1), PeerId::new(2)]),
        ));
        let initial = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&initial);
        let initial_peers = initial
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request.peer_id()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(initial_peers, vec![PeerId::new(1), PeerId::new(2)]);
        let timer = timer_operation(&initial);

        let effects = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: timer,
            timer: TimerKind::AcquireTimeout,
        });
        let retry_peers = effects
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            retry_peers.len(),
            2,
            "timeout must reach every selected peer"
        );
        assert!(retry_peers.iter().all(|retry| {
            retry.session() == session
                && retry.request() == &LedgerDataRequest::GetLedger { sequence: Some(10) }
        }));
        assert_eq!(
            retry_peers
                .iter()
                .map(|retry| retry.peer_id())
                .collect::<Vec<_>>(),
            vec![PeerId::new(1), PeerId::new(2)]
        );
        assert_eq!(runner.snapshot().peer_requests(), 4);
        assert_eq!(
            runner.session(session).expect("live session").sent_peers(),
            &BTreeSet::from([PeerId::new(1), PeerId::new(2)])
        );
    }

    #[test]
    fn progress_suppresses_one_interval_without_resetting_timeout_budget_or_peer_window() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new((1..=100).map(PeerId::new).collect()),
        ));
        let initial = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&initial);
        let mut effects = initial;

        // A no-progress interval consumes budget and can expand the bounded
        // selected window. A progress interval only rearms: it does not reset
        // the already consumed rippled timeout count.
        for expected_timeouts in 1..=3 {
            effects = runner.handle_event(AcquisitionEvent::TimerFired {
                operation: timer_operation(&effects),
                timer: TimerKind::AcquireTimeout,
            });
            assert_eq!(
                runner
                    .session(session)
                    .expect("live session")
                    .plan()
                    .timeouts(),
                expected_timeouts
            );
            assert!(
                runner
                    .session(session)
                    .expect("live session")
                    .sent_peers()
                    .len()
                    <= MAX_SELECTED_PEERS
            );

            runner
                .state
                .sessions
                .get_mut(&session)
                .expect("live session")
                .plan
                .note_progress();
            effects = runner.handle_event(AcquisitionEvent::TimerFired {
                operation: timer_operation(&effects),
                timer: TimerKind::AcquireTimeout,
            });
            assert_eq!(
                runner
                    .session(session)
                    .expect("live session")
                    .plan()
                    .timeouts(),
                expected_timeouts,
                "a progress interval must not erase prior no-progress budget"
            );
        }
    }

    #[test]
    fn seeded_no_progress_timeout_reprobes_and_resends_exact_frontier() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let node = PlanNetworkNeed::new(
            SHAMapNodeId::default(),
            Uint256::from(0x77),
            ledger::TreeKind::Transaction,
        );
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsNetworkWithKind(
                vec![node],
            )])),
        );
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new((1..=6).map(PeerId::new).collect()),
        ));
        let initial = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&initial);
        let initial_timer = timer_operation(&initial);
        let seed = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let initial_frontier = seed
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request)
                    if matches!(request.request(), LedgerDataRequest::GetLedgerNodes { .. }) =>
                {
                    Some(request.clone())
                }
                _ => None,
            })
            .expect("seeded plan must request its normal frontier");

        // The Base seed was useful, so rippled's `wasProgress` interval only
        // rearms; it must not manufacture a timeout recovery request yet.
        let first = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: initial_timer,
            timer: TimerKind::AcquireTimeout,
        });
        assert!(read_effects(&first).is_empty());
        assert!(
            !first
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
        );

        // The next quiet interval is a seeded no-progress timeout. It submits
        // bounded async local reprobes and resends the exact transaction-node
        // frontier with fresh operation identities, including one bounded peer
        // escalation from the initial five peers to peer six.
        let second = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: timer_operation(&first),
            timer: TimerKind::AcquireTimeout,
        });
        let reads = read_effects(&second);
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].key(), SHAMapHash::new(Uint256::from(0x77)));
        assert_eq!(reads[0].operation().session(), session);
        let normal = second
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request)
                    if matches!(request.request(), LedgerDataRequest::GetLedgerNodes { .. }) =>
                {
                    Some(request)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(normal.len(), 6);
        assert!(normal.iter().all(|request| {
            request.operation() != initial_frontier.operation()
                && matches!(
                    request.request(),
                    LedgerDataRequest::GetLedgerNodes {
                        kind: ledger::TreeKind::Transaction,
                        node_ids,
                        sequence: 1,
                        query_depth: 0,
                        indirect: true,
                    } if node_ids == &vec![SHAMapNodeId::default()]
                )
        }));

        // After rippled's `timeouts > 4` threshold the same retained frontier
        // switches to bounded by-hash requests, still with fresh operations.
        let mut effects = second;
        for _ in 0..4 {
            for read in read_effects(&effects) {
                let _ = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
                    read.operation(),
                    ReadOutcome::Settled { node: None },
                )));
            }
            effects = runner.handle_event(AcquisitionEvent::TimerFired {
                operation: timer_operation(&effects),
                timer: TimerKind::AcquireTimeout,
            });
        }
        assert!(effects.iter().any(|effect| {
            matches!(
                effect,
                AcquisitionEffect::SendLedgerRequest(request)
                    if matches!(request.request(), LedgerDataRequest::GetNodes { nodes, sequence: Some(1) }
                        if nodes == &vec![crate::peer::LedgerNodeRequest::new(
                            Uint256::from(0x77),
                            ledger::TreeKind::Transaction,
                        )])
            )
        }));
    }

    #[test]
    fn repeated_timeouts_under_global_saturation_keep_one_exact_queued_retry() {
        let node = state_network_need(0x77);
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsNetworkWithKind(
                vec![node],
            )])),
        );
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new((1..=6).map(PeerId::new).collect()),
        ));
        let initial = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&initial);
        let _seeded = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));

        // Saturate the global pool with unrelated exact operations. The
        // session timeout releases only its own requests, so none of these
        // credits become available during the retry sequence.
        runner.release_session_request_credits(session);
        let blocker = SessionRef::new(
            RunEpoch::new(99),
            SessionId::new(99),
            Uint256::from(99),
            PlanEpoch::new(1),
            StoreGeneration::new(1),
        );
        for id in 1..=MAX_OUTBOUND_REQUESTS_GLOBAL as u64 {
            runner.state.outbound.outstanding.insert(
                OperationRef::new(
                    blocker,
                    OperationKind::PeerRequest,
                    OperationId::new(id),
                    OperationGeneration::new(id),
                ),
                PeerId::new(99),
            );
        }

        // The first interval observed seed progress. Every later interval is a
        // no-progress retry of the same retained frontier. Settling local
        // reprobes lets the next network timeout execute without adding plan
        // progress.
        let mut effects = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: timer_operation(&initial),
            timer: TimerKind::AcquireTimeout,
        });
        assert!(
            effects
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
        );
        for _ in 0..4 {
            effects = runner.handle_event(AcquisitionEvent::TimerFired {
                operation: timer_operation(&effects),
                timer: TimerKind::AcquireTimeout,
            });
            for read in read_effects(&effects) {
                let _ = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
                    read.operation(),
                    ReadOutcome::Settled { node: None },
                )));
            }
            assert!(
                effects
                    .iter()
                    .all(|effect| !matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
            );
            assert!(runner.state.outbound.intents.len() <= 6);
            assert!(
                runner
                    .state
                    .outbound
                    .intents
                    .iter()
                    .enumerate()
                    .all(|(index, intent)| runner
                        .state
                        .outbound
                        .intents
                        .iter()
                        .skip(index + 1)
                        .all(|other| other != intent))
            );
        }
        assert_eq!(runner.state.outbound.intents.len(), 6);
        assert!(runner.state.outbound.intents.iter().all(|intent| {
            intent.session == session
                && matches!(intent.request, LedgerDataRequest::GetLedgerNodes { .. })
        }));
        assert!(runner.state.outbound.intents.len() <= MAX_QUEUED_REQUEST_INTENTS);
    }

    #[test]
    fn consensus_capacity_preserves_anchor_and_preempts_only_lower_priority_work() {
        let budget = BudgetState::new(1, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let first = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            target(1),
            AcquireReason::Consensus,
        )));
        let first_session = peer_request_session(&first);

        // A moving preferred observation remains policy metadata without
        // cancelling or displacing the exact active recovery owner.
        let deferred = runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(target(2), AcquireReason::Consensus),
        ));
        assert!(deferred.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::CancelSession(_) | AcquisitionEffect::SessionStarted(_)
        )));
        assert_eq!(
            runner.session(first_session).expect("first").phase(),
            &SessionPhase::Active
        );
        assert!(!runner.has_deferred_consensus_target(target(2)));
        assert_eq!(runner.state.latest_consensus_target, Some(target(2)));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(1) });

        // Generic pressure still cannot consume the only retained slot.
        let generic = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(3),
            reason: AcquireReason::Generic,
        });
        assert!(
            !generic
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SessionStarted(_)))
        );

        // When lower-priority work is the occupant, consensus starts now by
        // cancelling only the pre-fence Generic session, never a handoff.
        let mut priority = CoordinatorRunner::with_budget(RunEpoch::new(2), budget);
        connect(&mut priority);
        let generic = priority.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(4),
            reason: AcquireReason::Generic,
        });
        let generic_session = peer_request_session(&generic);
        let consensus = priority.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(target(5), AcquireReason::Consensus),
        ));
        assert!(consensus.contains(&AcquisitionEffect::CancelSession(generic_session)));
        assert!(consensus.iter().any(|effect| {
            matches!(effect, AcquisitionEffect::SessionStarted(session) if session.target_hash() == target(5).hash())
        }));
    }

    #[test]
    fn reply_driven_network_request_uses_the_replying_peer() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsNetwork(vec![(
                SHAMapNodeId::default(),
                Uint256::from(3),
            )])])),
        );
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1), PeerId::new(2), PeerId::new(3)]),
        ));
        let initial = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&initial);

        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(
            admitted_packet_from_peer(session, PeerId::new(3), AdmissionBudget::new(1, 256), 8),
        ));
        let requests = effects
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(requests.len(), 1);
        assert_eq!(requests[0].peer_id(), PeerId::new(3));
        assert!(matches!(
            requests[0].request(),
            LedgerDataRequest::GetLedgerNodes {
                query_depth: 1,
                indirect: false,
                ..
            }
        ));
    }

    #[test]
    fn reply_driven_duplicate_nodes_are_suppressed_after_header_fanout() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let node = (SHAMapNodeId::default(), Uint256::from(3));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![
                ScriptedStep::NeedsNetwork(vec![node]),
                ScriptedStep::NeedsNetwork(vec![node]),
            ])),
        );
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1), PeerId::new(2)]),
        ));
        let session = peer_request_session(&acquire_with_effects(&mut runner, 10));

        let first = runner.handle_event(AcquisitionEvent::PacketAdmitted(
            admitted_packet_from_peer(session, PeerId::new(1), AdmissionBudget::new(1, 256), 8),
        ));
        assert_eq!(
            first
                .iter()
                .filter(|effect| matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
                .count(),
            1
        );

        // A second header reply from another initial-fanout peer discovers the
        // same missing node. As in rippled `filterNodes(..., Reply)`, it must
        // not emit a duplicate request or add that peer to the request set.
        let duplicate = runner.handle_event(AcquisitionEvent::PacketAdmitted(
            admitted_packet_from_peer(session, PeerId::new(2), AdmissionBudget::new(1, 256), 8),
        ));
        assert!(
            duplicate
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SendLedgerRequest(_)))
        );
        assert_eq!(runner.snapshot().peer_requests(), 3); // two Base + one node
        assert_eq!(
            runner.session(session).expect("live session").sent_peers(),
            &BTreeSet::from([PeerId::new(1), PeerId::new(2)])
        );
    }

    #[test]
    fn terminal_sessions_do_not_consume_live_session_capacity() {
        let budget = BudgetState::new(1, AdmissionBudget::default(), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let first = acquire(&mut runner, 1);

        let effects = runner.handle_event(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));
        assert!(effects.contains(&AcquisitionEffect::CancelSession(first)));
        assert!(
            runner
                .session(first)
                .expect("terminal session")
                .phase()
                .is_terminal()
        );

        let effects = acquire_with_effects(&mut runner, 2);
        assert!(effects.iter().any(|effect| {
            matches!(effect, AcquisitionEffect::SendLedgerRequest(request)
                if request.session().target_hash() == Uint256::from(2))
        }));
        assert_eq!(runner.snapshot().rejected_events(), 0);
    }

    #[test]
    fn completions_require_exact_session_liveness_and_kind() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let session = acquire(&mut runner, 10);

        // A read completion whose operation is not the exact in-flight read is
        // stale even for a live session: a target hash alone never authorizes
        // a result.
        let read = OperationRef::new(
            session,
            OperationKind::Read,
            OperationId::new(1),
            OperationGeneration::new(1),
        );
        runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            read,
            ReadOutcome::Settled { node: None },
        )));
        assert_eq!(runner.snapshot().stale_events(), 1);

        // A completion with the wrong operation kind is stale.
        let wrong_kind = OperationRef::new(
            session,
            OperationKind::Timer,
            OperationId::new(1),
            OperationGeneration::new(1),
        );
        runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            wrong_kind,
            ReadOutcome::Settled { node: None },
        )));
        assert_eq!(runner.snapshot().stale_events(), 2);

        // A completion for an unknown session is stale.
        let foreign = SessionRef::new(
            RunEpoch::new(1),
            SessionId::new(999),
            Uint256::from(999),
            PlanEpoch::new(1),
            StoreGeneration::new(1),
        );
        let read = OperationRef::new(
            foreign,
            OperationKind::Read,
            OperationId::new(1),
            OperationGeneration::new(1),
        );
        runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            read,
            ReadOutcome::Settled { node: None },
        )));
        assert_eq!(runner.snapshot().stale_events(), 3);
    }

    #[test]
    fn durability_fence_and_handoff_ack_require_a_live_session() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let session = acquire(&mut runner, 10);

        // A fence whose operation is not an exact in-flight fence is stale
        // even for a live session: a target hash alone never authorizes a
        // result, and durability never adopts provisionally.
        let fence = OperationRef::new(
            session,
            OperationKind::DurabilityFence,
            OperationId::new(1),
            OperationGeneration::new(1),
        );
        runner.handle_event(AcquisitionEvent::DurabilityFenced(
            DurabilityCompletion::new(fence, crate::io::DurabilityOutcome::Passed),
        ));
        assert_eq!(runner.snapshot().stale_events(), 1);

        // A handoff ack for a session that never issued a handoff is stale:
        // only the exact pending handoff id authorizes finalization.
        runner.handle_event(AcquisitionEvent::DurableHandoffAcknowledged(
            DurableHandoffAcknowledgement::new(DurableHandoffId::new(1), session),
        ));
        assert_eq!(runner.snapshot().stale_events(), 2);
        assert_eq!(runner.snapshot().sessions_completed(), 0);

        // A matching local LCL cancellation makes later fence facts stale;
        // peer loss alone only demotes service phase and preserves the session.
        let effects = runner.handle_event(AcquisitionEvent::LclInstalled(identity(10)));
        assert!(effects.contains(&AcquisitionEffect::CancelSession(session)));
        runner.handle_event(AcquisitionEvent::DurabilityFenced(
            DurabilityCompletion::new(fence, crate::io::DurabilityOutcome::Passed),
        ));
        assert_eq!(runner.snapshot().stale_events(), 3);
    }

    #[test]
    fn shutdown_produces_stopping_and_no_further_effects() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let session = acquire(&mut runner, 10);

        let effects = runner.handle_event(AcquisitionEvent::Shutdown);
        assert!(effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Stopping)));
        assert!(effects.contains(&AcquisitionEffect::CancelSession(session)));
        assert_eq!(runner.phase(), &SyncPhase::Stopping);
        assert!(runner.snapshot().shutdown());

        // Post-shutdown events produce no effects and are stale.
        let effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(20),
            reason: AcquireReason::Consensus,
        });
        assert!(effects.is_empty());
        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        assert!(effects.is_empty());
        // Post-shutdown events are stale, so the peer view is frozen at its
        // last accepted snapshot.
        assert_eq!(runner.snapshot().stale_events(), 2);
        assert_eq!(runner.snapshot().peer_count(), 1);
    }

    #[test]
    fn max_sessions_keeps_moving_consensus_as_metadata_without_cancelling_anchor() {
        let budget = BudgetState::new(1, AdmissionBudget::default(), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let first = peer_request_session(&runner.handle_event(AcquisitionEvent::ConsensusTarget(
            ConsensusTarget::new(target(1), AcquireReason::Consensus),
        )));

        let effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            target(2),
            AcquireReason::Consensus,
        )));
        assert!(effects.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::CancelSession(_) | AcquisitionEffect::SessionStarted(_)
        )));
        assert_eq!(
            runner.session(first).expect("first").phase(),
            &SessionPhase::Active
        );
        assert!(!runner.has_deferred_consensus_target(target(2)));
        assert_eq!(runner.state.latest_consensus_target, Some(target(2)));
        assert_eq!(runner.snapshot().session_count(), 1);
        assert_eq!(runner.snapshot().rejected_events(), 0);
    }

    #[test]
    fn local_lcl_install_drives_connected_to_tracking_without_acquisition() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        assert_eq!(runner.phase(), &SyncPhase::Connected);

        // A locally resident preferred LCL installed while Connected (no
        // acquisition was needed) drives Connected -> Tracking, matching
        // rippled switchLastClosedLedger clearing needNetworkLedger.
        let effects = runner.handle_event(AcquisitionEvent::LclInstalled(identity(9)));
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Tracking {
                lcl: identity(9)
            })]
        );

        // Tracking -> Full still requires a fresh matching publication.
        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(9),
            fresh: false,
        });
        assert!(effects.is_empty());
        assert_eq!(runner.phase(), &SyncPhase::Tracking { lcl: identity(9) });
        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(9),
            fresh: true,
        });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Full {
                lcl: identity(9),
                published: identity(9)
            })]
        );
    }

    #[test]
    fn ordinary_preferred_target_after_lcl_install_does_not_demote_tracking() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let installed = identity(9);
        let _ = runner.handle_event(AcquisitionEvent::LclInstalled(installed));
        assert_eq!(runner.phase(), &SyncPhase::Tracking { lcl: installed });

        let next = target(10);
        let effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            next,
            AcquireReason::Consensus,
        )));
        assert!(effects.iter().any(|effect| matches!(
            effect,
            AcquisitionEffect::SessionStarted(session) if session.target_hash() == next.hash()
        )));
        assert!(effects.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::SetServicePhase(SyncPhase::Syncing { .. })
        )));
        assert_eq!(
            runner.phase(),
            &SyncPhase::Tracking { lcl: installed },
            "ordinary next-ledger fetch is not a needNetworkLedger fact",
        );

        let effects =
            runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: next });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                target: next,
            })],
        );
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: next });
    }

    #[test]
    fn ordinary_acquisitions_are_phase_neutral_after_lcl_install() {
        for phase in [
            SyncPhase::Tracking { lcl: identity(9) },
            SyncPhase::Full {
                lcl: identity(9),
                published: identity(9),
            },
        ] {
            for reason in [
                AcquireReason::Consensus,
                AcquireReason::Generic,
                AcquireReason::History,
            ] {
                let mut runner = CoordinatorRunner::with_phase(RunEpoch::new(1), phase);
                let _ = runner.handle_event(AcquisitionEvent::Connectivity(
                    PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
                ));
                let next = LedgerTarget::new(Uint256::from(10), Some(10));
                let effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
                    target: next,
                    reason,
                });
                assert!(effects.iter().any(|effect| matches!(
                    effect,
                    AcquisitionEffect::SessionStarted(session)
                        if session.target_hash() == next.hash()
                )));
                assert!(
                    effects
                        .iter()
                        .all(|effect| !matches!(effect, AcquisitionEffect::SetServicePhase(_)))
                );
                assert_eq!(runner.phase(), &phase);

                let divergence =
                    runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: next });
                assert_eq!(
                    divergence,
                    vec![AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                        target: next,
                    })]
                );
            }
        }
    }

    #[test]
    fn hash_only_consensus_probe_for_locally_installed_lcl_does_not_demote_full() {
        let mut runner = CoordinatorRunner::with_phase(
            RunEpoch::new(1),
            SyncPhase::Full {
                lcl: identity(9),
                published: identity(9),
            },
        );
        // Full already has peer capability in production. This establishes the
        // same peer view without treating a redundant capability fact as a
        // service-phase transition.
        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1)]),
        ));
        assert!(effects.is_empty());

        let target = LedgerTarget::new(Uint256::from(10), None);
        let effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target,
            reason: AcquireReason::Consensus,
        });
        let session = peer_request_session(&effects);
        assert!(
            !effects.iter().any(|effect| matches!(
                effect,
                AcquisitionEffect::SetServicePhase(SyncPhase::Syncing { .. })
            )),
            "a hash-only local consensus probe must not demote Full before remote work exists"
        );
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl: identity(9),
                published: identity(9),
            }
        );

        // A matching peer Base reply can arrive before the local consensus
        // child is installed. It proves the object is available but not that
        // the preferred LCL diverged. In rippled, only consensusViewChange's
        // explicit divergence path changes mode, so this must remain Full.
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        assert!(
            !effects
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SetServicePhase(_))),
            "a peer reply for a hash-only local consensus probe must not demote Full"
        );
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl: identity(9),
                published: identity(9),
            }
        );

        // The exact locally produced child is then installed. It cancels the
        // pre-fence probe while Full remains stable; its matching fresh
        // publication refreshes Full's identities in place without a visible
        // mode transition.
        let effects = runner.handle_event(AcquisitionEvent::LclInstalled(identity(10)));
        assert!(
            !effects
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SetServicePhase(_))),
            "a newer local LCL must not emit a redundant Full -> Tracking transition"
        );
        assert!(effects.contains(&AcquisitionEffect::CancelSession(session)));
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl: identity(10),
                published: identity(9),
            }
        );
        assert_eq!(
            runner
                .snapshot()
                .cancelled_by_reason()
                .get(&CancelReason::LclInstalled),
            Some(&1)
        );

        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(10),
            fresh: true,
        });
        assert!(effects.is_empty());
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl: identity(10),
                published: identity(10),
            }
        );
    }

    #[test]
    fn full_publication_advances_without_claiming_a_new_local_lcl() {
        let mut runner = CoordinatorRunner::with_phase(
            RunEpoch::new(1),
            SyncPhase::Full {
                lcl: identity(9),
                published: identity(9),
            },
        );

        // The adapter has proven ledger 10 is a descendant of the local LCL.
        // Advance only the publication identity until LclInstalled catches up.
        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(10),
            fresh: true,
        });
        assert!(effects.is_empty());
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl: identity(9),
                published: identity(10),
            }
        );

        // A later exact local-LCL fact advances the independent Full LCL in
        // place without causing a visible Full -> Tracking cycle.
        let _ = runner.handle_event(AcquisitionEvent::LclInstalled(identity(10)));
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl: identity(10),
                published: identity(10),
            }
        );
        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(11),
            fresh: true,
        });
        assert!(effects.is_empty());
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl: identity(10),
                published: identity(11),
            }
        );

        // Freshness gates only Tracking -> Full. Once Full, the coordinator
        // still mirrors a newer contiguous LedgerMaster publication head.
        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(12),
            fresh: false,
        });
        assert!(effects.is_empty());
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl: identity(10),
                published: identity(12),
            }
        );
    }

    #[test]
    fn lcl_installed_and_publication_drive_tracking_and_full() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let session = acquire(&mut runner, 9);
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(9) });

        // LCL installation for a hash that is not the syncing target is ignored.
        let effects = runner.handle_event(AcquisitionEvent::LclInstalled(identity(99)));
        assert!(effects.is_empty());
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: target(9) });

        // The matching LCL install drives Syncing -> Tracking and cancels the
        // no-longer-needed pre-fence acquisition before its timeout can fire.
        let effects = runner.handle_event(AcquisitionEvent::LclInstalled(identity(9)));
        assert!(
            effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Tracking {
                lcl: identity(9)
            }))
        );
        assert!(effects.contains(&AcquisitionEffect::CancelSession(session)));
        assert_eq!(
            runner
                .snapshot()
                .cancelled_by_reason()
                .get(&CancelReason::LclInstalled),
            Some(&1)
        );

        // A stale (non-fresh) publication never promotes Tracking -> Full even
        // for the matching chain head; the coordinator owns the freshness gate.
        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(9),
            fresh: false,
        });
        assert!(effects.is_empty());
        assert_eq!(runner.phase(), &SyncPhase::Tracking { lcl: identity(9) });

        // The matching, fresh publication drives Tracking -> Full.
        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(9),
            fresh: true,
        });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Full {
                lcl: identity(9),
                published: identity(9)
            })]
        );
    }

    #[test]
    fn fresh_contiguous_published_anchor_behind_lcl_promotes_full() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        acquire(&mut runner, 10);
        let _ = runner.handle_event(AcquisitionEvent::LclInstalled(identity(10)));

        // NetworkOps has proven ledger 9 is the contiguous published anchor of
        // the installed LCL. This is the post-restart condition from rippled
        // endConsensus: publication may lag the closed ledger while the open
        // ledger is fresh, and the node must still regain proposing mode.
        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(9),
            fresh: true,
        });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Full {
                lcl: identity(10),
                published: identity(9),
            })]
        );
    }

    #[test]
    fn fresh_contiguous_published_descendant_ahead_of_lcl_promotes_full() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        acquire(&mut runner, 10);
        let _ = runner.handle_event(AcquisitionEvent::LclInstalled(identity(10)));

        // NetworkOps proved that published ledger 12 names local LCL 10 as an
        // ancestor. Rippled's Full gate is current-open freshness, so the
        // publication being ahead while the local LCL catches up is valid.
        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(12),
            fresh: true,
        });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Full {
                lcl: identity(10),
                published: identity(12),
            })]
        );
    }

    #[test]
    fn newer_lcl_refreshes_tracking_identity_before_publication() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        acquire(&mut runner, 9);
        let _ = runner.handle_event(AcquisitionEvent::LclInstalled(identity(9)));

        let effects = runner.handle_event(AcquisitionEvent::LclInstalled(identity(10)));
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Tracking {
                lcl: identity(10)
            })]
        );
        assert_eq!(runner.phase(), &SyncPhase::Tracking { lcl: identity(10) });

        let effects = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(10),
            fresh: true,
        });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Full {
                lcl: identity(10),
                published: identity(10),
            })]
        );
    }

    #[test]
    fn heartbeat_republishes_only_normalizable_phases() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));

        // Disconnected: no re-publish; recovery is owned by the connectivity
        // fact, not the heartbeat.
        let effects = runner.handle_event(AcquisitionEvent::Heartbeat);
        assert!(effects.is_empty());
        assert_eq!(runner.phase(), &SyncPhase::Disconnected);

        // Connected re-publishes so the phase port re-applies validated-age
        // normalization (rippled processHeartbeatTimer parity).
        connect(&mut runner);
        let effects = runner.handle_event(AcquisitionEvent::Heartbeat);
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Connected)]
        );
        assert_eq!(runner.phase(), &SyncPhase::Connected);

        // Syncing re-publishes for the same reason.
        acquire(&mut runner, 9);
        let effects = runner.handle_event(AcquisitionEvent::Heartbeat);
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                target: target(9)
            })]
        );

        // Tracking and Full are never reasserted (matching
        // heartbeat_operating_mode_reassertion).
        let _ = runner.handle_event(AcquisitionEvent::LclInstalled(identity(9)));
        let effects = runner.handle_event(AcquisitionEvent::Heartbeat);
        assert!(effects.is_empty());
        assert_eq!(runner.phase(), &SyncPhase::Tracking { lcl: identity(9) });
        let _ = runner.handle_event(AcquisitionEvent::PublicationCommitted {
            identity: identity(9),
            fresh: true,
        });
        let effects = runner.handle_event(AcquisitionEvent::Heartbeat);
        assert!(effects.is_empty());
        assert_eq!(
            runner.phase(),
            &SyncPhase::Full {
                lcl: identity(9),
                published: identity(9)
            }
        );
    }

    #[test]
    fn events_handled_counts_every_dispatched_event() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        acquire(&mut runner, 1);
        acquire(&mut runner, 2);
        assert_eq!(runner.snapshot().events_handled(), 5);
        assert_eq!(runner.snapshot().sessions_started(), 2);
    }

    #[test]
    fn session_retains_the_timer_it_armed() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let effects = acquire_with_effects(&mut runner, 7);
        let session = peer_request_session(&effects);
        let timer_op = timer_operation(&effects);
        let (kind, pending) = runner
            .session(session)
            .expect("live session")
            .pending_timer()
            .expect("a timer must be armed");
        assert_eq!(kind, TimerKind::AcquireTimeout);
        assert_eq!(pending, timer_op);
    }

    /// A deterministic one-shot [`PlanSeed`]: the first Base packet builds a
    /// [`ScriptedEngine`] whose scripted steps run once per advance.
    #[derive(Debug, Clone)]
    struct ScriptedSeed {
        steps: VecDeque<ScriptedStep>,
        durable: Option<Arc<ledger::Ledger>>,
    }

    impl ScriptedSeed {
        fn new(steps: Vec<ScriptedStep>) -> Self {
            Self {
                steps: steps.into(),
                durable: None,
            }
        }

        /// Attaches a durable ledger the built engine yields at the M5 handoff.
        fn with_durable_ledger(mut self, ledger: Arc<ledger::Ledger>) -> Self {
            self.durable = Some(ledger);
            self
        }
    }

    impl PlanSeed for ScriptedSeed {
        fn build(
            &mut self,
            session: SessionRef,
            _header: &ledger::InboundLedgerPacket,
        ) -> Option<Box<dyn TreeEngine + Send + Sync>> {
            let engine = ScriptedEngine::new(
                TreePlanId::new(session.session_id().get() + 1),
                std::mem::take(&mut self.steps),
                Vec::new(),
            )
            .with_persistence_sequence(1);
            let engine = match self.durable.take() {
                Some(durable) => engine.with_durable_ledger(durable),
                None => engine,
            };
            Some(Box::new(engine))
        }
    }

    fn read_effects(effects: &[AcquisitionEffect]) -> Vec<crate::io::ReadRequest> {
        effects
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SubmitRead(request) => Some(request.clone()),
                _ => None,
            })
            .collect()
    }

    fn write_batch(effects: &[AcquisitionEffect]) -> crate::io::WriteBatch {
        effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SubmitWrite(batch) => Some(batch.clone()),
                _ => None,
            })
            .expect("a write batch effect must be emitted")
    }

    fn durable_handoff(effects: &[AcquisitionEffect]) -> DurableLedger {
        effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::PublishDurable(ledger) => Some(ledger.clone()),
                _ => None,
            })
            .expect("a durable handoff effect must be emitted")
    }

    fn immutable_ledger(seq: u32) -> Arc<ledger::Ledger> {
        let header = ledger::LedgerHeader {
            seq,
            ..ledger::LedgerHeader::default()
        };
        let mut ledger = ledger::Ledger::new(header, false);
        ledger.set_immutable(true);
        Arc::new(ledger)
    }

    #[test]
    fn base_packet_seeds_the_plan_and_drives_a_read() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsReads(vec![
                PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(7)),
                    10,
                    SHAMapNodeId::default(),
                    0,
                ),
            ])])),
        );
        connect(&mut runner);
        let session = acquire(&mut runner, 10);

        let packet = admitted_packet(session, AdmissionBudget::new(1, 256), 8);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(packet));
        let reads = read_effects(&effects);
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].operation().kind(), OperationKind::Read);
        assert_eq!(reads[0].key(), SHAMapHash::new(Uint256::from(7)));
        assert_eq!(reads[0].ledger_sequence(), 10);
        // The header packet was fed and consumed; no queue remains.
        assert_eq!(runner.session(session).expect("live").packet_count(), 0);
        assert_eq!(runner.snapshot().plan_turns(), 1);
    }

    #[test]
    fn local_reconstruction_does_not_consume_network_timeout_or_idle_expiry() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![
                ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(7)),
                    10,
                    SHAMapNodeId::default(),
                    0,
                )]),
                ScriptedStep::NeedsNetwork(vec![(SHAMapNodeId::default(), Uint256::from(8))]),
            ])),
        );
        connect(&mut runner);
        let started = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&started);
        let expiry = expiry_operation(&started);
        let seeded = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let read = read_effects(&seeded)[0].operation();
        // Model the initial header probe losing the race to this Base packet;
        // production clears it when the exact broker callback settles.
        runner
            .state
            .sessions
            .get_mut(&session)
            .expect("live session")
            .pending_header_read = None;

        let expiry_effects = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: expiry,
            timer: TimerKind::SessionExpiry,
        });
        assert!(runner.session(session).is_some());
        assert!(expiry_effects.is_empty());
        assert!(
            runner
                .handle_event(AcquisitionEvent::RegistrySweep)
                .is_empty()
        );
        assert!(runner.state.swept_local_scan_owners.contains(&session));

        // More than rippled's seven network no-progress ticks may pass while
        // the externalized equivalent of one synchronous local scan is still
        // awaiting its read batch. None may consume timeout budget.
        for _ in 0..9 {
            let operation = runner
                .session(session)
                .expect("local scan remains live")
                .pending_timer()
                .expect("deadline remains armed")
                .1;
            let effects = runner.handle_event(AcquisitionEvent::TimerFired {
                operation,
                timer: TimerKind::AcquireTimeout,
            });
            assert_eq!(runner.session(session).expect("live").plan().timeouts(), 0);
            assert!(effects.iter().all(|effect| matches!(
                effect,
                AcquisitionEffect::ArmTimer(request)
                    if request.timer() == TimerKind::AcquireTimeout
            )));
        }

        let network = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            read,
            ReadOutcome::Settled { node: None },
        )));
        assert!(network.contains(&AcquisitionEffect::CancelSession(session)));
        assert!(runner.session(session).is_none());
    }

    #[test]
    fn late_header_probe_cannot_restart_base_after_peer_seeded_graph() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsNetwork(vec![(
                SHAMapNodeId::default(),
                Uint256::from(8),
            )])])),
        );
        connect(&mut runner);
        let started = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&started);
        let header_read = read_effects(&started)
            .into_iter()
            .find(|request| request.operation().kind() == OperationKind::HeaderRead)
            .expect("initial header probe")
            .operation();
        let _ = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));

        let effects = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            header_read,
            ReadOutcome::Settled { node: None },
        )));
        assert!(effects.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::SendLedgerRequest(request)
                if matches!(request.request(), LedgerDataRequest::GetLedger { .. })
        )));
        assert!(
            runner
                .session(session)
                .expect("live")
                .plan()
                .engine()
                .is_some()
        );
    }

    #[test]
    fn moving_tips_admit_three_bounded_scans_and_waiters_hold_no_read_operations() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let mut sessions = Vec::new();
        let mut expiries = Vec::new();
        let mut owner_reads = Vec::new();

        for seq in 20..26 {
            let started = acquire_with_effects(&mut runner, seq);
            let session = peer_request_session(&started);
            sessions.push(session);
            expiries.push(expiry_operation(&started));
            let state = runner
                .state
                .sessions
                .get_mut(&session)
                .expect("new session");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(u64::from(seq)),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(u64::from(seq) + 1000)),
                    seq,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
            if seq == 24 {
                runner.state.latest_consensus_target = Some(target(seq));
            }
            let mut effects = Vec::new();
            runner.run_plan_turn(session, None, &mut effects);
            if let Some(read) = read_effects(&effects).first() {
                owner_reads.push((session, read.operation()));
            }
        }

        assert_eq!(runner.state.local_scan_owners.len(), MAX_LOCAL_SCAN_OWNERS);
        assert_eq!(owner_reads.len(), MAX_LOCAL_SCAN_OWNERS);
        assert_eq!(runner.state.local_scan_waiters.len(), 3);
        for session in &sessions[MAX_LOCAL_SCAN_OWNERS..] {
            assert_eq!(
                runner
                    .session(*session)
                    .expect("waiter")
                    .plan()
                    .pending_read_count(),
                0,
                "a waiting target must not mint or pin a 512-read operation batch"
            );
        }

        // A queued target models rippled's queued JtLedgerData lambda, whose
        // captured shared_ptr keeps the InboundLedger alive until the job
        // executes. The registry sweep marks it for reap at the eventual scan
        // boundary but must not cancel it out of the runnable FIFO.
        let swept = sessions[5];
        let eligible = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: expiries[5],
            timer: TimerKind::SessionExpiry,
        });
        assert!(eligible.is_empty());
        let effects = runner.handle_event(AcquisitionEvent::RegistrySweep);
        assert!(effects.is_empty());
        assert!(runner.state.local_scan_waiters.contains(&swept));
        assert!(runner.state.swept_local_scan_owners.contains(&swept));
        assert!(!runner.live_sessions().any(|session| session == swept));

        // At completed read-batch boundaries, a moving policy observation
        // cannot displace the latched owner. Non-anchor waiters remain FIFO.
        let first_release = runner.handle_event(AcquisitionEvent::ReadCompleted(
            ReadCompletion::new(owner_reads[0].1, ReadOutcome::Settled { node: None }),
        ));
        assert!(
            read_effects(&first_release)
                .iter()
                .any(|read| read.operation().session() == sessions[3])
        );
        let second_release = runner.handle_event(AcquisitionEvent::ReadCompleted(
            ReadCompletion::new(owner_reads[1].1, ReadOutcome::Settled { node: None }),
        ));
        assert!(
            read_effects(&second_release)
                .iter()
                .any(|read| read.operation().session() == sessions[4])
        );
        let third_release = runner.handle_event(AcquisitionEvent::ReadCompleted(
            ReadCompletion::new(owner_reads[2].1, ReadOutcome::Settled { node: None }),
        ));
        let swept_read = read_effects(&third_release)
            .iter()
            .find(|read| read.operation().session() == swept)
            .expect("the sweep-marked queued job must run before it can be reaped")
            .operation();
        assert_eq!(runner.state.local_scan_owners.len(), MAX_LOCAL_SCAN_OWNERS);

        let boundary = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            swept_read,
            ReadOutcome::Settled { node: None },
        )));
        assert!(boundary.contains(&AcquisitionEffect::CancelSession(swept)));
        assert!(runner.session(swept).is_none());
    }

    #[test]
    fn queued_scan_waiter_defers_network_timeout_budget_until_job_runs() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let mut waiter = None;
        let mut first_owner_read = None;

        for seq in 20..24 {
            let started = acquire_with_effects(&mut runner, seq);
            let session = peer_request_session(&started);
            let state = runner.state.sessions.get_mut(&session).expect("session");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(u64::from(seq)),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(u64::from(seq) + 50_000)),
                    seq,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
            let mut effects = Vec::new();
            runner.run_plan_turn(session, None, &mut effects);
            if seq == 20 {
                first_owner_read = read_effects(&effects).first().map(|read| read.operation());
            }
            if seq == 23 {
                waiter = Some(session);
            }
        }

        let waiter = waiter.expect("fourth session");
        assert!(runner.state.local_scan_waiters.contains(&waiter));
        assert!(!runner.state.local_scan_owners.contains(&waiter));
        assert_eq!(runner.session(waiter).expect("waiter").plan().timeouts(), 0);
        // More than the seven true network no-progress intervals may elapse
        // while this logical JtLedgerData job is queued. Every wake rearms one
        // exact timer without consuming budget or disturbing FIFO priority.
        for _ in 0..9 {
            let operation = runner
                .session(waiter)
                .expect("waiter remains live")
                .pending_timer()
                .expect("acquisition timer remains armed")
                .1;
            let effects = runner.handle_event(AcquisitionEvent::TimerFired {
                operation,
                timer: TimerKind::AcquireTimeout,
            });
            assert_eq!(runner.session(waiter).expect("waiter").plan().timeouts(), 0);
            assert!(runner.state.local_scan_waiters.contains(&waiter));
            assert!(effects.iter().all(|effect| matches!(
                effect,
                AcquisitionEffect::ArmTimer(request)
                    if request.timer() == TimerKind::AcquireTimeout
            )));
        }

        // The deferred timer did not steal or cancel the job: releasing the
        // oldest owner resumes this sole waiter with its first read batch.
        let resumed = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            first_owner_read.expect("first owner read"),
            ReadOutcome::Settled { node: None },
        )));
        assert!(
            read_effects(&resumed)
                .iter()
                .any(|read| read.operation().session() == waiter)
        );
    }

    #[test]
    fn swept_detached_scan_does_not_consume_live_session_capacity() {
        let budget = BudgetState::new(1, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let first_effects = acquire_with_effects(&mut runner, 20);
        let first = peer_request_session(&first_effects);
        runner.state.local_scan_owners.insert(first);
        let expiry = expiry_operation(&first_effects);
        let _ = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: expiry,
            timer: TimerKind::SessionExpiry,
        });
        assert!(
            runner
                .handle_event(AcquisitionEvent::RegistrySweep)
                .is_empty()
        );
        assert!(runner.state.swept_local_scan_owners.contains(&first));

        let second_effects = acquire_with_effects(&mut runner, 21);
        assert!(second_effects.iter().any(|effect| matches!(
            effect,
            AcquisitionEffect::SessionStarted(session) if session.target_hash() == target(21).hash()
        )));
        let snapshot = runner.snapshot();
        assert_eq!(snapshot.session_count(), 2);
        assert_eq!(snapshot.detached_sessions(), 1);
        assert_eq!(
            snapshot.active_by_reason().get(&AcquireReason::Consensus),
            Some(&1)
        );
    }

    #[test]
    fn deferred_consensus_replay_ignores_swept_detached_scan() {
        let budget = BudgetState::new(1, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let first_effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(20),
            reason: AcquireReason::Generic,
        });
        let detached = peer_request_session(&first_effects);
        runner.state.local_scan_owners.insert(detached);
        let _ = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: expiry_operation(&first_effects),
            timer: TimerKind::SessionExpiry,
        });
        assert!(
            runner
                .handle_event(AcquisitionEvent::RegistrySweep)
                .is_empty()
        );
        assert!(runner.state.swept_local_scan_owners.contains(&detached));

        let deferred = target(21);
        runner.state.deferred_consensus_acquire = Some(deferred);
        let effects = runner.handle_event(AcquisitionEvent::Heartbeat);

        assert!(effects.iter().any(|effect| matches!(
            effect,
            AcquisitionEffect::SessionStarted(session) if session.target_hash() == deferred.hash()
        )));
        assert_eq!(runner.state.deferred_consensus_acquire, None);
        assert!(runner.state.swept_local_scan_owners.contains(&detached));
        assert_eq!(
            runner
                .session(detached)
                .expect("detached continuation")
                .phase(),
            &SessionPhase::Active
        );
    }

    #[test]
    fn capacity_preemption_never_cancels_swept_detached_scan() {
        let budget = BudgetState::new(1, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let first_effects = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(20),
            reason: AcquireReason::History,
        });
        let detached = peer_request_session(&first_effects);
        runner.state.local_scan_owners.insert(detached);
        let _ = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: expiry_operation(&first_effects),
            timer: TimerKind::SessionExpiry,
        });
        let _ = runner.handle_event(AcquisitionEvent::RegistrySweep);
        assert!(runner.state.swept_local_scan_owners.contains(&detached));

        let live = peer_request_session(&runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(21),
            reason: AcquireReason::Consensus,
        }));
        let preferred = target(22);
        let effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            preferred,
            AcquireReason::Consensus,
        )));

        assert!(effects.iter().all(|effect| {
            !matches!(effect, AcquisitionEffect::CancelSession(session) if *session == detached)
        }));
        assert_eq!(
            runner
                .session(detached)
                .expect("detached continuation")
                .phase(),
            &SessionPhase::Active
        );
        assert_eq!(
            runner.session(live).expect("capacity owner").phase(),
            &SessionPhase::Active
        );
        assert!(runner.has_deferred_consensus_target(preferred));
    }

    #[test]
    fn completed_read_batch_retains_owner_until_natural_boundary() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let mut sessions = Vec::new();
        let mut owner_reads = Vec::new();
        let mut first_batch_reads = Vec::new();

        for seq in 30..34 {
            let started = acquire_with_effects(&mut runner, seq);
            let session = peer_request_session(&started);
            sessions.push(session);
            let state = runner.state.sessions.get_mut(&session).expect("session");
            state.pending_header_read = None;
            let first_needs = if seq == 30 {
                vec![
                    PlanReadNeed::new(
                        SHAMapHash::new(Uint256::from(10_030)),
                        seq,
                        SHAMapNodeId::default(),
                        0,
                    ),
                    PlanReadNeed::new(
                        SHAMapHash::new(Uint256::from(10_031)),
                        seq,
                        SHAMapNodeId::default(),
                        0,
                    ),
                ]
            } else {
                vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(u64::from(seq) + 10_000)),
                    seq,
                    SHAMapNodeId::default(),
                    0,
                )]
            };
            let steps = if seq < 33 {
                VecDeque::from([
                    ScriptedStep::NeedsReads(first_needs),
                    ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                        SHAMapHash::new(Uint256::from(u64::from(seq) + 20_000)),
                        seq,
                        SHAMapNodeId::default(),
                        0,
                    )]),
                ])
            } else {
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(40_000)),
                    seq,
                    SHAMapNodeId::default(),
                    0,
                )])])
            };
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(u64::from(seq)),
                steps,
                Vec::new(),
            ))));
            let mut effects = Vec::new();
            runner.run_plan_turn(session, None, &mut effects);
            if seq == 30 {
                first_batch_reads = read_effects(&effects)
                    .iter()
                    .map(|read| read.operation())
                    .collect();
            }
            if let Some(read) = read_effects(&effects).first() {
                owner_reads.push(read.operation());
            }
        }

        assert_eq!(owner_reads.len(), MAX_LOCAL_SCAN_OWNERS);
        assert_eq!(first_batch_reads.len(), 2);
        let preferred = sessions[3];
        runner.state.latest_consensus_target = Some(LedgerTarget::new(target(33).hash(), None));
        assert!(runner.state.local_scan_waiters.contains(&preferred));

        let turns_before_partial = runner.snapshot().plan_turns();
        let partial = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            first_batch_reads[0],
            ReadOutcome::Settled { node: None },
        )));
        assert_eq!(runner.snapshot().plan_turns(), turns_before_partial);
        assert!(
            read_effects(&partial)
                .iter()
                .all(|read| read.operation().session() != preferred)
        );
        assert!(runner.state.local_scan_owners.contains(&sessions[0]));

        let effects = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            first_batch_reads[1],
            ReadOutcome::Settled { node: None },
        )));
        assert!(
            read_effects(&effects)
                .iter()
                .all(|read| read.operation().session() != preferred)
        );
        let retained_owner_read = read_effects(&effects)
            .iter()
            .find(|read| read.operation().session() == sessions[0])
            .expect("the same synchronous-scan analogue owns the next deferred-read batch")
            .operation();
        assert!(runner.state.local_scan_owners.contains(&sessions[0]));
        assert!(runner.state.local_scan_waiters.contains(&preferred));

        // Once that job reaches its natural boundary, it releases the slot
        // and the preferred queued job may begin.
        let boundary = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            retained_owner_read,
            ReadOutcome::Settled { node: None },
        )));
        assert!(
            read_effects(&boundary)
                .iter()
                .any(|read| read.operation().session() == preferred)
        );
        assert!(runner.state.local_scan_owners.contains(&preferred));
        assert_eq!(runner.state.local_scan_owners.len(), MAX_LOCAL_SCAN_OWNERS);
    }

    #[test]
    fn admitted_reply_waiter_runs_before_a_new_preferred_scan() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let mut sessions = Vec::new();
        let mut owner_reads = Vec::new();

        for seq in 40..45 {
            let started = acquire_with_effects(&mut runner, seq);
            let session = peer_request_session(&started);
            sessions.push(session);
            let state = runner.state.sessions.get_mut(&session).expect("session");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(u64::from(seq)),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(u64::from(seq) + 30_000)),
                    seq,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
            let mut effects = Vec::new();
            runner.run_plan_turn(session, None, &mut effects);
            if let Some(read) = read_effects(&effects).first() {
                owner_reads.push(read.operation());
            }
        }

        assert_eq!(owner_reads.len(), MAX_LOCAL_SCAN_OWNERS);
        let reply_waiter = sessions[3];
        let newest_preferred = sessions[4];
        runner.state.latest_consensus_target = Some(target(44));
        assert_eq!(runner.state.latest_consensus_target, Some(target(44)));

        // A reply received while all three jobs are occupied remains retained
        // in its mailbox and queues the session for the next permit.
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            reply_waiter,
            AdmissionBudget::new(1, 256),
            8,
        )));
        assert!(effects.is_empty());
        assert_eq!(
            runner.session(reply_waiter).expect("live").packet_count(),
            1
        );

        // The queued JtLedgerData-equivalent work owns a logical shared
        // reference in rippled. Even if the registry sweep cadence lands
        // before a run slot opens, the reply and traversal must stay queued.
        let expiry = runner
            .session(reply_waiter)
            .expect("reply waiter")
            .pending_expiry_timer()
            .expect("expiry timer");
        assert!(
            runner
                .handle_event(AcquisitionEvent::TimerFired {
                    operation: expiry,
                    timer: TimerKind::SessionExpiry,
                })
                .is_empty()
        );
        assert!(
            runner
                .handle_event(AcquisitionEvent::RegistrySweep)
                .is_empty()
        );
        assert!(runner.session(reply_waiter).is_some());
        assert!(runner.state.local_scan_waiters.contains(&reply_waiter));
        assert!(runner.state.swept_local_scan_owners.contains(&reply_waiter));

        // Releasing a job must apply admitted data before allowing the moving
        // preferred target to jump the queue.  The Base packet is consumed and
        // the retained continuation immediately emits its first local read.
        let effects = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            owner_reads[0],
            ReadOutcome::Settled { node: None },
        )));
        assert!(
            read_effects(&effects)
                .iter()
                .any(|read| read.operation().session() == reply_waiter)
        );
        assert_eq!(
            runner.session(reply_waiter).expect("live").packet_count(),
            0
        );
        assert!(runner.state.local_scan_waiters.contains(&newest_preferred));
    }

    #[test]
    fn newer_packet_waiter_cannot_overtake_older_ordinary_scan() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let mut sessions = Vec::new();
        let mut owner_reads = Vec::new();

        for seq in 50..55 {
            let started = acquire_with_effects(&mut runner, seq);
            let session = peer_request_session(&started);
            sessions.push(session);
            let state = runner.state.sessions.get_mut(&session).expect("session");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(u64::from(seq)),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(u64::from(seq) + 35_000)),
                    seq,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
            let mut effects = Vec::new();
            runner.run_plan_turn(session, None, &mut effects);
            if let Some(read) = read_effects(&effects).first() {
                owner_reads.push(read.operation());
            }
        }

        let older_waiter = sessions[3];
        let newer_reply = sessions[4];
        assert!(
            runner
                .handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
                    newer_reply,
                    AdmissionBudget::new(1, 256),
                    8,
                )))
                .is_empty()
        );

        let effects = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            owner_reads[0],
            ReadOutcome::Settled { node: None },
        )));
        assert!(
            read_effects(&effects)
                .iter()
                .any(|read| read.operation().session() == older_waiter)
        );
        assert!(runner.state.local_scan_waiters.contains(&newer_reply));
    }

    #[test]
    fn incremental_writes_retain_three_owner_slots_until_natural_boundary() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let sessions = (70..74)
            .map(|seq| peer_request_session(&acquire_with_effects(&mut runner, seq)))
            .collect::<Vec<_>>();

        for (index, session) in sessions[..3].iter().enumerate() {
            let seq = 70 + index as u32;
            let state = runner.state.sessions.get_mut(session).expect("session");
            state.pending_header_read = None;
            assert!(
                state.plan.install_engine(Box::new(
                    ScriptedEngine::new(
                        TreePlanId::new(u64::from(seq)),
                        VecDeque::from([ScriptedStep::NeedsNetwork(vec![(
                            SHAMapNodeId::default(),
                            Uint256::from(u64::from(seq) + 40_000),
                        )])]),
                        vec![crate::io::PersistNode::new(
                            SHAMapHash::new(Uint256::from(u64::from(seq) + 50_000)),
                            bytes::Bytes::from_static(b"accepted-node"),
                            crate::io::StoredObjectKind::AccountNode,
                        )],
                    )
                    .with_persistence_sequence(seq),
                ))
            );
            runner.state.local_scan_owners.insert(*session);
        }

        let reply_waiter = sessions[3];
        {
            let state = runner
                .state
                .sessions
                .get_mut(&reply_waiter)
                .expect("reply waiter");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(74),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(60_000)),
                    73,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
        }
        assert!(
            runner
                .handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
                    reply_waiter,
                    AdmissionBudget::new(1, 256),
                    8,
                )))
                .is_empty()
        );
        assert!(runner.state.local_scan_waiters.contains(&reply_waiter));

        // Incremental persistence externalizes a step of the same logical
        // JtLedgerData job. It must retain its owner slot while pending, so the
        // fourth moving-tip session cannot create a fourth physical write.
        let mut first = Vec::new();
        runner.run_plan_turn(sessions[0], None, &mut first);
        let first_write = write_batch(&first);
        assert!(first_write.fence().is_none());
        assert!(
            read_effects(&first).is_empty(),
            "a pending incremental write must not admit the waiter"
        );
        assert!(runner.state.local_scan_owners.contains(&sessions[0]));

        let mut writes = vec![first_write];
        for session in &sessions[1..3] {
            let mut effects = Vec::new();
            runner.run_plan_turn(*session, None, &mut effects);
            let batch = write_batch(&effects);
            assert!(batch.fence().is_none());
            writes.push(batch);
            assert!(runner.state.local_scan_owners.contains(session));
        }
        assert_eq!(runner.state.local_scan_owners.len(), MAX_LOCAL_SCAN_OWNERS);
        assert!(runner.state.local_scan_waiters.contains(&reply_waiter));
        assert!(writes.iter().all(|batch| batch.fence().is_none()));

        // Only the exact old write completion resumes that same owner. Its
        // deferred network frontier is requested first; reaching that natural
        // boundary then releases the permit and admits the queued reply scan.
        let resumed = runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            writes[0].operation(),
            WriteOutcome::Accepted,
        )));
        assert!(resumed
            .iter()
            .any(|effect| matches!(effect, AcquisitionEffect::SendLedgerRequest(request) if request.session() == sessions[0])));
        assert!(
            read_effects(&resumed)
                .iter()
                .any(|read| read.operation().session() == reply_waiter),
            "the waiter is admitted only after the old owner reaches its network boundary"
        );
        assert!(!runner.state.local_scan_owners.contains(&sessions[0]));
        assert!(runner.state.local_scan_owners.contains(&reply_waiter));
        assert_eq!(runner.state.local_scan_owners.len(), MAX_LOCAL_SCAN_OWNERS);
        assert!(matches!(
            runner
                .session(sessions[0])
                .expect("retained scan")
                .plan()
                .persistence(),
            crate::plan::SessionPersistence::None
        ));
    }

    #[test]
    fn incremental_write_completion_reselects_strict_higher_recovery_at_full_capacity() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let sessions = (170..174)
            .map(|seq| peer_request_session(&acquire_with_effects(&mut runner, seq)))
            .collect::<Vec<_>>();
        let lower = &sessions[..3];
        let recovery = sessions[3];
        let mut writes = Vec::new();

        for (index, session) in lower.iter().enumerate() {
            let seq = 170 + index as u32;
            let state = runner.state.sessions.get_mut(session).expect("lower owner");
            state.pending_header_read = None;
            assert!(
                state.plan.install_engine(Box::new(
                    ScriptedEngine::new(
                        TreePlanId::new(u64::from(seq)),
                        VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                            SHAMapHash::new(Uint256::from(u64::from(seq) + 70_000)),
                            seq,
                            SHAMapNodeId::default(),
                            0,
                        )])]),
                        vec![crate::io::PersistNode::new(
                            SHAMapHash::new(Uint256::from(u64::from(seq) + 80_000)),
                            bytes::Bytes::from_static(b"accepted-node"),
                            crate::io::StoredObjectKind::AccountNode,
                        )],
                    )
                    .with_persistence_sequence(seq),
                ))
            );
            runner.state.local_scan_owners.insert(*session);
            let mut effects = Vec::new();
            runner.run_plan_turn(*session, None, &mut effects);
            writes.push(write_batch(&effects));
        }

        {
            let state = runner
                .state
                .sessions
                .get_mut(&recovery)
                .expect("recovery waiter");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(173),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(90_173)),
                    173,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
        }
        runner.state.validation_recovery_session = Some(recovery);
        runner.state.local_scan_waiters.push_back(recovery);
        assert_eq!(runner.state.local_scan_owners.len(), MAX_LOCAL_SCAN_OWNERS);

        let effects = runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            writes[0].operation(),
            WriteOutcome::Accepted,
        )));

        assert!(runner.state.local_scan_owners.contains(&recovery));
        assert!(!runner.state.local_scan_owners.contains(&lower[0]));
        assert!(runner.state.local_scan_waiters.contains(&lower[0]));
        assert_eq!(runner.state.local_scan_owners.len(), MAX_LOCAL_SCAN_OWNERS);
        assert!(read_effects(&effects).iter().any(|read| {
            read.operation().session() == recovery && read.priority() == ReadPriority::Consensus
        }));
        assert!(
            read_effects(&effects)
                .iter()
                .all(|read| read.operation().session() != lower[0])
        );
        assert!(writes[1..].iter().all(|write| matches!(
            runner
                .session(write.operation().session())
                .expect("unrelated lower owner")
                .plan()
                .persistence(),
            crate::plan::SessionPersistence::IncrementalWritePending { .. }
        )));
    }

    #[test]
    fn binding_existing_validation_recovery_waiter_reclaims_pending_lower_writer() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let sessions = (180..184)
            .map(|seq| peer_request_session(&acquire_with_effects(&mut runner, seq)))
            .collect::<Vec<_>>();
        let lower = &sessions[..3];
        let recovery = sessions[3];

        for (index, session) in lower.iter().enumerate() {
            let seq = 180 + index as u32;
            let state = runner.state.sessions.get_mut(session).expect("lower owner");
            state.pending_header_read = None;
            assert!(
                state.plan.install_engine(Box::new(
                    ScriptedEngine::new(
                        TreePlanId::new(u64::from(seq)),
                        VecDeque::from([ScriptedStep::NeedsNetwork(vec![(
                            SHAMapNodeId::default(),
                            Uint256::from(u64::from(seq) + 100_000),
                        )])]),
                        vec![crate::io::PersistNode::new(
                            SHAMapHash::new(Uint256::from(u64::from(seq) + 110_000)),
                            bytes::Bytes::from_static(b"accepted-node"),
                            crate::io::StoredObjectKind::AccountNode,
                        )],
                    )
                    .with_persistence_sequence(seq),
                ))
            );
            runner.state.local_scan_owners.insert(*session);
            let mut effects = Vec::new();
            runner.run_plan_turn(*session, None, &mut effects);
            assert!(effects.iter().any(|effect| matches!(
                effect,
                AcquisitionEffect::SubmitWrite(write)
                    if write.operation().session() == *session
            )));
        }

        {
            let state = runner
                .state
                .sessions
                .get_mut(&recovery)
                .expect("existing waiter");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(183),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(120_183)),
                    183,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
        }
        runner.state.local_scan_waiters.push_back(recovery);
        assert_eq!(runner.state.validation_recovery_session, None);
        assert_eq!(runner.state.local_scan_owners.len(), MAX_LOCAL_SCAN_OWNERS);

        let effects = runner.handle_event(AcquisitionEvent::ValidationRecoveryTarget(Some(
            target(183),
        )));

        assert_eq!(runner.state.validation_recovery_session, Some(recovery));
        assert!(runner.state.local_scan_owners.contains(&recovery));
        assert_eq!(runner.state.local_scan_owners.len(), MAX_LOCAL_SCAN_OWNERS);
        assert_eq!(
            lower
                .iter()
                .filter(|session| runner.state.local_scan_owners.contains(session))
                .count(),
            MAX_LOCAL_SCAN_OWNERS - 1
        );
        assert!(read_effects(&effects).iter().any(|read| {
            read.operation().session() == recovery && read.priority() == ReadPriority::Consensus
        }));
        for session in lower {
            assert!(matches!(
                runner
                    .session(*session)
                    .expect("lower writer")
                    .plan()
                    .persistence(),
                crate::plan::SessionPersistence::IncrementalWritePending { .. }
            ));
        }
    }

    #[test]
    fn incremental_write_submission_yields_ordinary_owner_to_stable_recovery() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let ordinary = peer_request_session(&acquire_with_effects(&mut runner, 80));
        let recovery = peer_request_session(&acquire_with_effects(&mut runner, 81));

        {
            let state = runner.state.sessions.get_mut(&ordinary).expect("ordinary");
            state.reason = AcquireReason::Generic;
            state.pending_header_read = None;
            assert!(
                state.plan.install_engine(Box::new(
                    ScriptedEngine::new(
                        TreePlanId::new(80),
                        VecDeque::from([ScriptedStep::NeedsNetwork(vec![(
                            SHAMapNodeId::default(),
                            Uint256::from(80_040),
                        )])]),
                        vec![crate::io::PersistNode::new(
                            SHAMapHash::new(Uint256::from(80_050)),
                            bytes::Bytes::from_static(b"accepted-node"),
                            crate::io::StoredObjectKind::AccountNode,
                        )],
                    )
                    .with_persistence_sequence(80),
                ))
            );
        }
        {
            let state = runner.state.sessions.get_mut(&recovery).expect("recovery");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(81),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(81_060)),
                    81,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
        }
        runner.state.local_scan_owners.insert(ordinary);
        runner.state.local_scan_waiters.push_back(recovery);
        runner.state.validation_recovery_session = Some(recovery);

        let mut effects = Vec::new();
        runner.run_plan_turn(ordinary, None, &mut effects);
        let write_position = effects
            .iter()
            .position(|effect| {
                matches!(
                    effect,
                    AcquisitionEffect::SubmitWrite(batch) if batch.operation().session() == ordinary
                )
            })
            .expect("ordinary write is submitted");
        let recovery_position = effects
            .iter()
            .position(|effect| {
                matches!(
                    effect,
                    AcquisitionEffect::SubmitRead(read) if read.operation().session() == recovery
                )
            })
            .expect("recovery read is submitted");
        assert!(write_position < recovery_position);
        assert!(
            read_effects(&effects)
                .iter()
                .any(|read| read.operation().session() == recovery)
        );
        assert!(!runner.state.local_scan_owners.contains(&ordinary));
        assert!(runner.state.local_scan_owners.contains(&recovery));
        assert!(!runner.state.local_scan_waiters.contains(&ordinary));
    }

    #[test]
    fn ordinary_async_boundary_yields_to_plain_consensus_waiter() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let ordinary = peer_request_session(&acquire_with_effects(&mut runner, 82));
        let consensus = peer_request_session(&acquire_with_effects(&mut runner, 83));
        runner
            .state
            .sessions
            .get_mut(&ordinary)
            .expect("ordinary")
            .reason = AcquireReason::Generic;
        runner
            .state
            .sessions
            .get_mut(&consensus)
            .expect("consensus")
            .reason = AcquireReason::Consensus;
        {
            let state = runner
                .state
                .sessions
                .get_mut(&consensus)
                .expect("consensus");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(83),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(83_010)),
                    83,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
        }
        runner.state.local_scan_owners.insert(ordinary);
        runner.state.local_scan_waiters.push_back(consensus);

        let mut effects = Vec::new();
        assert!(runner.yield_ordinary_scan_to_recovery(ordinary, true, &mut effects));
        assert!(runner.state.local_scan_owners.contains(&consensus));
        assert!(runner.state.local_scan_waiters.contains(&ordinary));
    }

    #[test]
    fn scan_waiters_rank_exact_then_validation_then_plain_consensus() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let sessions = (84..88)
            .map(|seq| peer_request_session(&acquire_with_effects(&mut runner, seq)))
            .collect::<Vec<_>>();
        let ordinary = sessions[0];
        let consensus = sessions[1];
        let validation = sessions[2];
        let anchor = sessions[3];
        runner
            .state
            .sessions
            .get_mut(&ordinary)
            .expect("ordinary")
            .reason = AcquireReason::Generic;
        runner.state.recovery_anchor_session = Some(anchor);
        runner.state.validation_recovery_session = Some(validation);
        runner.state.local_scan_waiters = VecDeque::from([ordinary, consensus, validation, anchor]);

        assert_eq!(runner.pop_scan_waiter(), Some(anchor));
        assert_eq!(runner.pop_scan_waiter(), Some(validation));
        assert_eq!(runner.pop_scan_waiter(), Some(consensus));
        assert_eq!(runner.pop_scan_waiter(), Some(ordinary));
    }

    #[test]
    fn safe_boundary_preempts_only_for_strictly_higher_recovery_rank() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let sessions = (88..91)
            .map(|seq| peer_request_session(&acquire_with_effects(&mut runner, seq)))
            .collect::<Vec<_>>();
        let plain = sessions[0];
        let validation = sessions[1];
        let anchor = sessions[2];
        for (session, seq) in [(validation, 89_u32), (anchor, 90_u32)] {
            let state = runner.state.sessions.get_mut(&session).expect("candidate");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(u64::from(seq)),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(u64::from(seq) * 1_000 + 10)),
                    seq,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
        }
        runner.state.recovery_anchor_session = Some(anchor);
        runner.state.validation_recovery_session = Some(validation);
        runner.state.local_scan_owners.insert(validation);
        runner.state.local_scan_waiters = VecDeque::from([plain, anchor]);

        let mut effects = Vec::new();
        assert!(runner.yield_ordinary_scan_to_recovery(validation, true, &mut effects));
        assert!(runner.state.local_scan_owners.contains(&anchor));
        assert!(runner.state.local_scan_waiters.contains(&validation));
        assert!(runner.state.local_scan_waiters.contains(&plain));

        runner.state.local_scan_owners.clear();
        runner.state.local_scan_waiters = VecDeque::from([validation]);
        runner.state.recovery_anchor_session = None;
        runner.state.local_scan_owners.insert(plain);
        let mut validation_effects = Vec::new();
        assert!(runner.yield_ordinary_scan_to_recovery(plain, true, &mut validation_effects));
        assert!(runner.state.local_scan_owners.contains(&validation));
    }

    #[test]
    fn plain_consensus_burst_grants_oldest_ordinary_every_third_slot() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let sessions = (91..95)
            .map(|seq| peer_request_session(&acquire_with_effects(&mut runner, seq)))
            .collect::<Vec<_>>();
        let ordinary = sessions[0];
        runner
            .state
            .sessions
            .get_mut(&ordinary)
            .expect("ordinary")
            .reason = AcquireReason::Generic;
        runner.state.local_scan_waiters =
            VecDeque::from([ordinary, sessions[1], sessions[2], sessions[3]]);

        assert_eq!(runner.pop_scan_waiter(), Some(sessions[1]));
        assert_eq!(runner.pop_scan_waiter(), Some(sessions[2]));
        assert_eq!(runner.pop_scan_waiter(), Some(ordinary));
        assert_eq!(runner.pop_scan_waiter(), Some(sessions[3]));
    }

    #[test]
    fn completed_boundary_forces_ordinary_after_plain_consensus_burst() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let ordinary = peer_request_session(&acquire_with_effects(&mut runner, 95));
        let consensus = peer_request_session(&acquire_with_effects(&mut runner, 96));
        runner
            .state
            .sessions
            .get_mut(&ordinary)
            .expect("ordinary")
            .reason = AcquireReason::Generic;
        {
            let state = runner
                .state
                .sessions
                .get_mut(&consensus)
                .expect("consensus");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(96),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(96_010)),
                    96,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
        }
        runner.state.local_scan_owners.insert(ordinary);
        runner.state.local_scan_waiters.push_back(consensus);
        runner.state.plain_consensus_scan_burst = MAX_PLAIN_CONSENSUS_SCAN_BURST;

        let mut forced_ordinary = Vec::new();
        assert!(!runner.yield_ordinary_scan_to_recovery(ordinary, true, &mut forced_ordinary));
        assert!(runner.state.local_scan_owners.contains(&ordinary));
        assert_eq!(runner.state.plain_consensus_scan_burst, 0);

        let mut next_boundary = Vec::new();
        assert!(runner.yield_ordinary_scan_to_recovery(ordinary, true, &mut next_boundary));
        assert!(runner.state.local_scan_owners.contains(&consensus));
        assert_eq!(runner.state.plain_consensus_scan_burst, 1);
    }

    #[test]
    fn arriving_recovery_reclaims_only_an_ordinary_pending_writer() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let sessions = (90..95)
            .map(|seq| peer_request_session(&acquire_with_effects(&mut runner, seq)))
            .collect::<Vec<_>>();
        let displaced = sessions[0];
        let recovery_anchor = sessions[3];
        let validation_recovery = sessions[4];

        for session in &sessions[..3] {
            runner
                .state
                .sessions
                .get_mut(session)
                .expect("ordinary")
                .reason = AcquireReason::Generic;
            runner.state.local_scan_owners.insert(*session);
        }
        {
            let state = runner
                .state
                .sessions
                .get_mut(&displaced)
                .expect("displaced");
            state.pending_header_read = None;
            assert!(
                state.plan.install_engine(Box::new(
                    ScriptedEngine::new(
                        TreePlanId::new(90),
                        VecDeque::from([ScriptedStep::NeedsNetwork(vec![(
                            SHAMapNodeId::default(),
                            Uint256::from(90_040),
                        )])]),
                        vec![crate::io::PersistNode::new(
                            SHAMapHash::new(Uint256::from(90_050)),
                            bytes::Bytes::from_static(b"accepted-node"),
                            crate::io::StoredObjectKind::AccountNode,
                        )],
                    )
                    .with_persistence_sequence(90),
                ))
            );
        }
        let mut write_effects = Vec::new();
        runner.run_plan_turn(displaced, None, &mut write_effects);
        let write = write_batch(&write_effects);
        assert!(runner.state.local_scan_owners.contains(&displaced));
        runner.state.swept_local_scan_owners.insert(displaced);

        {
            let state = runner
                .state
                .sessions
                .get_mut(&recovery_anchor)
                .expect("recovery anchor");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(93),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(93_060)),
                    93,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
        }
        runner.state.local_scan_waiters.push_back(recovery_anchor);
        runner.state.recovery_anchor_session = Some(recovery_anchor);
        runner.state.validation_recovery_session = Some(validation_recovery);
        let mut recovery_effects = Vec::new();
        runner.run_plan_turn(validation_recovery, None, &mut recovery_effects);
        assert!(
            read_effects(&recovery_effects)
                .iter()
                .any(|read| read.operation().session() == recovery_anchor)
        );
        assert!(
            read_effects(&recovery_effects)
                .iter()
                .all(|read| read.operation().session() != validation_recovery)
        );
        assert!(runner.state.local_scan_owners.contains(&recovery_anchor));
        assert!(
            runner
                .state
                .local_scan_waiters
                .contains(&validation_recovery)
        );
        assert!(!runner.state.local_scan_owners.contains(&displaced));
        assert!(runner.state.swept_local_scan_owners.contains(&displaced));

        let resumed = runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            write.operation(),
            WriteOutcome::Accepted,
        )));
        assert!(resumed.is_empty());
        assert!(runner.state.local_scan_waiters.contains(&displaced));
        assert!(runner.state.swept_local_scan_owners.contains(&displaced));
        assert_eq!(runner.state.local_scan_owners.len(), MAX_LOCAL_SCAN_OWNERS);
    }

    #[test]
    fn arriving_plain_consensus_reclaims_an_ordinary_pending_writer() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let sessions = (95..99)
            .map(|seq| peer_request_session(&acquire_with_effects(&mut runner, seq)))
            .collect::<Vec<_>>();
        let blocked = sessions[0];
        let consensus = sessions[3];

        for session in &sessions[..3] {
            runner
                .state
                .sessions
                .get_mut(session)
                .expect("ordinary")
                .reason = AcquireReason::Generic;
            runner.state.local_scan_owners.insert(*session);
        }
        {
            let state = runner.state.sessions.get_mut(&blocked).expect("blocked");
            state.pending_header_read = None;
            assert!(
                state.plan.install_engine(Box::new(
                    ScriptedEngine::new(
                        TreePlanId::new(95),
                        VecDeque::from([ScriptedStep::NeedsNetwork(vec![(
                            SHAMapNodeId::default(),
                            Uint256::from(95_040),
                        )])]),
                        vec![crate::io::PersistNode::new(
                            SHAMapHash::new(Uint256::from(95_050)),
                            bytes::Bytes::from_static(b"accepted-node"),
                            crate::io::StoredObjectKind::AccountNode,
                        )],
                    )
                    .with_persistence_sequence(95),
                ))
            );
        }
        let mut write_effects = Vec::new();
        runner.run_plan_turn(blocked, None, &mut write_effects);
        assert!(matches!(
            runner
                .state
                .sessions
                .get(&blocked)
                .expect("blocked")
                .plan
                .persistence(),
            crate::plan::SessionPersistence::IncrementalWritePending { .. }
        ));
        {
            let state = runner
                .state
                .sessions
                .get_mut(&consensus)
                .expect("consensus");
            state.reason = AcquireReason::Consensus;
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(98),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(98_060)),
                    98,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
        }

        let mut effects = Vec::new();
        runner.run_plan_turn(consensus, None, &mut effects);
        assert!(!runner.state.local_scan_owners.contains(&blocked));
        assert!(runner.state.local_scan_owners.contains(&consensus));
        assert!(
            read_effects(&effects)
                .iter()
                .any(|read| read.operation().session() == consensus)
        );
    }

    #[test]
    fn generic_provenance_exact_recovery_owner_is_never_displaced() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let exact = peer_request_session(&acquire_with_effects(&mut runner, 96));
        let validation = peer_request_session(&acquire_with_effects(&mut runner, 97));

        {
            let state = runner
                .state
                .sessions
                .get_mut(&exact)
                .expect("exact recovery");
            state.reason = AcquireReason::Generic;
            state.pending_header_read = None;
            assert!(
                state.plan.install_engine(Box::new(
                    ScriptedEngine::new(
                        TreePlanId::new(96),
                        VecDeque::from([ScriptedStep::NeedsNetwork(vec![(
                            SHAMapNodeId::default(),
                            Uint256::from(96_040),
                        )])]),
                        vec![crate::io::PersistNode::new(
                            SHAMapHash::new(Uint256::from(96_050)),
                            bytes::Bytes::from_static(b"accepted-node"),
                            crate::io::StoredObjectKind::AccountNode,
                        )],
                    )
                    .with_persistence_sequence(96),
                ))
            );
        }
        runner.state.recovery_anchor_session = Some(exact);
        runner.state.validation_recovery_session = Some(validation);
        runner.state.local_scan_owners.insert(exact);
        runner.state.local_scan_waiters.push_back(validation);

        let mut effects = Vec::new();
        runner.run_plan_turn(exact, None, &mut effects);
        assert!(effects.iter().any(|effect| matches!(
            effect,
            AcquisitionEffect::SubmitWrite(batch) if batch.operation().session() == exact
        )));
        assert!(runner.state.local_scan_owners.contains(&exact));
        assert!(runner.state.local_scan_waiters.contains(&validation));
        assert!(effects.iter().all(|effect| !matches!(
            effect,
            AcquisitionEffect::SubmitRead(read) if read.operation().session() == validation
        )));
    }

    #[test]
    fn generic_provenance_exact_recovery_emits_consensus_reads() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let exact = peer_request_session(&acquire_with_effects(&mut runner, 99));
        {
            let state = runner
                .state
                .sessions
                .get_mut(&exact)
                .expect("exact recovery");
            state.reason = AcquireReason::Generic;
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(99),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(99_010)),
                    99,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
        }
        runner.state.recovery_anchor_session = Some(exact);

        let mut effects = Vec::new();
        runner.run_plan_turn(exact, None, &mut effects);
        let reads = read_effects(&effects);
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].priority(), ReadPriority::Consensus);
    }

    #[test]
    fn completed_read_barrier_yields_ordinary_owner_to_stable_recovery() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let ordinary = peer_request_session(&acquire_with_effects(&mut runner, 100));
        let recovery = peer_request_session(&acquire_with_effects(&mut runner, 101));

        {
            let state = runner.state.sessions.get_mut(&ordinary).expect("ordinary");
            state.reason = AcquireReason::Generic;
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(100),
                VecDeque::from([
                    ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                        SHAMapHash::new(Uint256::from(100_010)),
                        100,
                        SHAMapNodeId::default(),
                        0,
                    )]),
                    ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                        SHAMapHash::new(Uint256::from(100_020)),
                        100,
                        SHAMapNodeId::default(),
                        0,
                    )]),
                ]),
                Vec::new(),
            ))));
        }
        {
            let state = runner.state.sessions.get_mut(&recovery).expect("recovery");
            state.pending_header_read = None;
            assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
                TreePlanId::new(101),
                VecDeque::from([ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(101_010)),
                    101,
                    SHAMapNodeId::default(),
                    0,
                )])]),
                Vec::new(),
            ))));
        }
        runner.state.local_scan_owners.insert(ordinary);
        let mut first = Vec::new();
        runner.run_plan_turn(ordinary, None, &mut first);
        let first_read = read_effects(&first)[0].operation();
        runner.state.local_scan_waiters.push_back(recovery);
        runner.state.validation_recovery_session = Some(recovery);

        let effects = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            first_read,
            ReadOutcome::Settled { node: None },
        )));
        assert!(
            read_effects(&effects)
                .iter()
                .any(|read| read.operation().session() == recovery)
        );
        assert!(runner.state.local_scan_owners.contains(&recovery));
        assert!(runner.state.local_scan_waiters.contains(&ordinary));
        assert!(
            read_effects(&effects)
                .iter()
                .all(|read| read.operation().session() != ordinary)
        );
    }

    #[test]
    fn cancelled_incremental_write_cancels_store_generation_session() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let session = peer_request_session(&acquire_with_effects(&mut runner, 70));
        {
            let state = runner.state.sessions.get_mut(&session).expect("session");
            state.pending_header_read = None;
            assert!(
                state.plan.install_engine(Box::new(
                    ScriptedEngine::new(
                        TreePlanId::new(70),
                        VecDeque::from([ScriptedStep::NeedsNetwork(vec![(
                            SHAMapNodeId::default(),
                            Uint256::from(40_070),
                        )])]),
                        vec![crate::io::PersistNode::new(
                            SHAMapHash::new(Uint256::from(50_070)),
                            bytes::Bytes::from_static(b"accepted-node"),
                            crate::io::StoredObjectKind::AccountNode,
                        )],
                    )
                    .with_persistence_sequence(70),
                ))
            );
        }

        let mut started = Vec::new();
        runner.run_plan_turn(session, None, &mut started);
        let batch = write_batch(&started);
        assert!(batch.fence().is_none());
        assert!(matches!(
            runner.session(session).expect("live").plan().persistence(),
            crate::plan::SessionPersistence::IncrementalWritePending { .. }
        ));

        let effects = runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            batch.operation(),
            WriteOutcome::Cancelled,
        )));
        assert!(effects.contains(&AcquisitionEffect::CancelSession(session)));
        assert!(matches!(
            runner
                .session(session)
                .expect("retained terminal session")
                .phase(),
            SessionPhase::Cancelled {
                reason: CancelReason::StoreRotated
            }
        ));
        assert_eq!(
            runner.snapshot().cancelled_by_reason(),
            &BTreeMap::from([(CancelReason::StoreRotated, 1)])
        );
        assert_eq!(runner.snapshot().stale_events(), 0);
    }

    #[test]
    fn five_hundred_twelve_read_completions_resume_plan_once_after_barrier() {
        let budget = BudgetState::new(
            8,
            AdmissionBudget::new(600, 1 << 20),
            Duration::from_secs(1),
        );
        let mut runner = CoordinatorRunner::with_budget(RunEpoch::new(1), budget);
        connect(&mut runner);
        let started = acquire_with_effects(&mut runner, 30);
        let session = peer_request_session(&started);
        let first_batch = (0..512u64)
            .map(|offset| {
                PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(10_000 + offset)),
                    30,
                    SHAMapNodeId::default(),
                    0,
                )
            })
            .collect();
        let state = runner.state.sessions.get_mut(&session).expect("session");
        state.pending_header_read = None;
        assert!(state.plan.install_engine(Box::new(ScriptedEngine::new(
            TreePlanId::new(30),
            VecDeque::from([
                ScriptedStep::NeedsReads(first_batch),
                ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(20_000)),
                    30,
                    SHAMapNodeId::default(),
                    0,
                )]),
            ]),
            Vec::new(),
        ))));
        let mut initial = Vec::new();
        runner.run_plan_turn(session, None, &mut initial);
        let reads = read_effects(&initial);
        assert_eq!(reads.len(), 512);
        let turns_before = runner.snapshot().plan_turns();
        let mut completions = reads
            .into_iter()
            .map(|read| ReadCompletion::new(read.operation(), ReadOutcome::Settled { node: None }))
            .collect::<Vec<_>>();
        let final_completion = completions.pop().expect("512th completion");

        let partial_effects = runner.handle_read_batch(completions);
        assert_eq!(runner.snapshot().plan_turns() - turns_before, 0);
        assert!(read_effects(&partial_effects).is_empty());
        assert_eq!(
            runner
                .session(session)
                .expect("live")
                .plan()
                .pending_traversal_read_count(),
            1
        );

        let effects = runner.handle_read_batch(vec![final_completion]);
        assert_eq!(
            runner.snapshot().plan_turns() - turns_before,
            1,
            "one drained deferred-read round must resume the continuation once"
        );
        assert_eq!(read_effects(&effects).len(), 1);
    }

    #[test]
    fn read_completion_must_match_the_exact_inflight_operation() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsReads(vec![
                PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(7)),
                    10,
                    SHAMapNodeId::default(),
                    0,
                ),
            ])])),
        );
        connect(&mut runner);
        let session = acquire(&mut runner, 10);
        let packet = admitted_packet(session, AdmissionBudget::new(1, 256), 8);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(packet));
        let reads = read_effects(&effects);
        let inflight = reads[0].operation();

        // A different read operation for the same session is stale: a target
        // hash alone never authorizes a result.
        let wrong = OperationRef::new(
            session,
            OperationKind::Read,
            OperationId::new(999),
            OperationGeneration::new(1),
        );
        runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            wrong,
            ReadOutcome::Settled { node: None },
        )));
        assert_eq!(runner.snapshot().stale_events(), 1);

        // The exact in-flight operation applies and the plan advances.
        runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            inflight,
            ReadOutcome::Settled { node: None },
        )));
        assert_eq!(runner.snapshot().stale_events(), 1);
        assert_eq!(runner.snapshot().plan_turns(), 2);
    }

    #[test]
    fn reply_peer_survives_async_reads_and_keeps_128_node_depth_one_shape() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let frontier = (1..=REPLY_NODE_REQUEST_BATCH)
            .map(|index| {
                (
                    SHAMapNodeId::default(),
                    Uint256::from(u64::try_from(index).expect("frontier index fits u64")),
                )
            })
            .collect::<Vec<_>>();
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![
                ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(999)),
                    10,
                    SHAMapNodeId::default(),
                    0,
                )]),
                ScriptedStep::NeedsNetwork(frontier),
            ])),
        );
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1), PeerId::new(2), PeerId::new(3)]),
        ));
        let session = acquire(&mut runner, 10);
        let packet =
            admitted_packet_from_peer(session, PeerId::new(3), AdmissionBudget::new(1, 256), 8);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(packet));
        let read = read_effects(&effects)
            .pop()
            .expect("reply must schedule its local read");

        let effects = runner.handle_event(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            read.operation(),
            ReadOutcome::Settled { node: None },
        )));
        let request = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => Some(request),
                _ => None,
            })
            .expect("read continuation must retain reply request semantics");
        assert_eq!(request.peer_id(), PeerId::new(3));
        assert!(matches!(
            request.request(),
            LedgerDataRequest::GetLedgerNodes {
                node_ids,
                query_depth: 1,
                indirect: false,
                ..
            } if node_ids.len() == REPLY_NODE_REQUEST_BATCH
        ));
    }

    #[test]
    fn fetch_pack_fact_re_advances_live_sessions_only() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![
                ScriptedStep::NeedsNetwork(vec![(SHAMapNodeId::default(), Uint256::from(3))]),
                ScriptedStep::NeedsReads(vec![PlanReadNeed::new(
                    SHAMapHash::new(Uint256::from(7)),
                    10,
                    SHAMapNodeId::default(),
                    0,
                )]),
            ])),
        );
        connect(&mut runner);
        let session = acquire(&mut runner, 10);

        // A fetch-pack fact before any live session has a rooted engine is a
        // no-op: there is nothing to re-advance.
        let effects = runner.handle_event(AcquisitionEvent::FetchPackAvailable);
        assert!(effects.is_empty());
        assert_eq!(runner.snapshot().fetch_pack_advances(), 0);

        // Seed the engine with a header packet; the first advance announces
        // network candidates and blocks on them.
        let packet = admitted_packet(session, AdmissionBudget::new(1, 256), 8);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(packet));
        assert!(
            effects
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SendLedgerRequest(_))),
            "the first advance announces network candidates"
        );
        assert_eq!(runner.snapshot().plan_turns(), 1);

        // The fetch-pack fact names no session but re-advances every live
        // session, so a session blocked on network needs takes another bounded
        // traversal pass and can announce freshly resolvable work.
        let effects = runner.handle_event(AcquisitionEvent::FetchPackAvailable);
        let reads = read_effects(&effects);
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].key(), SHAMapHash::new(Uint256::from(7)));
        assert_eq!(runner.snapshot().fetch_pack_advances(), 1);
        assert_eq!(runner.snapshot().plan_turns(), 2);

        // After the session is cancelled a later fetch-pack fact is a no-op.
        let cancel = runner.handle_event(AcquisitionEvent::Shutdown);
        assert!(
            cancel.iter().any(|effect| {
                matches!(effect, AcquisitionEffect::CancelSession(s) if *s == session)
            }),
            "shutdown cancels the live session"
        );
        assert!(
            runner
                .handle_event(AcquisitionEvent::FetchPackAvailable)
                .is_empty()
        );
    }

    fn state_network_need(hash: u64) -> PlanNetworkNeed {
        PlanNetworkNeed::new(
            SHAMapNodeId::new(64, Uint256::from(hash)).expect("valid deterministic node id"),
            Uint256::from(hash),
            ledger::TreeKind::State,
        )
    }

    fn normal_ledger_node_requests(
        effects: &[AcquisitionEffect],
    ) -> Vec<(PeerId, Vec<SHAMapNodeId>)> {
        effects
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SendLedgerRequest(request) => match request.request() {
                    LedgerDataRequest::GetLedgerNodes { node_ids, .. } => {
                        Some((request.peer_id(), node_ids.clone()))
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect()
    }

    #[test]
    fn blind_frontier_emits_one_fifo_12_node_request_per_selected_peer() {
        let needs = (1..=256).map(state_network_need).collect::<Vec<_>>();
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![
                ScriptedStep::NeedsNetworkWithKind(Vec::new()),
                ScriptedStep::NeedsNetworkWithKind(needs.clone()),
            ])),
        );
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1), PeerId::new(2)]),
        ));
        let session = acquire(&mut runner, 10);
        let _ = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));

        let effects = runner.handle_event(AcquisitionEvent::FetchPackAvailable);
        let requests = normal_ledger_node_requests(&effects);
        let first_batch = needs[..12]
            .iter()
            .map(|need| need.node_id())
            .collect::<Vec<_>>();
        assert_eq!(requests.len(), 2);
        assert_eq!(requests[0], (PeerId::new(1), first_batch.clone()));
        assert_eq!(requests[1], (PeerId::new(2), first_batch));
    }

    #[test]
    fn later_owner_wake_advances_to_the_next_non_overlapping_blind_fifo_batch() {
        let needs = (1..=256).map(state_network_need).collect::<Vec<_>>();
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![
                ScriptedStep::NeedsNetworkWithKind(Vec::new()),
                ScriptedStep::NeedsNetworkWithKind(needs.clone()),
            ])),
        );
        let _ = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![PeerId::new(1), PeerId::new(2)]),
        ));
        let session = acquire(&mut runner, 10);
        let _ = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let first =
            normal_ledger_node_requests(&runner.handle_event(AcquisitionEvent::FetchPackAvailable));
        let later =
            normal_ledger_node_requests(&runner.handle_event(AcquisitionEvent::FetchPackAvailable));
        let first_ids = needs[..12]
            .iter()
            .map(|need| need.node_id())
            .collect::<Vec<_>>();
        let later_ids = needs[12..24]
            .iter()
            .map(|need| need.node_id())
            .collect::<Vec<_>>();
        assert_eq!(first.len(), 2);
        assert!(first.iter().all(|(_, ids)| *ids == first_ids));
        assert_eq!(later.len(), 2);
        assert!(later.iter().all(|(_, ids)| *ids == later_ids));
        assert_ne!(first_ids, later_ids);
    }

    #[test]
    fn reply_frontier_emits_at_most_128_nodes_only_to_the_responder() {
        let needs = (1..=256).map(state_network_need).collect::<Vec<_>>();
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::NeedsNetworkWithKind(
                needs.clone(),
            )])),
        );
        connect(&mut runner);
        let session = acquire(&mut runner, 10);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let requests = normal_ledger_node_requests(&effects);
        assert_eq!(requests.len(), 1);
        assert_eq!(requests[0].0, PeerId::new(1));
        assert_eq!(requests[0].1.len(), 128);
        assert_eq!(
            requests[0].1,
            needs[..128]
                .iter()
                .map(|need| need.node_id())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn durable_fence_hands_off_once_and_ack_completes() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let ledger = immutable_ledger(10);
        let seed = ScriptedSeed::new(vec![ScriptedStep::Complete])
            .with_durable_ledger(Arc::clone(&ledger));
        let mut runner =
            CoordinatorRunner::with_plan_seed(RunEpoch::new(1), budget, Box::new(seed));
        connect(&mut runner);
        let session = acquire(&mut runner, 10);
        let packet = admitted_packet(session, AdmissionBudget::new(1, 256), 8);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(packet));
        let batch = write_batch(&effects);
        assert_eq!(batch.operation().kind(), OperationKind::Write);
        assert_eq!(
            batch.fence().expect("final batch fence").kind(),
            OperationKind::DurabilityFence
        );
        assert!(matches!(
            runner.session(session).expect("live").phase(),
            SessionPhase::Persisting
        ));

        // A write completion that is not the exact in-flight write is stale.
        let wrong = OperationRef::new(
            session,
            OperationKind::Write,
            OperationId::new(999),
            OperationGeneration::new(1),
        );
        runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            wrong,
            WriteOutcome::Accepted,
        )));
        assert_eq!(runner.snapshot().stale_events(), 1);

        // The exact write completion moves the persistence state to FencePending.
        let effects = runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            batch.operation(),
            WriteOutcome::Accepted,
        )));
        assert!(effects.is_empty());

        // A fence completion for a different operation is stale.
        let wrong_fence = OperationRef::new(
            session,
            OperationKind::DurabilityFence,
            OperationId::new(999),
            OperationGeneration::new(1),
        );
        runner.handle_event(AcquisitionEvent::DurabilityFenced(
            DurabilityCompletion::new(wrong_fence, crate::io::DurabilityOutcome::Passed),
        ));
        assert_eq!(runner.snapshot().stale_events(), 2);

        // The exact fence moves Persisting -> DurablePending and emits exactly
        // one PublishDurable handoff: a unique id plus the durable ledger. The
        // ledger is never normal-adoptable before this fence.
        let effects = runner.handle_event(AcquisitionEvent::DurabilityFenced(
            DurabilityCompletion::new(
                batch.fence().expect("final batch fence"),
                crate::io::DurabilityOutcome::Passed,
            ),
        ));
        let published = durable_handoff(&effects);
        assert!(Arc::ptr_eq(published.ledger(), &ledger));
        assert!(!published.handoff().is_invalid());
        assert!(matches!(
            runner.session(session).expect("live").phase(),
            SessionPhase::DurablePending
        ));

        // A handoff ack carrying a different id is stale and cannot finalize.
        runner.handle_event(AcquisitionEvent::DurableHandoffAcknowledged(
            DurableHandoffAcknowledgement::new(DurableHandoffId::new(999), session),
        ));
        assert_eq!(runner.snapshot().stale_events(), 3);
        assert!(matches!(
            runner.session(session).expect("live").phase(),
            SessionPhase::DurablePending
        ));

        // The exact pending handoff id authorizes DurablePending -> Complete:
        // one logical terminal durable result for this successful session.
        runner.handle_event(AcquisitionEvent::DurableHandoffAcknowledged(
            DurableHandoffAcknowledgement::new(published.handoff(), session),
        ));
        assert!(matches!(
            runner.session(session).expect("live").phase(),
            SessionPhase::Complete
        ));
        let completed_target = runner.session(session).expect("retained terminal").target();
        assert!(
            !runner.has_viable_target_work(completed_target),
            "an acknowledged terminal session must not pin a Syncing anchor"
        );
        assert_eq!(runner.snapshot().sessions_completed(), 1);
    }

    #[test]
    fn handoff_ack_keeps_recovery_target_until_exact_lcl_install() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let ledger = immutable_ledger(10);
        let anchor_target = LedgerTarget::new(*ledger.header().hash.as_uint256(), Some(10));
        let seed = ScriptedSeed::new(vec![ScriptedStep::Complete])
            .with_durable_ledger(Arc::clone(&ledger));
        let mut runner =
            CoordinatorRunner::with_plan_seed(RunEpoch::new(1), budget, Box::new(seed));
        connect(&mut runner);
        let started = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            anchor_target,
            AcquireReason::Consensus,
        )));
        let session = peer_request_session(&started);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let batch = write_batch(&effects);
        let _ = runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            batch.operation(),
            WriteOutcome::Accepted,
        )));
        let fenced = runner.handle_event(AcquisitionEvent::DurabilityFenced(
            DurabilityCompletion::new(
                batch.fence().expect("final fence"),
                crate::io::DurabilityOutcome::Passed,
            ),
        ));
        let handoff = durable_handoff(&fenced).handoff();

        let moving = target(20);
        let _ = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            moving,
            AcquireReason::Consensus,
        )));
        let _ = runner.handle_event(AcquisitionEvent::DurableHandoffAcknowledged(
            DurableHandoffAcknowledgement::new(handoff, session),
        ));

        assert_eq!(
            runner.session(session).expect("terminal owner").phase(),
            &SessionPhase::Complete
        );
        assert_eq!(runner.state.recovery_anchor_target, Some(anchor_target));
        assert_eq!(runner.state.recovery_anchor_session, None);
        assert_eq!(
            runner.phase(),
            &SyncPhase::Syncing {
                target: anchor_target
            }
        );
        assert_eq!(runner.state.latest_consensus_target, Some(moving));

        let installed = LedgerIdentity::new(anchor_target.hash(), 10);
        let _ = runner.handle_event(AcquisitionEvent::LclInstalled(installed));
        assert_eq!(runner.state.recovery_anchor_target, None);
        assert_eq!(runner.phase(), &SyncPhase::Tracking { lcl: installed });
    }

    #[test]
    fn durable_header_refines_hash_only_syncing_target_sequence() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let ledger = immutable_ledger(27);
        let hash = *ledger.header().hash.as_uint256();
        let unresolved = LedgerTarget::new(hash, None);
        let seed = ScriptedSeed::new(vec![ScriptedStep::Complete])
            .with_durable_ledger(Arc::clone(&ledger));
        let mut runner =
            CoordinatorRunner::with_plan_seed(RunEpoch::new(1), budget, Box::new(seed));
        connect(&mut runner);
        let _ =
            runner.handle_event(AcquisitionEvent::PreferredLclDivergence { target: unresolved });
        let effects = runner.handle_event(AcquisitionEvent::ConsensusTarget(ConsensusTarget::new(
            unresolved,
            AcquireReason::Consensus,
        )));
        let session = peer_request_session(&effects);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let batch = write_batch(&effects);
        let _ = runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            batch.operation(),
            WriteOutcome::Accepted,
        )));

        let effects = runner.handle_event(AcquisitionEvent::DurabilityFenced(
            DurabilityCompletion::new(
                batch.fence().expect("final batch fence"),
                crate::io::DurabilityOutcome::Passed,
            ),
        ));
        let resolved = LedgerTarget::new(hash, Some(ledger.header().seq));
        assert_eq!(runner.phase(), &SyncPhase::Syncing { target: resolved });
        assert!(
            effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                target: resolved
            }))
        );
        assert_eq!(runner.state.latest_consensus_target, Some(resolved));
        assert_eq!(
            runner.session(session).expect("live session").target(),
            resolved
        );
        assert!(
            effects
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::PublishDurable(_)))
        );
        let phase_index = effects
            .iter()
            .position(|effect| matches!(effect, AcquisitionEffect::SetServicePhase(_)))
            .expect("resolved phase effect");
        let handoff_index = effects
            .iter()
            .position(|effect| matches!(effect, AcquisitionEffect::PublishDurable(_)))
            .expect("durable handoff effect");
        assert!(
            phase_index < handoff_index,
            "target identity must be published before the durable ledger handoff"
        );
    }

    #[test]
    fn passed_fence_without_a_durable_payload_fails_before_handoff() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::Complete])),
        );
        connect(&mut runner);
        let session = acquire(&mut runner, 10);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let batch = write_batch(&effects);
        let _ = runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            batch.operation(),
            WriteOutcome::Accepted,
        )));

        let effects = runner.handle_event(AcquisitionEvent::DurabilityFenced(
            DurabilityCompletion::new(
                batch.fence().expect("final batch fence"),
                crate::io::DurabilityOutcome::Passed,
            ),
        ));
        assert!(effects.contains(&AcquisitionEffect::CancelSession(session)));
        assert!(
            effects
                .iter()
                .all(|effect| { !matches!(effect, AcquisitionEffect::PublishDurable(_)) })
        );
        assert!(matches!(
            runner.session(session).expect("failed session").phase(),
            SessionPhase::Failed {
                reason: FailureReason::DurabilityFenceFailed
            }
        ));
    }

    #[test]
    fn peer_loss_preserves_durable_pending_handoff_retry_state() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let ledger = immutable_ledger(12);
        let seed = ScriptedSeed::new(vec![ScriptedStep::Complete])
            .with_durable_ledger(Arc::clone(&ledger));
        let mut runner =
            CoordinatorRunner::with_plan_seed(RunEpoch::new(1), budget, Box::new(seed));
        connect(&mut runner);
        let session = acquire(&mut runner, 12);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(admitted_packet(
            session,
            AdmissionBudget::new(1, 256),
            8,
        )));
        let batch = write_batch(&effects);
        runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            batch.operation(),
            WriteOutcome::Accepted,
        )));
        let effects = runner.handle_event(AcquisitionEvent::DurabilityFenced(
            DurabilityCompletion::new(
                batch.fence().expect("final batch fence"),
                crate::io::DurabilityOutcome::Passed,
            ),
        ));
        let published = durable_handoff(&effects);
        let retry_effects = runner.handle_event(AcquisitionEvent::DurableHandoffRejected {
            handoff: published.handoff(),
            session,
            reason: HandoffRejectReason::ChannelFull,
        });
        let retry = timer_operation(&retry_effects);

        let effects = runner.handle_event(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(vec![]),
        ));
        assert!(effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Disconnected)));
        assert!(
            !effects.contains(&AcquisitionEffect::CancelSession(session)),
            "peer loss must not revoke a post-fence durable handoff"
        );
        assert!(matches!(
            runner.session(session).expect("durable session").phase(),
            SessionPhase::DurablePending
        ));
        assert_eq!(
            runner
                .session(session)
                .expect("durable session")
                .pending_timer(),
            Some((TimerKind::HandoffRetry, retry))
        );
        assert_eq!(
            runner.handle_event(AcquisitionEvent::TimerFired {
                operation: retry,
                timer: TimerKind::HandoffRetry,
            }),
            vec![AcquisitionEffect::PublishDurable(published)]
        );
    }

    #[test]
    fn handoff_rejection_arms_one_exact_retry_before_republish() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let ledger = immutable_ledger(11);
        let seed = ScriptedSeed::new(vec![ScriptedStep::Complete])
            .with_durable_ledger(Arc::clone(&ledger));
        let mut runner =
            CoordinatorRunner::with_plan_seed(RunEpoch::new(1), budget, Box::new(seed));
        connect(&mut runner);
        let session = acquire(&mut runner, 11);
        let packet = admitted_packet(session, AdmissionBudget::new(1, 256), 8);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(packet));
        let batch = write_batch(&effects);
        runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            batch.operation(),
            WriteOutcome::Accepted,
        )));
        let effects = runner.handle_event(AcquisitionEvent::DurabilityFenced(
            DurabilityCompletion::new(
                batch.fence().expect("final batch fence"),
                crate::io::DurabilityOutcome::Passed,
            ),
        ));
        let published = durable_handoff(&effects);
        assert!(matches!(
            runner.session(session).expect("live").phase(),
            SessionPhase::DurablePending
        ));
        // A repeated exact demand coalesces even after durability: it cannot
        // cancel or replace a committed handoff awaiting acknowledgement.
        let duplicate = runner.handle_event(AcquisitionEvent::AcquireRequested {
            target: target(11),
            reason: AcquireReason::Consensus,
        });
        assert!(duplicate.iter().all(|effect| {
            !matches!(
                effect,
                AcquisitionEffect::CancelSession(_) | AcquisitionEffect::SendLedgerRequest(_)
            )
        }));
        assert!(matches!(
            runner.session(session).expect("live").phase(),
            SessionPhase::DurablePending
        ));

        // A rejection carrying a different handoff id is stale and never
        // re-publishes: only the exact pending id authorizes retry.
        let effects = runner.handle_event(AcquisitionEvent::DurableHandoffRejected {
            handoff: DurableHandoffId::new(777),
            session,
            reason: HandoffRejectReason::ChannelFull,
        });
        assert!(effects.is_empty());
        assert_eq!(runner.snapshot().stale_events(), 1);

        // The exact pending id arms one fresh retry timer; rejection itself
        // cannot re-publish. A duplicate rejection while that timer is armed is
        // stale, preventing retry storms.
        let effects = runner.handle_event(AcquisitionEvent::DurableHandoffRejected {
            handoff: published.handoff(),
            session,
            reason: HandoffRejectReason::ChannelFull,
        });
        let retry = timer_operation(&effects);
        assert!(
            effects
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::PublishDurable(_)))
        );
        assert_eq!(
            runner.session(session).expect("live").pending_timer(),
            Some((TimerKind::HandoffRetry, retry))
        );
        assert_eq!(runner.snapshot().handoff_rejections(), 1);
        let duplicate = runner.handle_event(AcquisitionEvent::DurableHandoffRejected {
            handoff: published.handoff(),
            session,
            reason: HandoffRejectReason::ChannelFull,
        });
        assert!(duplicate.is_empty());
        assert_eq!(runner.snapshot().stale_events(), 2);

        // Only the exact retry wakeup re-publishes the same durable handoff.
        let effects = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: retry,
            timer: TimerKind::HandoffRetry,
        });
        assert_eq!(
            effects,
            vec![AcquisitionEffect::PublishDurable(published.clone())]
        );
        let stale_retry = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: retry,
            timer: TimerKind::HandoffRetry,
        });
        assert!(stale_retry.is_empty());
        assert_eq!(runner.snapshot().stale_events(), 3);
        assert!(matches!(
            runner.session(session).expect("live").phase(),
            SessionPhase::DurablePending
        ));

        // The eventual ack still finalizes exactly once; the retry did not
        // duplicate adoption.
        runner.handle_event(AcquisitionEvent::DurableHandoffAcknowledged(
            DurableHandoffAcknowledgement::new(published.handoff(), session),
        ));
        assert!(matches!(
            runner.session(session).expect("live").phase(),
            SessionPhase::Complete
        ));
        assert_eq!(runner.snapshot().sessions_completed(), 1);
    }

    #[test]
    fn write_failure_terminalizes_without_adoption() {
        let budget = BudgetState::new(8, AdmissionBudget::new(4, 1024), Duration::from_secs(1));
        let mut runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            budget,
            Box::new(ScriptedSeed::new(vec![ScriptedStep::Complete])),
        );
        connect(&mut runner);
        let session = acquire(&mut runner, 10);
        let packet = admitted_packet(session, AdmissionBudget::new(1, 256), 8);
        let effects = runner.handle_event(AcquisitionEvent::PacketAdmitted(packet));
        let batch = write_batch(&effects);

        let effects = runner.handle_event(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            batch.operation(),
            WriteOutcome::Failed,
        )));
        assert!(effects.contains(&AcquisitionEffect::CancelSession(session)));
        assert!(matches!(
            runner.session(session).expect("live").phase(),
            SessionPhase::Failed { .. }
        ));
        assert_eq!(
            runner.snapshot().failed_by_reason(),
            &BTreeMap::from([(FailureReason::WriteFailure, 1)])
        );

        // A late fence for the cancelled session is stale.
        runner.handle_event(AcquisitionEvent::DurabilityFenced(
            DurabilityCompletion::new(
                batch.fence().expect("final batch fence"),
                crate::io::DurabilityOutcome::Passed,
            ),
        ));
        assert_eq!(runner.snapshot().stale_events(), 1);
    }

    #[test]
    fn unseeded_base_packet_does_not_reset_the_acquisition_timeout_budget() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let effects = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&effects);
        let mut timer = timer_operation(&effects);

        // Consume six no-progress recovery intervals, leaving the seventh
        // interval to fail. An unseeded/invalid Base packet is merely admitted;
        // it must not reset this budget because no verified header was retained.
        for _ in 0..6 {
            let effects = runner.handle_event(AcquisitionEvent::TimerFired {
                operation: timer,
                timer: TimerKind::AcquireTimeout,
            });
            timer = timer_operation(&effects);
        }
        let packet = admitted_packet(session, AdmissionBudget::new(1, 256), 8);
        let _ = runner.handle_event(AcquisitionEvent::PacketAdmitted(packet));

        let effects = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: timer,
            timer: TimerKind::AcquireTimeout,
        });
        assert!(effects.contains(&AcquisitionEffect::CancelSession(session)));
        assert!(
            runner
                .session(session)
                .expect("session")
                .phase()
                .is_terminal()
        );
    }

    #[test]
    fn acquire_timeout_rearms_then_fails_after_the_budget() {
        let mut runner = CoordinatorRunner::new(RunEpoch::new(1));
        connect(&mut runner);
        let effects = acquire_with_effects(&mut runner, 10);
        let session = peer_request_session(&effects);
        let mut timer_op = timer_operation(&effects);

        // DEFAULT_MAX_ACQUIRE_TIMEOUTS permits six no-progress recovery
        // intervals. The seventh fires terminalize the session.
        for _ in 0..6 {
            let effects = runner.handle_event(AcquisitionEvent::TimerFired {
                operation: timer_op,
                timer: TimerKind::AcquireTimeout,
            });
            let rearm = effects
                .iter()
                .find_map(|effect| match effect {
                    AcquisitionEffect::ArmTimer(request) => Some(request.clone().operation()),
                    _ => None,
                })
                .expect("the deadline must be rearmed");
            assert_ne!(rearm, timer_op);
            timer_op = rearm;
        }
        assert!(
            !runner
                .session(session)
                .expect("live session")
                .phase()
                .is_terminal()
        );

        let effects = runner.handle_event(AcquisitionEvent::TimerFired {
            operation: timer_op,
            timer: TimerKind::AcquireTimeout,
        });
        assert!(effects.contains(&AcquisitionEffect::CancelSession(session)));
        assert!(matches!(
            runner.session(session).expect("live").phase(),
            SessionPhase::Failed { .. }
        ));
    }
}
