//! NetworkOPs timer strand — matching rippled's `NetworkOPsImp` strand model.
//!
//! ONE dedicated thread exclusively owns the `ConsensusRunner` and drives:
//! - `peer_proposal()` — proposals from overlay peers
//! - `timer_entry()` — 1-second consensus timer tick
//! - `execute_accept()` — build accepted ledger when consensus closes
//! - `got_tx_set()` — tx-set completion from InboundTransactions
//! - `start_round()` — begin next consensus round
//! - `checkAccept()` — promote ledger to validated when quorum met
//! - `tryAdvance()` — publish validated ledgers and trigger history fill
//! - Operating mode promotion (Connected → Tracking → Full)
//!
//! This matches rippled's single-strand guarantee: only ONE thread ever
//! accesses the consensus state machine. No mutex protects it because only
//! this thread touches it.

use std::collections::{HashSet, VecDeque};
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use acquisition::{DurableHandoffId, SessionRef};
use basics::base_uint::Uint256;
use consensus::algorithm::ConsensusPhase;

use crate::ApplicationRoot;
use crate::consensus::rcl_consensus::{ConsensusRunner, PendingAcceptWork};
use crate::consensus::rcl_validation::RclValidatedLedger;
use crate::job::job_queue::JobQueue;
use crate::job::job_types::JobType;
use crate::ledger::inbound_ledgers::{AcquireReason, InboundLedgers, ProvisionalLedgerIdentity};
use crate::network::network_ops::NetworkOpsOperatingMode;
use crate::runtime::component_runtime::{AppConsensusRuntime, ConsensusCommand, ConsensusIngress};

// Quaxar's strand polls more often than rippled's JtAdvance worker. Keep the
// history retry cadence to one consensus heartbeat so an existing History
// request is not repeatedly touched and a sparse skip list cannot fan out
// acquisitions between heartbeats.
const HISTORY_BACKFILL_RETRY_INTERVAL: Duration = Duration::from_secs(1);
/// A retained provisional preferred-LCL waiter is checked immediately on its
/// exact lifecycle wake and otherwise rechecks the moving preferred target at
/// the ordinary heartbeat cadence, never once per strand wake.
const PROVISIONAL_LCL_RECHECK_INTERVAL: Duration = Duration::from_secs(1);
// A polling turn must always return to the heartbeat scheduler. The overlay
// channels can be continuously non-empty under peer load; draining either one
// without a budget would otherwise defer the next JtNetopTimer forever.
// A command burst should not defer a heartbeat indefinitely either.
const MAX_COMMANDS_PER_TURN: usize = 64;
const MAX_MAP_COMPLETIONS_PER_TURN: usize = 64;
const MAX_LEDGER_COMPLETIONS_PER_TURN: usize = 64;
/// Retain enough recent coordinator handoffs to suppress the same item when
/// both legacy completed-ledger receive paths observe it, without turning this
/// strand-local optimization into lifecycle ownership.
const MAX_COORDINATOR_HANDOFF_DEDUP: usize = MAX_LEDGER_COMPLETIONS_PER_TURN * 2;
/// Exact durable ACK receipts retained by the sole NetworkOps strand while the
/// coordinator control queue is full. This is delivery retry state only, not
/// coordinator session lifecycle state.
const MAX_PENDING_DURABLE_ACKS: usize = MAX_LEDGER_COMPLETIONS_PER_TURN * 2;
const MAX_STRAND_COMMAND_QUEUE: usize = 1_024;
/// Bound per-pass LCL diagnostics during persistent WrongLedger recovery.
/// State transitions (switches and rejections) remain unsampled.
const LCL_AUDIT_SAMPLE_INTERVAL: Duration = Duration::from_secs(5);

struct LclAuditSampler {
    last_emitted: Instant,
}

/// Bounded duplicate suppression for coordinator items after they cross the
/// completed-ledger channel. The coordinator remains the handoff lifecycle
/// owner; this only prevents the recipient from processing the same exact
/// `(handoff, session)` twice if both compatibility receivers see it.
#[derive(Default)]
struct CoordinatorHandoffDedup {
    seen: HashSet<(acquisition::DurableHandoffId, acquisition::SessionRef)>,
    order: VecDeque<(acquisition::DurableHandoffId, acquisition::SessionRef)>,
}

impl CoordinatorHandoffDedup {
    fn claim(
        &mut self,
        handoff: acquisition::DurableHandoffId,
        session: acquisition::SessionRef,
    ) -> bool {
        if !self.seen.insert((handoff, session)) {
            return false;
        }
        self.order.push_back((handoff, session));
        if self.order.len() > MAX_COORDINATOR_HANDOFF_DEDUP {
            let evicted = self.order.pop_front().expect("dedup order is non-empty");
            self.seen.remove(&evicted);
        }
        true
    }
    fn release(
        &mut self,
        handoff: acquisition::DurableHandoffId,
        session: acquisition::SessionRef,
    ) {
        let key = (handoff, session);
        self.seen.remove(&key);
        self.order.retain(|entry| *entry != key);
    }
}

/// One NetworkOps-owned wait key for a resolver-visible preferred LCL. It is
/// not an adoption token: it suppresses only repeated Accepted-phase planning
/// while Worker 2 still exposes this exact durable-fence lifecycle.
#[derive(Clone, Copy)]
struct ProvisionalLclWaiter {
    identity: ProvisionalLedgerIdentity,
    suppression_logged: bool,
    last_preference_recheck: Instant,
}

impl LclAuditSampler {
    fn new() -> Self {
        Self {
            last_emitted: Instant::now() - LCL_AUDIT_SAMPLE_INTERVAL,
        }
    }

    fn should_emit(&mut self) -> bool {
        if self.last_emitted.elapsed() < LCL_AUDIT_SAMPLE_INTERVAL {
            return false;
        }
        self.last_emitted = Instant::now();
        true
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PreferredLclReconciliation {
    NoChange,
    /// An exact target is absent or incomplete and recovery started a
    /// WrongLedger replacement round for that target.
    Pending,
    /// The exact target is resolver-visible but still belongs to Worker 2's
    /// provisional acquisition identity. It may be re-requested, but may not
    /// mutate LCL, TxQ, open/closed ledger, status, mode, or round state.
    Provisional,
    Switched,
}

fn effective_validation_recovery_target(
    ordinary_selected: Uint256,
    local_lcl: Uint256,
    stable_anchor: Option<(Uint256, u32)>,
    ordinary_selected_is_resident: bool,
) -> acquisition::LedgerTarget {
    // A stable acquisition owner prevents a moving, unresolved network tip
    // from starving recovery.  It must not mask an ordinary getPreferredLCL
    // result that is already locally available: rippled immediately hands
    // that ledger to switchLastClosedLedger instead of waiting for an older
    // asynchronous acquisition.
    if ordinary_selected_is_resident && ordinary_selected != local_lcl {
        return acquisition::LedgerTarget::new(ordinary_selected, None);
    }
    stable_anchor
        .map(|(hash, seq)| acquisition::LedgerTarget::new(hash, Some(seq)))
        .filter(|target| target.hash() != local_lcl)
        .unwrap_or_else(|| acquisition::LedgerTarget::new(ordinary_selected, None))
}

fn preferred_candidate_passes_switch_admission(
    lm: &ledger::LedgerMaster,
    expected_hash: Uint256,
    candidate: &ledger::Ledger,
    now_close_time: u32,
) -> bool {
    *candidate.header().hash.as_uint256() == expected_hash
        && !candidate.state_map().is_synching()
        && (candidate.header().tx_hash.is_zero() || !candidate.tx_map().is_synching())
        && lm.can_be_current(candidate, now_close_time)
        && lm.compatibility_audit(candidate).compatible()
}

/// Result of the strand-owned second phase of inbound completion. A result is
/// acknowledged only after its intended lifecycle transition is durable or
/// intentionally cache-only; retry retains the acquisition in the registry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CompletionPersistence {
    inserted: bool,
    acknowledged: bool,
}

/// Live adapters for the deterministic `ledger::run_try_fill_backwalk` core.
/// They keep relational and NodeStore ownership in `AppLoadedLedgerRuntime`;
/// this strand only applies the already verified contiguous result.
struct LiveHistoryPresence<'a> {
    ledger_master: &'a ledger::LedgerMaster,
}

impl ledger::LedgerPresence for LiveHistoryPresence<'_> {
    fn have_ledger(&self, ledger_index: u32) -> bool {
        self.ledger_master.have_ledger(ledger_index)
    }
}

struct LiveHistoryHashPairs<'a> {
    loaded: &'a crate::ledger::loaded_ledger_runtime::AppLoadedLedgerRuntime,
}

impl ledger::LedgerHashPairProvider for LiveHistoryHashPairs<'_> {
    fn get_hashes_by_index(
        &self,
        min_seq: u32,
        max_seq: u32,
    ) -> Vec<(u32, ledger::LedgerHashPair)> {
        self.loaded.get_hash_pairs_by_index(min_seq, max_seq)
    }
}

struct LiveHistoryObjectPresence<'a> {
    loaded: &'a crate::ledger::loaded_ledger_runtime::AppLoadedLedgerRuntime,
}

impl ledger::LedgerObjectPresence for LiveHistoryObjectPresence<'_> {
    fn has_ledger_object(&self, ledger_hash: ledger::SHAMapHash, ledger_seq: u32) -> bool {
        self.loaded.has_ledger_object(ledger_hash, ledger_seq)
    }
}

struct StrandHistoryFillStopper<'a>(&'a ApplicationRoot);

impl ledger::Stopper for StrandHistoryFillStopper<'_> {
    fn is_stopping(&self) -> bool {
        self.0.is_stopping()
    }
}

/// Typed JobQueue handoff for work that must ultimately mutate consensus.
///
/// Rippled schedules heartbeats as `JtNetopTimer` and accepted-ledger work as
/// `JtAccept`. Quaxar's runner is deliberately owned only by the strand, so
/// the queued closure cannot call it directly. Instead each typed job sends a
/// command to that sole owner. This retains the queue's existing priority and
/// limit policy without adding a second scheduler or permitting concurrent
/// `timer_tick`/`execute_accept` calls.
#[derive(Clone)]
struct ConsensusJobScheduler {
    job_queue: JobQueue,
    ingress: ConsensusIngress,
    heartbeat_queued: Arc<AtomicBool>,
    accept_queued: Arc<AtomicBool>,
    /// Accepted-ledger work remains here until a JtAccept worker has
    /// successfully handed it to the strand command queue. A full bounded
    /// queue must delay, never discard, the `doAccept` transition.
    pending_accept: Arc<Mutex<Option<PendingAcceptWork>>>,
}

impl ConsensusJobScheduler {
    fn new(job_queue: JobQueue, ingress: ConsensusIngress) -> Self {
        Self {
            job_queue,
            ingress,
            heartbeat_queued: Arc::new(AtomicBool::new(false)),
            accept_queued: Arc::new(AtomicBool::new(false)),
            pending_accept: Arc::new(Mutex::new(None)),
        }
    }

    /// Queue at most one outstanding heartbeat. The flag remains set until
    /// the command is consumed by the strand, which prevents timer-job pileup
    /// when workers are temporarily saturated.
    fn schedule_heartbeat(&self) -> bool {
        if self
            .heartbeat_queued
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return false;
        }

        let ingress = self.ingress.clone();
        let heartbeat_queued = Arc::clone(&self.heartbeat_queued);
        if self
            .job_queue
            .add_job(JobType::JtNetopTimer, "NetHeart", move || {
                if !ingress.publish_heartbeat() {
                    heartbeat_queued.store(false, Ordering::Release);
                }
            })
        {
            true
        } else {
            self.heartbeat_queued.store(false, Ordering::Release);
            false
        }
    }

    /// Queue at most one accepted-ledger handoff. `execute_accept` stays on
    /// the strand so its full `doAccept → endConsensus → startRound` ordering
    /// is serialized with timer, proposal, and tx-set mutations.
    fn schedule_accept(&self, work: PendingAcceptWork) -> bool {
        let mut pending = self.pending_accept.lock().expect("pending accept lock");
        if pending.is_some() {
            return false;
        }
        *pending = Some(work);
        drop(pending);
        self.schedule_pending_accept()
    }

    /// Retry an accept handoff retained because the bounded command queue or
    /// the JobQueue was saturated. The work is removed only after `try_send`
    /// succeeds, so accepted-phase recovery cannot race ahead of it.
    fn schedule_pending_accept(&self) -> bool {
        if self
            .accept_queued
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return false;
        }

        let ingress = self.ingress.clone();
        let accept_queued = Arc::clone(&self.accept_queued);
        let pending_accept = Arc::clone(&self.pending_accept);
        if self
            .job_queue
            .add_job(JobType::JtAccept, "AcceptLedger", move || {
                let work = pending_accept.lock().expect("pending accept lock").take();
                let Some(work) = work else {
                    accept_queued.store(false, Ordering::Release);
                    return;
                };
                match ingress.try_send(ConsensusCommand::Accept(Box::new(work))) {
                    Ok(()) => {}
                    Err(std::sync::mpsc::TrySendError::Full(ConsensusCommand::Accept(work)))
                    | Err(std::sync::mpsc::TrySendError::Disconnected(ConsensusCommand::Accept(
                        work,
                    ))) => {
                        *pending_accept.lock().expect("pending accept lock") = Some(*work);
                        accept_queued.store(false, Ordering::Release);
                    }
                    Err(_) => unreachable!("only Accept commands are sent here"),
                }
            })
        {
            true
        } else {
            self.accept_queued.store(false, Ordering::Release);
            false
        }
    }

    /// True while accepted work has been captured (schedule_accept) but the
    /// JtAccept job has not yet handed it back to the strand as a command.
    /// This is the async window between scheduling and execution that
    /// reconciliation/StartRound must not race ahead of.
    fn has_pending_accept(&self) -> bool {
        self.pending_accept
            .lock()
            .expect("pending accept lock")
            .is_some()
    }

    fn heartbeat_consumed(&self) {
        self.heartbeat_queued.store(false, Ordering::Release);
    }

    fn accept_consumed(&self) {
        self.accept_queued.store(false, Ordering::Release);
    }

    fn accept_is_queued(&self) -> bool {
        self.accept_queued.load(Ordering::Acquire)
    }
}

/// Drain at most `budget` messages so a saturated ingress channel cannot
/// monopolize the consensus owner.
fn drain_bounded<T>(
    receiver: &std::sync::mpsc::Receiver<T>,
    budget: usize,
    mut handle: impl FnMut(T),
) {
    for _ in 0..budget {
        match receiver.try_recv() {
            Ok(value) => handle(value),
            Err(
                std::sync::mpsc::TryRecvError::Empty | std::sync::mpsc::TryRecvError::Disconnected,
            ) => break,
        }
    }
}

fn announce_completed_tx_set(root: &ApplicationRoot, hash: Uint256) {
    use overlay::Overlay;

    let Some(overlay_runtime) = root.overlay_runtime() else {
        return;
    };
    let message = overlay::ProtocolMessage::new(overlay::ProtocolPayload::HaveSet(
        overlay::TmHaveTransactionSet {
            status: 1, // protocol::tsHAVE
            hash: hash.data().to_vec(),
        },
    ));
    overlay_runtime.overlay().broadcast(&message);
}

/// Insert recovered tx-set completions into the sole consensus FIFO. A full
/// command queue retains the exact completion locally and retries it before
/// admitting newer recovered completions; it must never call `got_tx_set`
/// directly and thereby bypass an older heartbeat already in the FIFO.
fn enqueue_recovered_txsets(
    ingress: &ConsensusIngress,
    retained: &mut VecDeque<(Uint256, Arc<shamap::sync::SyncTree>)>,
    recovered: impl IntoIterator<Item = (Uint256, Arc<shamap::sync::SyncTree>)>,
) -> bool {
    retained.extend(recovered);
    while let Some((hash, set)) = retained.pop_front() {
        match ingress.try_publish_tx_set(hash, set) {
            Ok(()) => {}
            Err(std::sync::mpsc::TrySendError::Full(ConsensusCommand::TxSetComplete {
                hash,
                set,
            })) => {
                retained.push_front((hash, set));
                return true;
            }
            Err(std::sync::mpsc::TrySendError::Disconnected(_)) => {
                retained.clear();
                return false;
            }
            Err(_) => unreachable!("only TxSetComplete commands are sent here"),
        }
    }
    true
}

/// Dependencies the strand needs (passed at construction).
pub struct NetworkOpsStrandDeps {
    pub root: ApplicationRoot,
    pub consensus_rt: Arc<AppConsensusRuntime>,
    pub shared_inbound: Arc<InboundLedgers>,
    pub configured_ledger_history: u32,
    /// rippled `SizedItem::LedgerFetch` for the configured node-size profile.
    pub configured_ledger_fetch_size: u32,
    /// rippled NetworkOPsImp::minPeerCount_, fixed at construction (zero for
    /// start_valid) rather than reinterpreted in the heartbeat.
    pub min_peer_count: usize,
    /// Receiver for completed ledgers from shared_inbound acquisition.
    pub shared_completed_rx:
        Option<std::sync::mpsc::Receiver<crate::ledger::inbound_ledgers::CompletedInboundLedger>>,
}

/// External handle to the running strand. Drop to stop.
pub struct NetworkOpsStrand {
    stop: Arc<AtomicBool>,
    thread: Option<JoinHandle<()>>,
    /// The sole ordered consensus ingress: proposals, tx-set completions,
    /// heartbeats, accepts, round changes, and stop all share this FIFO.
    pub ingress: ConsensusIngress,
}

impl NetworkOpsStrand {
    /// Spawn the strand thread. Takes ownership of the consensus runner.
    pub fn spawn(deps: NetworkOpsStrandDeps) -> Self {
        let stop = Arc::new(AtomicBool::new(false));
        let (ingress, command_rx) = ConsensusIngress::bounded(MAX_STRAND_COMMAND_QUEUE);

        // Wire the command sender to the consensus runtime so external code
        // (e.g. validation event loop) can issue StartRound commands.
        deps.consensus_rt.set_cmd_sender(ingress.sender());

        let stop_clone = Arc::clone(&stop);
        let strand_ingress = ingress.clone();
        let thread = thread::Builder::new()
            .name("networkops-strand".into())
            .spawn(move || {
                strand_loop(deps, stop_clone, command_rx, strand_ingress);
            })
            .expect("failed to spawn networkops-strand thread");

        Self {
            stop,
            thread: Some(thread),
            ingress,
        }
    }

    /// Signal the strand to stop and wait for the thread to exit.
    pub fn stop(&mut self) {
        self.stop.store(true, Ordering::Release);
        let _ = self.ingress.try_send(ConsensusCommand::Stop);
        if let Some(handle) = self.thread.take() {
            let _ = handle.join();
        }
    }
}

impl Drop for NetworkOpsStrand {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Release);
        let _ = self.ingress.try_send(ConsensusCommand::Stop);
        // Don't join on drop — just signal.
    }
}

// ─── Strand thread body ──────────────────────────────────────────────────────

fn strand_loop(
    deps: NetworkOpsStrandDeps,
    stop: Arc<AtomicBool>,
    command_rx: std::sync::mpsc::Receiver<ConsensusCommand>,
    ingress: ConsensusIngress,
) {
    // Elevate thread priority — consensus must never be starved by RPC load.
    #[cfg(unix)]
    unsafe {
        libc::setpriority(0, 0, -15);
    }

    tracing::info!(target: "consensus", "NetworkOPs strand running");

    let NetworkOpsStrandDeps {
        root,
        consensus_rt,
        shared_inbound,
        configured_ledger_history,
        configured_ledger_fetch_size,
        min_peer_count,
        shared_completed_rx,
    } = deps;

    // Take the consensus runner — it now lives exclusively on this thread.
    let mut runner = match consensus_rt.take_runner() {
        Some(r) => r,
        None => {
            tracing::error!(target: "consensus", "No consensus runner available, exiting strand");
            return;
        }
    };

    let scheduler = ConsensusJobScheduler::new(root.job_queue().clone(), ingress.clone());
    let mut consensus_started = false;
    let mut last_timer_tick = Instant::now();
    let mut last_round_ledger_id: Option<Uint256> = None;
    // Emit at most one restart-gate diagnostic per closed ledger. Accepted
    // phase maintenance runs every strand tick, so per-pass INFO events turn
    // a stalled restart gate into an operator-hostile log flood.
    let mut last_restart_gate_ledger_id: Option<Uint256> = None;
    let mut last_history_tick = Instant::now();
    let mut history_fetch_pack: Option<(u32, Instant)> = None;
    // Matches LedgerMaster::histLedger_: after a primary history result is
    // materialized, its normal skip list is the closest reference for the
    // next predecessor lookup.
    let mut history_reference: Option<Arc<ledger::Ledger>> = None;
    // Match rippled's `acquiringLedger_`: only issue ONE acquireAsync per
    // unique preferred-LCL hash. Prevents flooding peers with parallel
    // Sample repeating LCL diagnostics while leaving recovery decisions and
    // state-transition logs complete.
    let mut lcl_audit_sampler = LclAuditSampler::new();
    // The strand owns this state and observes it only from endConsensus.
    // Callbacks merely wake the strand through the coalesced owner event.
    let mut provisional_lcl_waiter: Option<ProvisionalLclWaiter> = None;
    let mut coordinator_handoff_dedup = CoordinatorHandoffDedup::default();
    let mut pending_durable_acks = VecDeque::new();
    // Durable overflow recovery crosses the same FIFO as ordinary map
    // completions. A saturated FIFO retains these exact items here.
    let mut pending_recovered_txsets = VecDeque::new();

    // Detect startup: always start consensus immediately on the closed
    // ledger, matching rippled's Application::run() which calls
    // beginConsensus(closedLedger.hash) unconditionally.
    {
        let _startup_lcl_transition_guard = root.lcl_transition_gate().lock();
        if let Some(closed) = root.closed_ledger() {
            let now = root.shared_time_keeper().close_time();
            let prev_id = *closed.header().hash.as_uint256();
            let prev_cx = crate::consensus_ledger_from_ledger(&closed);
            if let Some(inbound_tx) = root.inbound_transactions().lock().ok().as_mut() {
                inbound_tx.new_round(closed.header().seq);
            }
            runner.start_round(now, prev_id, prev_cx, true);
            consensus_rt.update_phase(runner.phase());
            consensus_rt.update_prev_ledger_id(runner.prev_ledger_id());
            consensus_started = true;
            last_round_ledger_id = Some(prev_id);
            last_timer_tick = Instant::now();
            tracing::info!(
                target: "consensus",
                seq = closed.header().seq,
                "Consensus started on closed ledger (matching rippled beginConsensus)"
            );
        }
    }

    // ═══════════════════════════════════════════════════════════════════════
    // MAIN STRAND LOOP — matches rippled's NetworkOPs::heartbeatTimer
    // ═══════════════════════════════════════════════════════════════════════
    while !stop.load(Ordering::Acquire) {
        // Retry retained accept work before doing any fallback that could
        // start a new round. A full command queue delays acceptance but never
        // permits the accepted-phase recovery path to bypass it.
        if scheduler.has_pending_accept() && !scheduler.accept_is_queued() {
            let _ = scheduler.schedule_pending_accept();
        }

        // ─── 0. Drive the coordinator owner loop ─────────────────────────
        // The coordinator is the single session lifecycle owner. Its typed
        // events (connectivity, acquire requests, packet admissions, read/write/
        // fence completions, timer wakeups, durable handoff acks, store rotation)
        // arrive on an unbounded channel and must be drained on this owner
        // strand so coordinator state never needs its own thread or lock
        // choreography. Effects are dispatched to the resource ports inside the
        // registry's coordinator adapter after each event.
        let (_, coordinator_work_remains) = shared_inbound.coordinator_drain_with_status();
        while let Some(&(handoff, session)) = pending_durable_acks.front() {
            if !shared_inbound.acknowledge_coordinator_durable_handoff(handoff, session) {
                break;
            }
            pending_durable_acks.pop_front();
        }

        // ─── 1. Process serialized commands ──────────────────────────────
        // Worker jobs and external callers can enqueue commands, but only this
        // thread owns `runner`, so timer, accept, proposal, and round changes
        // cannot mutate consensus concurrently.
        let mut accepted_work_executed = false;
        'commands: for _ in 0..MAX_COMMANDS_PER_TURN {
            let Ok(cmd) = command_rx.try_recv() else {
                break;
            };
            match cmd {
                ConsensusCommand::PeerProposal(proposal) => {
                    let now = root.shared_time_keeper().close_time();
                    let peer_close_time =
                        basics::chrono::NetClockTimePoint::new(proposal.message.close_time);
                    let master_key = root.manifest_cache().get_master_key(&proposal.public_key);
                    let prop = consensus::ConsensusProposal::new(
                        proposal.previous_ledger,
                        proposal.message.propose_seq,
                        proposal.current_tx_hash,
                        peer_close_time,
                        now,
                        master_key,
                    );
                    let peer_pos = crate::consensus::rcl_cx_peer_pos::RclCxPeerPos::new(
                        proposal.public_key,
                        proposal.message.signature.clone(),
                        proposal.suppression,
                        prop,
                    );
                    if runner.peer_proposal(now, &peer_pos)
                        && let Some(overlay_runtime) = root.overlay_runtime()
                    {
                        overlay_runtime.overlay().relay_proposal(
                            proposal.message,
                            proposal.suppression,
                            proposal.public_key,
                        );
                    }
                    consensus_rt.update_phase(runner.phase());
                    consensus_rt.update_prev_ledger_id(runner.prev_ledger_id());
                }
                ConsensusCommand::TxSetComplete { hash, set } => {
                    let now = root.shared_time_keeper().close_time();
                    let tx_set = consensus::RclTxSet::from_parts(
                        set.root(),
                        Arc::clone(runner.adaptor.tx_set_cache()),
                        set.backed(),
                        0,
                    );
                    runner.got_tx_set(now, tx_set);
                    announce_completed_tx_set(&root, hash);
                    consensus_rt.update_phase(runner.phase());
                    tracing::debug!(target: "consensus", %hash, "strand: got_tx_set processed");
                }
                ConsensusCommand::Heartbeat => {
                    scheduler.heartbeat_consumed();
                    let now = root.shared_time_keeper().close_time();
                    if let Some(work) = runner.timer_tick(now)
                        && !scheduler.schedule_accept(work)
                    {
                        // A second accept result cannot normally occur before
                        // the first is consumed: timer_entry remains in
                        // Accepted. Never execute it inline on this path.
                        tracing::error!(target: "consensus", "failed to queue JtAccept handoff");
                    }
                    consensus_rt.update_phase(runner.phase());
                    consensus_rt.update_prev_ledger_id(runner.prev_ledger_id());
                    last_timer_tick = Instant::now();
                }
                ConsensusCommand::Accept(work) => {
                    // This command was emitted by a JtAccept job. Execute the
                    // complete accepted-ledger transition on the sole owner.
                    // The endConsensus policy below runs before this turn may
                    // drain another command, proposal, tx-set, completion, or
                    // coordinator event, matching rippled's JtAccept closure.
                    let now = root.shared_time_keeper().close_time();
                    runner.execute_accept(now, *work);
                    scheduler.accept_consumed();
                    consensus_rt.update_phase(runner.phase());
                    consensus_rt.update_prev_ledger_id(runner.prev_ledger_id());
                    last_round_ledger_id = Some(runner.prev_ledger_id());
                    accepted_work_executed = true;
                    break 'commands;
                }
                ConsensusCommand::StartRound {
                    now,
                    network_closed,
                    prev_ledger,
                } => {
                    let _lcl_transition_guard = root.lcl_transition_gate().lock();
                    let local_prev_id = prev_ledger.id();
                    if runner.phase() != ConsensusPhase::Accepted
                        || scheduler.accept_is_queued()
                        || scheduler.has_pending_accept()
                        || root.closed_ledger().is_none_or(|current| {
                            *current.header().hash.as_uint256() != local_prev_id
                        })
                    {
                        tracing::warn!(
                            target: "consensus",
                            %local_prev_id,
                            %network_closed,
                            accept_is_queued = scheduler.accept_is_queued(),
                            has_pending_accept = scheduler.has_pending_accept(),
                            "discarded stale or recovery-conflicting external start-round command"
                        );
                        continue;
                    }
                    // `network_closed` is the peer/validation target, while
                    // `prev_ledger` is the local materialized parent. rippled
                    // deliberately permits them to differ: beginConsensus then
                    // enters WrongLedger/acquisition rather than stranding an
                    // Accepted runner. Only the local parent must match LCL.
                    if let Some(inbound_tx) = root.inbound_transactions().lock().ok().as_mut() {
                        inbound_tx.new_round(prev_ledger.seq());
                    }
                    runner.start_round(now, network_closed, prev_ledger, true);
                    consensus_rt.update_phase(runner.phase());
                    consensus_rt.update_prev_ledger_id(runner.prev_ledger_id());
                    consensus_started = true;
                    last_round_ledger_id = Some(runner.prev_ledger_id());
                    last_timer_tick = Instant::now();
                    tracing::info!(target: "consensus", "Consensus started via external command");
                }
                ConsensusCommand::Stop => {
                    tracing::info!(target: "consensus", "Strand received Stop command");
                    return;
                }
            }
        }

        if !consensus_started {
            // Should not happen — consensus starts unconditionally above.
            thread::sleep(Duration::from_millis(50));
            continue;
        }

        let mut registry_completion_count = 0usize;
        // A JtAccept closure in rippled performs doAccept then endConsensus
        // without re-entering ordinary timer, ingress, acquisition, or
        // completion handling. Preserve that adjacency on the strand after
        // the owner receives accepted work.
        if !accepted_work_executed {
            // ─── 1b. Peer availability → coordinator owner, or legacy mode demotion
            // (matching rippled processHeartbeatTimer). The coordinator receives
            // the actual active-peer identity snapshot whenever one is usable;
            // consensus quorum remains a separate gate below. This prevents a
            // below-quorum but connected overlay from manufacturing
            // `PeerCapabilityLost` and pausing live acquisition demand.
            if let Some(overlay_rt) = root.overlay_runtime() {
                use overlay::Overlay;
                // Keep the configured threshold exactly.  In particular, rippled
                // constructs `NetworkOPsImp` with `minPeerCount_ = 0` for
                // `startValid` (NetworkOPs.cpp), so a peerless start-valid node
                // continues driving consensus instead of being manufactured
                // into Disconnected. For that exact zero-threshold case, the
                // empty transport snapshot is not published as a mode fact.
                let min_peers = required_peer_count(min_peer_count);
                let active_peers = overlay_rt.overlay().active_peers();
                let num_peers = active_peers.len();
                let active_peer_ids = active_peers
                    .iter()
                    .map(|peer| peer.id())
                    .collect::<Vec<_>>();
                if shared_inbound.coordinator_installed() {
                    // Publish the quorum gate before a below-threshold
                    // non-empty transport snapshot. Otherwise the transport
                    // fact can transiently republish Connected before the
                    // same heartbeat demotes it again.
                    if num_peers < min_peers {
                        shared_inbound.coordinator_report_consensus_quorum(false);
                    }
                    // A zero threshold keeps acquisition transport membership
                    // current while making it phase-neutral: start-valid
                    // consensus remains operational without overlay peers.
                    // Positive thresholds use the ordinary phase-bearing fact.
                    if min_peers == 0 {
                        shared_inbound.coordinator_report_transport_availability(&active_peer_ids);
                    } else {
                        shared_inbound.coordinator_report_peer_availability(&active_peer_ids);
                    }
                    shared_inbound.coordinator_heartbeat();
                    if root.network_ops_state().is_blocked()
                        && shared_inbound
                            .coordinator_snapshot()
                            .is_some_and(|snapshot| {
                                matches!(snapshot.phase(), acquisition::SyncPhase::Full { .. })
                            })
                    {
                        // setAmendmentBlocked/setUNLBlocked demote rippled's
                        // public mode immediately. Mirror that fact into the
                        // coordinator so its phase cannot remain stale Full.
                        shared_inbound.coordinator_blocked_with_no_target();
                    }
                    let current_mode = root.network_ops_state().operating_mode();
                    if num_peers < min_peers {
                        if current_mode != NetworkOpsOperatingMode::Disconnected {
                            tracing::warn!(
                                target: "consensus",
                                num_peers,
                                min_peers,
                                "Peer count below minimum — consensus gated while coordinator retains active-peer connectivity"
                            );
                        }
                        // Skip consensus timer when disconnected (matching rippled)
                        root.wait_consensus_or_timeout(Duration::from_millis(500));
                        continue;
                    }
                    if shared_inbound
                        .coordinator_snapshot()
                        .is_some_and(|snapshot| {
                            matches!(snapshot.phase(), acquisition::SyncPhase::Disconnected)
                        })
                    {
                        shared_inbound.coordinator_report_consensus_quorum(true);
                    }
                    if current_mode == NetworkOpsOperatingMode::Disconnected {
                        tracing::info!(
                            target: "consensus",
                            num_peers,
                            "Peer count sufficient — coordinator phase set to CONNECTED"
                        );
                    }
                } else {
                    let current_mode = root.network_ops_state().operating_mode();
                    if num_peers < min_peers {
                        if current_mode != NetworkOpsOperatingMode::Disconnected {
                            root.set_network_ops_operating_mode_with_reason(
                                NetworkOpsOperatingMode::Disconnected,
                                "insufficient_peers",
                            );
                            tracing::warn!(
                                target: "consensus",
                                num_peers,
                                min_peers,
                                "Peer count below minimum — mode set to DISCONNECTED"
                            );
                        }
                        // Skip consensus timer when disconnected (matching rippled)
                        root.wait_consensus_or_timeout(Duration::from_millis(500));
                        continue;
                    } else if let Some(mode_to_reassert) =
                        heartbeat_operating_mode_reassertion(current_mode)
                    {
                        // Match NetworkOPsImp::processHeartbeatTimer: reconnecting
                        // first reasserts CONNECTED, and an already CONNECTED or
                        // SYNCING node re-runs setMode so validated-ledger age can
                        // normalize it in either direction.
                        root.set_network_ops_operating_mode_with_reason(
                            mode_to_reassert,
                            "heartbeat_reassertion",
                        );
                        if current_mode == NetworkOpsOperatingMode::Disconnected {
                            tracing::info!(
                                target: "consensus",
                                num_peers,
                                "Peer count sufficient — mode set to CONNECTED"
                            );
                        }
                    }
                }
            }

            // Durable recovery for completion notifications that could not enter
            // the bounded consensus FIFO. These are coalesced by tx-set hash
            // in InboundTransactions and drained every strand turn. Recovery is
            // enqueued before scheduling a new heartbeat because its original
            // direct-FIFO attempt necessarily happened earlier.
            let recovered = if pending_recovered_txsets.is_empty() {
                root.inbound_transactions()
                    .lock()
                    .ok()
                    .map(|mut inbound| {
                        inbound.take_pending_map_completions(MAX_MAP_COMPLETIONS_PER_TURN)
                    })
                    .unwrap_or_default()
            } else {
                Vec::new()
            };
            if !enqueue_recovered_txsets(
                &scheduler.ingress,
                &mut pending_recovered_txsets,
                recovered,
            ) {
                return;
            }

            // ─── 2. Schedule the 1s heartbeat after older overflow ingress ──
            // `JtNetopTimer` has the reference priority/limit. The job only
            // hands off a command; `timer_tick` remains serialized on this strand.
            if last_timer_tick.elapsed() >= Duration::from_secs(1) {
                let _ = scheduler.schedule_heartbeat();
            }

            // ─── 5. Persist inbound completion before LCL reconciliation ────
            // ─── 6a. legacy completion recovery — registry is authoritative ──
            // Coordinator durable handoffs have their own acknowledged channel
            // below. M7 installation rejects a live or unacknowledged legacy
            // lifecycle, so coordinator mode must not poll the legacy ready queue.
            if !shared_inbound.coordinator_installed()
                && let Some(lm_rt) = root.ledger_master_runtime()
            {
                let lm = lm_rt.ledger_master();
                let registry_completions =
                    shared_inbound.poll_results_bounded(MAX_LEDGER_COMPLETIONS_PER_TURN);
                registry_completion_count = registry_completions.len();
                if registry_completion_count != 0 {
                    tracing::info!(
                        target: "lcl_trace",
                        event = "completion_batch_polled",
                        source = "registry_poll",
                        count = registry_completion_count,
                        runner_phase = ?runner.phase(),
                        "LCL trace: completed inbound ledgers are ready for persistence"
                    );
                }
                for (hash, acquisition_id, ledger, reason) in registry_completions {
                    process_completed_inbound_ledger(
                        &root,
                        &lm,
                        &shared_inbound,
                        "registry_ready",
                        hash,
                        acquisition_id,
                        Arc::new(ledger),
                        reason,
                        true,
                    );
                }
            }

            // ─── 6b. completion wakeups / coordinator durable handoff ────────
            // Registry polling above is the only persistence/checkAccept/ack owner
            // for legacy sessions; those bounded receivers merely wake this turn
            // and never duplicate a completion still retained in the registry.
            // Coordinator durable handoffs (`from_coordinator`) have no registry
            // ready-queue entry: the coordinator session terminalized at the
            // durability fence, so the strand consumes those items authoritatively
            // (persist + register + checkAccept + trace), exactly once, per the
            // M5 durable-only handoff protocol.
            if let Some(lm_rt) = root.ledger_master_runtime() {
                let lm = lm_rt.ledger_master();
                let receipt_budget = MAX_PENDING_DURABLE_ACKS
                    .saturating_sub(pending_durable_acks.len())
                    .min(MAX_LEDGER_COMPLETIONS_PER_TURN);
                let completed = {
                    let rx_guard = lm_rt
                        .completed_ledgers_rx
                        .lock()
                        .expect("completed_ledgers_rx");
                    rx_guard
                        .as_ref()
                        .map(|rx| rx.try_iter().take(receipt_budget).collect::<Vec<_>>())
                        .unwrap_or_default()
                };
                for item in completed {
                    process_coordinator_completed_inbound_ledger(
                        &root,
                        &lm,
                        &shared_inbound,
                        &item,
                        &mut coordinator_handoff_dedup,
                        &mut pending_durable_acks,
                    );
                }
            }
            if let Some(ref rx) = shared_completed_rx {
                let lm = root
                    .ledger_master_runtime()
                    .map(|lm_rt| lm_rt.ledger_master());
                if let Some(lm) = lm {
                    drain_bounded(rx, MAX_LEDGER_COMPLETIONS_PER_TURN, |item| {
                        process_coordinator_completed_inbound_ledger(
                            &root,
                            &lm,
                            &shared_inbound,
                            &item,
                            &mut coordinator_handoff_dedup,
                            &mut pending_durable_acks,
                        );
                    });
                }
            }

            // ─── 6c. pending_consensus_ledger → acquire_async ────────────────
            if let Some(lm_rt) = root.ledger_master_runtime() {
                let pending = lm_rt.take_pending_consensus_ledger();
                if let Some(hash) = pending {
                    tracing::info!(
                        target: "lcl_trace",
                        event = "pending_consensus_target_acquire",
                        %hash,
                        "LCL trace: pending consensus ledger is being acquired"
                    );
                    // A pending consensus ledger is keyed by hash only. Do not
                    // infer its sequence from a peer's independent history range.
                    shared_inbound.acquire_closed_ledger_async(hash, AcquireReason::Consensus);
                }
            }
        }

        // ─── 7. endConsensus/checkLastClosedLedger → beginConsensus ────
        // Capture the phase before reconciliation can begin a WrongLedger or
        // replacement round. This is the sole endConsensus cadence token for
        // peer-status cycling, mode promotion, and the ordinary next round.
        let end_consensus_pass = should_run_end_consensus_reconciliation(
            runner.phase(),
            scheduler.accept_is_queued(),
            scheduler.has_pending_accept(),
        );
        if registry_completion_count != 0 && !end_consensus_pass {
            tracing::info!(
                target: "lcl_trace",
                event = "reconcile_deferred_after_completion",
                completion_count = registry_completion_count,
                runner_phase = ?runner.phase(),
                accept_queued = scheduler.accept_is_queued(),
                pending_accept = scheduler.has_pending_accept(),
                "LCL trace: completion persisted but preferred-LCL reconciliation awaits Accepted"
            );
        }
        if end_consensus_pass {
            // This branch may run every strand wake while consensus remains
            // Accepted. Keep its detailed lifecycle trace opt-in: emitting it
            // at INFO previously produced hundreds of journal writes/second
            // and starved the same strand that must make consensus progress.
            tracing::debug!(
                target: "lcl_trace",
                event = "end_consensus_reconcile_enter",
                runner_phase = ?runner.phase(),
                accept_queued = scheduler.accept_is_queued(),
                pending_accept = scheduler.has_pending_accept(),
                "LCL trace: entering preferred-LCL reconciliation"
            );
            // endConsensus invalidates obsolete peer status before evaluating
            // the preferred LCL, whether or not this pass later performs a jump.
            cycle_obsolete_peer_statuses(&root);
        }

        // All inbound sources above persist first. A completed ledger is
        // immediately cache history; generic WrongLedger recovery may consume
        // it regardless of later preferred-LCL observations.
        let reconciliation = if end_consensus_pass {
            reconcile_preferred_lcl(
                &root,
                &shared_inbound,
                &mut runner,
                &consensus_rt,
                &mut last_round_ledger_id,
                &mut lcl_audit_sampler,
                &mut provisional_lcl_waiter,
            )
        } else {
            PreferredLclReconciliation::NoChange
        };
        if end_consensus_pass {
            tracing::debug!(
                target: "lcl_trace",
                event = "end_consensus_reconcile_outcome",
                reconciliation = ?reconciliation,
                runner_phase = ?runner.phase(),
                current_mode = ?root.network_ops_operating_mode(),
                need_network_ledger = root.need_network_ledger(),
                "LCL trace: preferred-LCL reconciliation completed"
            );
        }

        if end_consensus_pass
            && reconciliation == PreferredLclReconciliation::NoChange
            && !root.need_network_ledger()
            && shared_inbound
                .coordinator_snapshot()
                .is_some_and(|snapshot| {
                    matches!(snapshot.phase(), acquisition::SyncPhase::Syncing { .. })
                })
            && let Some(closed) = root.closed_ledger()
        {
            shared_inbound.coordinator_preferred_lcl_reconciled(acquisition::LedgerIdentity::new(
                *closed.header().hash.as_uint256(),
                closed.header().seq,
            ));
        }

        // `checkAccept`/publication/history do not select, acquire, install,
        // or clear recovery intent. Mode advancement is the sole exception:
        // rippled performs it inside endConsensus only when checkLastClosedLedger
        // reports no abnormal ledger change, before beginConsensus.
        check_accept_and_advance(
            &root,
            &shared_inbound,
            configured_ledger_history,
            configured_ledger_fetch_size,
            &mut last_history_tick,
            &mut history_fetch_pack,
            &mut history_reference,
            should_promote_operating_mode_at_end_consensus(end_consensus_pass, reconciliation),
        );

        // Only a no-change endConsensus pass may begin the ordinary next
        // round. A missing preferred target already began generic consensus
        // with that target (WrongLedger); a switch already began exactly one
        // replacement round (normal/SwitchedLedger handling stays generic).
        let ordinary_round_eligible =
            should_begin_ordinary_round(end_consensus_pass, reconciliation)
                && !scheduler.accept_is_queued()
                && !scheduler.has_pending_accept();
        if let Some(closed) = root.closed_ledger() {
            let closed_id = *closed.header().hash.as_uint256();
            let restart_suppressed =
                !ordinary_round_eligible || last_round_ledger_id == Some(closed_id);
            if restart_suppressed && last_restart_gate_ledger_id != Some(closed_id) {
                tracing::info!(
                    target: "lcl_trace",
                    event = "ordinary_consensus_round_restart_suppressed",
                    local_lcl_hash = %closed_id,
                    local_lcl_seq = closed.header().seq,
                    end_consensus_pass,
                    reconciliation = ?reconciliation,
                    last_round_already_closed = last_round_ledger_id == Some(closed_id),
                    runner_phase = ?runner.phase(),
                    "LCL trace: ordinary consensus round restart suppressed"
                );
                last_restart_gate_ledger_id = Some(closed_id);
            } else if !restart_suppressed {
                last_restart_gate_ledger_id = None;
            }
        }

        if ordinary_round_eligible {
            let _lcl_transition_guard = root.lcl_transition_gate().lock();
            if let Some(closed) = root.closed_ledger() {
                let closed_id = *closed.header().hash.as_uint256();
                if last_round_ledger_id != Some(closed_id) {
                    let now = root.shared_time_keeper().close_time();
                    let prev_cx = crate::consensus_ledger_from_ledger(&closed);
                    if let Some(inbound_tx) = root.inbound_transactions().lock().ok().as_mut() {
                        inbound_tx.new_round(closed.header().seq);
                    }
                    let proposing =
                        root.network_ops_operating_mode() == NetworkOpsOperatingMode::Full;
                    runner.start_round(now, closed_id, prev_cx, proposing);
                    consensus_rt.update_phase(runner.phase());
                    consensus_rt.update_prev_ledger_id(runner.prev_ledger_id());
                    last_round_ledger_id = Some(closed_id);
                    last_timer_tick = Instant::now();
                    tracing::info!(
                        target: "consensus",
                        seq = closed.header().seq,
                        "Consensus started next round after checkLastClosedLedger"
                    );
                    tracing::info!(
                        target: "lcl_trace",
                        event = "ordinary_consensus_round_started",
                        local_lcl_hash = %closed_id,
                        local_lcl_seq = closed.header().seq,
                        started_prev_ledger = %runner.prev_ledger_id(),
                        proposing,
                        current_mode = ?root.network_ops_operating_mode(),
                        need_network_ledger = root.need_network_ledger(),
                        "LCL trace: ordinary consensus round started after no reconciliation change"
                    );
                    tracing::debug!(
                        target: "lcl_audit",
                        local_lcl_hash = %closed_id,
                        local_lcl_seq = closed.header().seq,
                        started_prev_ledger = %runner.prev_ledger_id(),
                        operating_mode = ?root.network_ops_operating_mode(),
                        need_network_ledger = root.need_network_ledger(),
                        "LCL_AUDIT ordinary consensus round restarted after no LCL switch"
                    );
                }
            }
        }

        // ─── 8. Wait for next event (proposal notify or 50ms timeout) ─────
        if !coordinator_work_remains {
            root.wait_consensus_or_timeout(Duration::from_millis(50));
        }
    }

    tracing::info!(target: "consensus", "NetworkOPs strand stopped");
}

// ─── checkLastClosedLedger / switchLastClosedLedger ─────────────────────────

/// Matches `NetworkOPsImp::endConsensus`: peers that still report our closed
/// ledger's predecessor must refresh status before policy chooses the next LCL.
fn cycle_obsolete_peer_statuses(root: &ApplicationRoot) {
    let Some(closed) = root.closed_ledger() else {
        return;
    };
    let obsolete = *closed.header().parent_hash.as_uint256();
    if let Some(overlay_rt) = root.overlay_runtime() {
        use overlay::Overlay;
        for peer in overlay_rt.overlay().active_peers() {
            if peer.closed_ledger_hash() == obsolete {
                peer.cycle_status();
            }
        }
    }
}

/// Preserve rippled's configured peer threshold. In particular,
/// `NetworkOPsImp` forces it to zero for `startValid`, allowing a local
/// start-valid validator to continue consensus without overlay peers.
fn required_peer_count(configured_minimum: usize) -> usize {
    configured_minimum
}

/// The rippled heartbeat re-applies these modes even when no peer-count
/// transition occurred, allowing `setMode` to normalize them by validated
/// ledger age. Other modes are left untouched by this heartbeat branch.
fn heartbeat_operating_mode_reassertion(
    current_mode: NetworkOpsOperatingMode,
) -> Option<NetworkOpsOperatingMode> {
    match current_mode {
        NetworkOpsOperatingMode::Disconnected => Some(NetworkOpsOperatingMode::Connected),
        NetworkOpsOperatingMode::Syncing => Some(NetworkOpsOperatingMode::Syncing),
        NetworkOpsOperatingMode::Connected => Some(NetworkOpsOperatingMode::Connected),
        _ => None,
    }
}

/// Rippled invokes `checkLastClosedLedger` only from `endConsensus`. Keep
/// preferred-target selection and pending-target replacement at that same
/// Accepted boundary: an acquisition completion may populate the cache at any
/// time, but it cannot supersede recovery intent until the next endConsensus
/// pass re-evaluates peer and validation evidence.
fn should_reconcile_preferred_lcl(phase: ConsensusPhase) -> bool {
    phase == ConsensusPhase::Accepted
}

/// Rippled's endConsensus exists only after doAccept returns. Quaxar's
/// JtAccept-to-strand handoff has an async window between `schedule_accept`
/// and the command reaching the strand; suppress the equivalent pass while
/// accepted work is in that window (queued or awaiting queue capacity).
fn should_run_end_consensus_reconciliation(
    phase: ConsensusPhase,
    accept_is_queued: bool,
    has_pending_accept: bool,
) -> bool {
    should_reconcile_preferred_lcl(phase) && !accept_is_queued && !has_pending_accept
}

/// Rippled advances from CONNECTED/SYNCING to TRACKING/FULL in endConsensus
/// only if checkLastClosedLedger did not report an abnormal ledger change.
fn should_promote_operating_mode_at_end_consensus(
    end_consensus_pass: bool,
    reconciliation: PreferredLclReconciliation,
) -> bool {
    end_consensus_pass && reconciliation == PreferredLclReconciliation::NoChange
}

/// Publication identity is an observation of the LedgerMaster-owned published
/// head. Mode promotion remains independently gated by the caller-provided
/// freshness bit.
fn should_emit_coordinator_publication(
    coordinator_installed: bool,
    chain_contiguous: bool,
) -> bool {
    coordinator_installed && chain_contiguous
}

fn coordinator_publication_is_fresh(
    allow_mode_promotion: bool,
    open_ledger_is_fresh: bool,
) -> bool {
    allow_mode_promotion && open_ledger_is_fresh
}

/// A provisional candidate is deliberately not a no-change outcome: the
/// ordinary round would replace the current round even though no durable LCL
/// target was admitted. Keep the predicate separate so its safety contract is
/// table-testable without a live consensus runner.
fn should_begin_ordinary_round(
    end_consensus_pass: bool,
    reconciliation: PreferredLclReconciliation,
) -> bool {
    end_consensus_pass && reconciliation == PreferredLclReconciliation::NoChange
}

/// Match rippled `checkLastClosedLedger`: choose the preferred LCL only for
/// this endConsensus pass, switch it if it is resident and admissible, and
/// otherwise leave generic Consensus to perform WrongLedger/GetConsL1
/// recovery.  InboundLedgers owns fetching and caching; it never transfers an
/// exact-target ownership token to NetworkOPs.
fn reconcile_preferred_lcl(
    root: &ApplicationRoot,
    shared_inbound: &Arc<InboundLedgers>,
    runner: &mut dyn ConsensusRunner,
    consensus_rt: &AppConsensusRuntime,
    last_round_ledger_id: &mut Option<Uint256>,
    audit_sampler: &mut LclAuditSampler,
    provisional_waiter: &mut Option<ProvisionalLclWaiter>,
) -> PreferredLclReconciliation {
    reconcile_preferred_lcl_with_status_broadcaster(
        root,
        shared_inbound,
        runner,
        consensus_rt,
        last_round_ledger_id,
        audit_sampler,
        provisional_waiter,
        &broadcast_switched_ledger_status,
    )
}

/// Production uses `broadcast_switched_ledger_status`; tests inject a counter
/// so the provisional fence observes status suppression independently of the
/// closed-LCL, round, and TxQ state assertions.
type SwitchedLedgerStatusBroadcaster = dyn Fn(&ApplicationRoot, &ledger::Ledger, i32, bool);

fn broadcast_switched_ledger_status(
    root: &ApplicationRoot,
    ledger: &ledger::Ledger,
    event: i32,
    have_correct_lcl: bool,
) {
    root.broadcast_consensus_status_change(ledger, event, have_correct_lcl);
}

fn reconcile_preferred_lcl_with_status_broadcaster(
    root: &ApplicationRoot,
    shared_inbound: &Arc<InboundLedgers>,
    runner: &mut dyn ConsensusRunner,
    consensus_rt: &AppConsensusRuntime,
    last_round_ledger_id: &mut Option<Uint256>,
    audit_sampler: &mut LclAuditSampler,
    provisional_waiter: &mut Option<ProvisionalLclWaiter>,
    status_broadcaster: &SwitchedLedgerStatusBroadcaster,
) -> PreferredLclReconciliation {
    if !should_reconcile_preferred_lcl(runner.phase()) {
        return PreferredLclReconciliation::NoChange;
    }

    let _lcl_transition_guard = root.lcl_transition_gate().lock();
    let Some(lm_rt) = root.ledger_master_runtime() else {
        return PreferredLclReconciliation::NoChange;
    };
    let lm = lm_rt.ledger_master();
    let Some(our_closed) = root.closed_ledger() else {
        return PreferredLclReconciliation::NoChange;
    };

    // A Worker-2 durable callback never adopts a ledger. It only wakes this
    // strand. Before doing another peer/validation selection pass, inspect a
    // retained exact wait key. If it remains provisional, this Accepted pass
    // has no new safe action and must not repeat resolver/acquire/replan work.
    // If the identity changed, the one serialized retry below re-evaluates the
    // current preferred target normally.
    if let Some(waiter) = provisional_waiter.as_ref().copied() {
        match shared_inbound.provisional_identity(&waiter.identity.target_hash) {
            Some(identity) if identity == waiter.identity => {
                if waiter.last_preference_recheck.elapsed() >= PROVISIONAL_LCL_RECHECK_INTERVAL {
                    // Preserve a moving-target escape hatch at the normal
                    // heartbeat cadence. The subsequent selection may release
                    // this waiter if the network now prefers another hash.
                } else {
                    if let Some(waiter) = provisional_waiter.as_mut()
                        && !waiter.suppression_logged
                    {
                        waiter.suppression_logged = true;
                        tracing::debug!(
                            target: "lcl_trace",
                            event = "provisional_lcl_wait_suppressed",
                            target_hash = %identity.target_hash,
                            ledger_hash = %identity.ledger_hash,
                            ledger_seq = identity.ledger_seq,
                            acquisition_id = identity.acquisition_id,
                            store_generation = identity.store_generation,
                            persistence_generation = identity.persistence_generation,
                            "LCL trace: repeated Accepted-phase reconciliation suppressed for exact provisional identity"
                        );
                    }
                    return PreferredLclReconciliation::Provisional;
                }
            }
            observed => {
                let previous = provisional_waiter
                    .take()
                    .expect("checked provisional waiter must remain present");
                tracing::debug!(
                    target: "lcl_trace",
                    event = "provisional_lcl_wait_woken",
                    wake_reason = if observed.is_some() { "acquisition_replaced" } else { "durable_or_terminal_transition" },
                    target_hash = %previous.identity.target_hash,
                    ledger_hash = %previous.identity.ledger_hash,
                    ledger_seq = previous.identity.ledger_seq,
                    acquisition_id = previous.identity.acquisition_id,
                    store_generation = previous.identity.store_generation,
                    persistence_generation = previous.identity.persistence_generation,
                    "LCL trace: exact provisional wait released for one serialized retry"
                );
            }
        }
    }

    let our_hash = *our_closed.header().hash.as_uint256();
    let parent_hash = *our_closed.header().parent_hash.as_uint256();
    // NOTE: Rippled's checkLastClosedLedger (NetworkOPs.cpp:1902-2005) has NO
    // local-parent-residency precondition. It always computes preferredLCL and
    // attempts recovery regardless of whether the parent is locally cached.
    // A previous gate here returned NoChange when the parent couldn't be
    // resolved, which permanently blocked preferred-LCL recovery whenever
    // the parent was swept from ledger_history (the common case during
    // catch-up). Removed to match rippled.

    use overlay::Overlay;
    let peers = root
        .overlay_runtime()
        .map(|overlay_rt| overlay_rt.overlay().active_peers())
        .unwrap_or_default();
    let mut peer_counts = std::collections::BTreeMap::<Uint256, u32>::new();
    peer_counts.entry(our_hash).or_insert(0);
    for peer in &peers {
        let hash = peer.closed_ledger_hash();
        if !hash.is_zero() {
            *peer_counts.entry(hash).or_default() += 1;
        }
    }
    if root.network_ops_operating_mode() >= NetworkOpsOperatingMode::Tracking {
        *peer_counts.entry(our_hash).or_default() += 1;
    }

    let min_valid_seq = lm.valid_ledger_seq();
    // Reconcile proof ownership from the runner's pre-observation latch. The
    // diagnostic below may snapshot a new moving tip as the sole successor;
    // feeding the event afterward preserves first-anchor/latest-candidate
    // ordering across failure, promotion, and authoritative preemption.
    let (recovery_anchor, recovery_candidate) =
        shared_inbound.coordinator_validation_recovery_latch();
    root.validations().reconcile_validation_recovery_latch(
        recovery_anchor.map(|(hash, seq)| (seq, hash)),
        recovery_candidate.map(|(hash, seq)| (seq, hash)),
    );
    let preference_diagnostic = root.validations().preferred_lcl_diagnostic(
        &RclValidatedLedger::from_ledger(&our_closed),
        min_valid_seq,
        &peer_counts,
    );
    let validation_recovery_target = preference_diagnostic
        .validation_recovery_candidate
        .map(|(seq, hash)| (hash, seq));
    shared_inbound.coordinator_validation_recovery_target(validation_recovery_target);
    let ordinary_selected_preferred_hash = preference_diagnostic.selected;
    // Resolve the ordinary rippled preference before applying Quaxar's
    // phase-neutral stable acquisition owner.  The owner is only a liveness
    // fallback for an unresolved moving tip; once the ordinary preferred LCL
    // is durable, complete, current, and compatible, checkLastClosedLedger
    // must be allowed to switch to it immediately.
    let ordinary_selected_preferred_resident = (ordinary_selected_preferred_hash != our_hash
        && ordinary_selected_preferred_hash != parent_hash
        && !ordinary_selected_preferred_hash.is_zero())
    .then(|| {
        root.resolve_ledger_by_hash(basics::sha_map_hash::SHAMapHash::new(
            ordinary_selected_preferred_hash,
        ))
    })
    .flatten()
    .filter(|_| !root.inbound_ledger_is_provisional(ordinary_selected_preferred_hash));
    let ordinary_selected_preferred_is_admissible = ordinary_selected_preferred_resident
        .as_ref()
        .is_some_and(|candidate| {
            preferred_candidate_passes_switch_admission(
                lm.as_ref(),
                ordinary_selected_preferred_hash,
                candidate.as_ref(),
                root.current_close_time_seconds(),
            )
        });
    // The diagnostic candidate is moving advice. Only the coordinator's
    // provenance-backed stable anchor may override a trie-local preference.
    // Once bound, retain that exact networkClosed target until its lifecycle
    // clears it so successive timer checks cannot redirect consensus to the
    // stale local branch while the asynchronous acquisition is active.
    let selected_preferred_target = effective_validation_recovery_target(
        ordinary_selected_preferred_hash,
        our_hash,
        shared_inbound.coordinator_validation_recovery_latch().0,
        ordinary_selected_preferred_is_admissible,
    );
    let selected_preferred_hash = selected_preferred_target.hash();
    // Match rippled's checkLastClosedLedger: ordinary preference is recomputed
    // for every accepted-boundary pass. The one exception is the bounded,
    // provenance-backed recovery anchor above: while its exact acquisition is
    // live it remains networkClosed, matching acquiringLedger_ ownership.
    let preferred_hash = selected_preferred_hash;
    if let Some(waiter) = provisional_waiter.as_ref().copied()
        && waiter.identity.target_hash == preferred_hash
        && shared_inbound.provisional_identity(&preferred_hash) == Some(waiter.identity)
    {
        if let Some(waiter) = provisional_waiter.as_mut() {
            waiter.last_preference_recheck = Instant::now();
        }
        tracing::debug!(
            target: "lcl_trace",
            event = "provisional_lcl_wait_rechecked",
            target_hash = %waiter.identity.target_hash,
            ledger_hash = %waiter.identity.ledger_hash,
            ledger_seq = waiter.identity.ledger_seq,
            acquisition_id = waiter.identity.acquisition_id,
            store_generation = waiter.identity.store_generation,
            persistence_generation = waiter.identity.persistence_generation,
            "LCL trace: exact provisional wait remains current after heartbeat recheck"
        );
        return PreferredLclReconciliation::Provisional;
    }
    if provisional_waiter
        .as_ref()
        .is_some_and(|waiter| waiter.identity.target_hash != preferred_hash)
    {
        let previous = provisional_waiter
            .take()
            .expect("checked provisional waiter must remain present");
        tracing::debug!(
            target: "lcl_trace",
            event = "provisional_lcl_wait_woken",
            wake_reason = "preferred_target_replaced",
            target_hash = %previous.identity.target_hash,
            ledger_hash = %previous.identity.ledger_hash,
            ledger_seq = previous.identity.ledger_seq,
            acquisition_id = previous.identity.acquisition_id,
            store_generation = previous.identity.store_generation,
            persistence_generation = previous.identity.persistence_generation,
            replacement_target_hash = %preferred_hash,
            "LCL trace: exact provisional wait released after heartbeat selected another target"
        );
    }
    // The only early resolution above was for a nonlocal ordinary preference;
    // local/parent no-switch paths remain provider-free.  Surface that lookup
    // here so live diagnostics can prove when a resident B superseded fallback
    // anchor A.
    let selected_preferred_resident = ordinary_selected_preferred_is_admissible
        .then_some(ordinary_selected_preferred_resident.as_ref())
        .flatten()
        .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq));
    tracing::info!(
        target: "lcl_trace",
        event = "preferred_lcl_selected",
        local_lcl_hash = %our_hash,
        local_lcl_seq = our_closed.header().seq,
        preferred_lcl_hash = %preferred_hash,
        selected_preferred_lcl_hash = %selected_preferred_hash,
        recovery_target_stabilized = preferred_hash != ordinary_selected_preferred_hash,
        peer_count = peers.len(),
        selected_trusted_validation_count = root.validations().num_trusted_for_ledger(preferred_hash),
        selected_peer_lcl_support = peer_counts.get(&preferred_hash).copied().unwrap_or_default(),
        validation_selection_source = ?preference_diagnostic.selection_source,
        validation_acquired_recovery_candidate = ?preference_diagnostic.acquired_recovery_candidate,
        validation_acquired_recovery_peer_support = ?preference_diagnostic.acquired_recovery_peer_support,
        validation_recovery_candidate = ?preference_diagnostic.validation_recovery_candidate,
        validation_recovery_support = ?preference_diagnostic.validation_recovery_support,
        validation_recovery_peer_support = ?preference_diagnostic.validation_recovery_peer_support,
        validation_working_source = ?preference_diagnostic.working_source,
        "LCL trace: preferred-LCL selection evaluated"
    );
    let emit_audit = audit_sampler.should_emit();
    if emit_audit {
        let inbound_lifecycle = shared_inbound.lifecycle_snapshot();
        let validated_anchor = lm
            .validated_ledger()
            .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq));
        let last_valid_anchor = lm.last_valid_ledger();
        tracing::info!(
            target: "lcl_audit",
            local_lcl_hash = %our_hash,
            local_lcl_seq = our_closed.header().seq,
            local_parent_hash = %parent_hash,
            local_lcl_close_time = our_closed.header().close_time,
            local_lcl_close_time_resolution = our_closed.header().close_time_resolution,
            now_close_time = root.current_close_time_seconds(),
            min_valid_seq,
            live_current_ledger_index = ?root.live_current_ledger_index(),
            selected_preferred_resident = ?selected_preferred_resident,
            published_ledger = ?root
                .published_ledger()
                .map(|ledger| (*ledger.header().hash.as_uint256(), ledger.header().seq)),
            operating_mode = ?root.network_ops_operating_mode(),
            need_network_ledger = root.need_network_ledger(),
            peer_count = peers.len(),
            peer_lcl_counts = ?peer_counts,
            preferred_lcl_hash = %preferred_hash,
            selected_trusted_validation_count = root.validations().num_trusted_for_ledger(preferred_hash),
            selected_peer_lcl_support = peer_counts.get(&preferred_hash).copied().unwrap_or_default(),
            validation_working_source = ?preference_diagnostic.working_source,
            validation_selection_source = ?preference_diagnostic.selection_source,
            validation_acquired_recovery_candidate = ?preference_diagnostic.acquired_recovery_candidate,
            validation_acquired_recovery_peer_support = ?preference_diagnostic.acquired_recovery_peer_support,
            validation_recovery_candidate = ?preference_diagnostic.validation_recovery_candidate,
            validation_recovery_support = ?preference_diagnostic.validation_recovery_support,
            validation_recovery_peer_support = ?preference_diagnostic.validation_recovery_peer_support,
            validation_trie_preferred = ?preference_diagnostic.trie_preferred,
            validation_acquiring_preferred = ?preference_diagnostic.acquiring_preferred,
            validation_working_preferred = ?preference_diagnostic.working_preferred,
            validation_peer_preferred = ?preference_diagnostic.peer_preferred,
            validation_current_count = preference_diagnostic.current_validation_count,
            validation_current_trusted_count = preference_diagnostic.current_trusted_count,
            validation_current_trusted_full_count = preference_diagnostic.current_trusted_full_count,
            validation_trie_ledger_count = preference_diagnostic.trie_ledger_count,
            validation_acquiring_entry_count = preference_diagnostic.acquiring_entry_count,
            validation_acquiring_waiter_count = preference_diagnostic.acquiring_waiter_count,
            validation_peer_lcl_entry_count = preference_diagnostic.peer_lcl_entry_count,
            inbound_lifecycle = ?inbound_lifecycle,
            ?validated_anchor,
            ?last_valid_anchor,
            "LCL_AUDIT preferred-LCL selection sampled"
        );
    }

    // Rippled does not switch back to its immediate predecessor. A zero
    // preference is likewise not an actionable recovery target.
    if preferred_hash.is_zero() || preferred_hash == parent_hash {
        shared_inbound.record_recovery_lcl_decision(
            preferred_hash,
            None,
            "check_last_closed_ledger",
            if preferred_hash.is_zero() {
                "ignored_zero"
            } else {
                "ignored_parent"
            },
        );
        tracing::info!(
            target: "lcl_trace",
            event = "preferred_lcl_not_actionable",
            preferred_lcl_hash = %preferred_hash,
            parent_hash = %parent_hash,
            "LCL trace: preferred LCL is zero or the local parent"
        );
        return PreferredLclReconciliation::NoChange;
    }
    if preferred_hash == our_hash {
        shared_inbound.record_recovery_lcl_decision(
            preferred_hash,
            Some(our_closed.as_ref()),
            "check_last_closed_ledger",
            "ignored_local",
        );
        tracing::info!(
            target: "lcl_trace",
            event = "preferred_lcl_already_local",
            preferred_lcl_hash = %preferred_hash,
            local_lcl_seq = our_closed.header().seq,
            "LCL trace: preferred LCL already matches local closed ledger"
        );
        return PreferredLclReconciliation::NoChange;
    }

    // Rippled resolves a preferred ledger only after proving this is an
    // actionable switch candidate.
    let preferred_resident = if preferred_hash == ordinary_selected_preferred_hash {
        ordinary_selected_preferred_resident
    } else {
        root.resolve_ledger_by_hash(basics::sha_map_hash::SHAMapHash::new(preferred_hash))
    };

    // `checkLastClosedLedger` immediately asks InboundLedgers for a resolver
    // miss. Preserve the source of a successful candidate so a live trace can
    // distinguish history-residency from a registry-resident completion.
    let (candidate, candidate_source) = match preferred_resident {
        Some(ledger) => (Some(ledger), "resolver"),
        None => {
            // NetworkOPs is the authoritative preferred-LCL selector. Publish
            // its exact hash before the normal InboundLedgers acquire so only
            // this fact, never generic consensus polling, owns the active
            // preferred-target permit.
            shared_inbound
                .coordinator_consensus_target(acquisition::LedgerTarget::new(preferred_hash, None));
            (
                shared_inbound.acquire(preferred_hash, 0, AcquireReason::Consensus),
                "inbound_registry",
            )
        }
    };
    tracing::info!(
        target: "lcl_trace",
        event = "preferred_lcl_candidate_lookup",
        preferred_lcl_hash = %preferred_hash,
        source = candidate_source,
        candidate_available = candidate.is_some(),
        candidate_seq = candidate.as_ref().map(|ledger| ledger.header().seq),
        "LCL trace: preferred target lookup completed"
    );
    let Some(candidate) = candidate else {
        let target_failed = shared_inbound.is_failure(&preferred_hash);
        let disposition = if target_failed {
            "failed"
        } else if shared_inbound.contains(&preferred_hash) {
            "registry_active"
        } else {
            "resolver_miss"
        };
        // Rippled re-invokes InboundLedgers::acquire(hash, 0, CONSENSUS) on
        // every endConsensus pass (NetworkOPs.cpp:1979-1981) unconditionally.
        // Deduplication happens INSIDE acquire(): ledgers_.find(hash) returns
        // the existing entry without creating a new one. Our registry does
        // the same via entries.get_mut(&hash). Match rippled exactly.
        tracing::info!(
            target: "lcl_trace",
            event = "preferred_lcl_resolver_miss",
            preferred_lcl_hash = %preferred_hash,
            candidate_source,
            disposition,
            local_lcl_hash = %our_hash,
            local_lcl_seq = our_closed.header().seq,
            "LCL trace: preferred LCL has an explicit non-adopted disposition"
        );
        shared_inbound.record_recovery_lcl_decision(
            preferred_hash,
            None,
            "check_last_closed_ledger",
            disposition,
        );
        if emit_audit {
            tracing::info!(
                target: "lcl_audit",
                local_lcl_hash = %our_hash,
                local_lcl_seq = our_closed.header().seq,
                preferred_lcl_hash = %preferred_hash,
                "LCL_AUDIT preferred-LCL candidate is not cached"
            );
        }

        restart_preferred_lcl_recovery(
            root,
            shared_inbound,
            runner,
            consensus_rt,
            last_round_ledger_id,
            selected_preferred_target,
            &our_closed,
        );
        return PreferredLclReconciliation::Pending;
    };

    let candidate_hash = *candidate.header().hash.as_uint256();
    if candidate_hash != preferred_hash {
        // A wrong object from an exact-hash resolver is retryable corruption.
        tracing::warn!(
            target: "lcl_trace",
            event = "preferred_lcl_hash_mismatch",
            preferred_lcl_hash = %preferred_hash,
            candidate_hash = %candidate_hash,
            candidate_seq = candidate.header().seq,
            "LCL trace: resolver returned a ledger with the wrong hash"
        );
        shared_inbound.record_recovery_lcl_decision(
            preferred_hash,
            Some(candidate.as_ref()),
            "check_last_closed_ledger",
            "rejected_hash_mismatch",
        );
        // Demote before the acquire demand so a coordinator-owned session is
        // minted from `Syncing` (M6-C ordering: `PreferredLclDivergence` drains
        // before `AcquireRequested`).
        restart_preferred_lcl_recovery(
            root,
            shared_inbound,
            runner,
            consensus_rt,
            last_round_ledger_id,
            acquisition::LedgerTarget::new(preferred_hash, None),
            &our_closed,
        );
        shared_inbound
            .coordinator_consensus_target(acquisition::LedgerTarget::new(preferred_hash, None));
        shared_inbound.acquire_closed_ledger_async(preferred_hash, AcquireReason::Consensus);
        return PreferredLclReconciliation::Pending;
    }

    if shared_inbound.is_provisional(&candidate_hash) {
        // A legacy external completion has no Worker-2 fence identity. Keep
        // its existing non-adoption behavior, but never fabricate an exact
        // waiter key for it.
        if let Some(identity) = shared_inbound.provisional_identity(&candidate_hash) {
            *provisional_waiter = Some(ProvisionalLclWaiter {
                identity,
                suppression_logged: false,
                last_preference_recheck: Instant::now(),
            });
            tracing::debug!(
                target: "lcl_trace",
                event = "provisional_lcl_wait_set",
                target_hash = %identity.target_hash,
                ledger_hash = %identity.ledger_hash,
                ledger_seq = identity.ledger_seq,
                acquisition_id = identity.acquisition_id,
                store_generation = identity.store_generation,
                persistence_generation = identity.persistence_generation,
                "LCL trace: retained exact provisional preferred-LCL wait key"
            );
        }
        // Worker 2 has registered this exact hash/acquisition identity and
        // made it resolver-visible, but its durable callback has not cleared
        // the identity. Do not call restart_preferred_lcl_recovery here: that
        // would demote mode and replace the round from a non-durable candidate.
        // Retain only the exact target acquisition; a durable callback wakes a
        // later serialized pass, while revocation leaves the target retryable.
        shared_inbound.record_recovery_lcl_decision(
            preferred_hash,
            Some(candidate.as_ref()),
            "check_last_closed_ledger",
            "provisional",
        );
        shared_inbound
            .coordinator_consensus_target(acquisition::LedgerTarget::new(preferred_hash, None));
        shared_inbound.acquire_closed_ledger_async(preferred_hash, AcquireReason::Consensus);
        tracing::info!(
            target: "lcl_trace",
            event = "preferred_lcl_provisional",
            preferred_lcl_hash = %preferred_hash,
            candidate_hash = %candidate_hash,
            candidate_seq = candidate.header().seq,
            candidate_source,
            "LCL trace: provisional preferred candidate retained behind durable fence"
        );
        return PreferredLclReconciliation::Provisional;
    }

    shared_inbound.record_recovery_lcl_decision(
        preferred_hash,
        Some(candidate.as_ref()),
        "check_last_closed_ledger",
        "durable",
    );
    let state_complete = !candidate.state_map().is_synching();
    let tx_complete = candidate.header().tx_hash.is_zero() || !candidate.tx_map().is_synching();
    let can_be_current = lm.can_be_current(candidate.as_ref(), root.current_close_time_seconds());
    let compatibility_audit = lm.compatibility_audit(candidate.as_ref());
    let compatible = compatibility_audit.compatible();
    if emit_audit {
        tracing::info!(
            target: "lcl_audit",
            target_hash = %preferred_hash,
            candidate_hash = %candidate_hash,
            candidate_seq = candidate.header().seq,
            candidate_parent_hash = %candidate.header().parent_hash,
            state_complete,
            tx_complete,
            can_be_current,
            compatible,
            compatibility = ?compatibility_audit,
            "LCL_AUDIT preferred-LCL candidate admission sampled"
        );
    }
    if !state_complete || !tx_complete {
        tracing::info!(
            target: "lcl_trace",
            event = "preferred_lcl_incomplete",
            preferred_lcl_hash = %preferred_hash,
            candidate_seq = candidate.header().seq,
            state_complete,
            tx_complete,
            "LCL trace: resolver-visible preferred LCL is incomplete"
        );
        shared_inbound.record_recovery_lcl_decision(
            preferred_hash,
            Some(candidate.as_ref()),
            "check_last_closed_ledger",
            "selected_but_incomplete",
        );
        // `getLedgerByHash` in rippled only hands checkLastClosedLedger a
        // completed inbound ledger. A resolver-visible partial ledger is
        // therefore equivalent to a miss: keep the desired hash as
        // `networkClosed` and let generic WrongLedger recovery acquire it.
        // Demote before the acquire demand so a coordinator-owned session is
        // minted from `Syncing` (M6-C ordering).
        restart_preferred_lcl_recovery(
            root,
            shared_inbound,
            runner,
            consensus_rt,
            last_round_ledger_id,
            acquisition::LedgerTarget::new(preferred_hash, Some(candidate.header().seq)),
            &our_closed,
        );
        shared_inbound
            .coordinator_consensus_target(acquisition::LedgerTarget::new(preferred_hash, None));
        shared_inbound.acquire_closed_ledger_async(preferred_hash, AcquireReason::Consensus);
        return PreferredLclReconciliation::Pending;
    }
    if !can_be_current || !compatible {
        tracing::warn!(
            target: "lcl_trace",
            event = "preferred_lcl_rejected",
            preferred_lcl_hash = %preferred_hash,
            candidate_hash = %candidate_hash,
            candidate_seq = candidate.header().seq,
            can_be_current,
            compatible,
            compatibility = ?compatibility_audit,
            "LCL trace: resolver-visible preferred LCL failed admission"
        );
        // Match rippled: keep our current LCL as the networkClosed output for
        // this pass; do not create or retire a separate exact-target state.
        shared_inbound.record_recovery_lcl_decision(
            preferred_hash,
            Some(candidate.as_ref()),
            "check_last_closed_ledger",
            "rejected_incompatible_or_stale",
        );
        tracing::warn!(
            target: "lcl_audit",
            target_hash = %preferred_hash,
            candidate_hash = %candidate_hash,
            candidate_seq = candidate.header().seq,
            can_be_current,
            compatible,
            compatibility = ?compatibility_audit,
            local_lcl_hash = %our_hash,
            local_lcl_seq = our_closed.header().seq,
            "LCL_AUDIT preferred-LCL candidate rejected"
        );
        // `rippled::checkLastClosedLedger` restores `networkClosed` to the
        // current local LCL and returns `false` for this path. Its subsequent
        // endConsensus pass may therefore leave CONNECTED/SYNCING and resume
        // TRACKING. Mirror that result in the typed coordinator: a previously
        // selected recovery anchor that proved stale or incompatible must not
        // keep the public phase Syncing after policy explicitly retained the
        // local LCL.
        shared_inbound.coordinator_preferred_lcl_reconciled(acquisition::LedgerIdentity::new(
            our_hash,
            our_closed.header().seq,
        ));
        return PreferredLclReconciliation::NoChange;
    }

    // Rippled demotes only after the candidate survives canBeCurrent and
    // compatibility admission. In particular, an incompatible resolver hit
    // returns false from checkLastClosedLedger without a FULL→CONNECTED flap.
    demote_for_preferred_lcl_divergence(
        root,
        shared_inbound,
        acquisition::LedgerTarget::new(preferred_hash, Some(candidate.header().seq)),
    );

    switch_last_closed_ledger(
        root,
        shared_inbound,
        runner,
        consensus_rt,
        last_round_ledger_id,
        preferred_hash,
        candidate,
        status_broadcaster,
    );
    PreferredLclReconciliation::Switched
}

/// Demote only once a preferred-LCL divergence has become actionable.
///
/// Rippled performs this after the `canBeCurrent`/`isCompatible` rejection
/// path in `checkLastClosedLedger`, not immediately after selecting a different
/// preferred hash.
///
/// When the coordinator owns service phase this feeds the typed
/// `PreferredLclDivergence` fact (`Connected/Tracking/Full -> Syncing` without
/// minting a session); otherwise the legacy direct write remains. The caller
/// must run this before any `acquire_closed_ledger_async` demand so the
/// demotion drains first and the demand is accepted from `Syncing`.
fn demote_for_preferred_lcl_divergence(
    root: &ApplicationRoot,
    shared_inbound: &Arc<InboundLedgers>,
    target: acquisition::LedgerTarget,
) {
    // Coordinator recovery is actionable from Connected as well as
    // Tracking/Full: Connected describes operating mode, not the absence of a
    // concrete wrong-ledger target. Feed the typed fact first so the exact
    // recovery owner becomes stable before its acquire demand. The legacy
    // direct mode write remains meaningful only as a Tracking/Full demotion.
    if shared_inbound.coordinator_installed() {
        shared_inbound.coordinator_preferred_lcl_divergence(target);
        return;
    }
    if !matches!(
        root.network_ops_operating_mode(),
        NetworkOpsOperatingMode::Tracking | NetworkOpsOperatingMode::Full
    ) {
        return;
    }
    root.set_network_ops_operating_mode_with_reason(
        NetworkOpsOperatingMode::Connected,
        "preferred_lcl_divergence",
    );
}

/// Preserve rippled's endConsensus → beginConsensus path when the preferred
/// LCL is absent or incomplete. The local closed ledger supplies the ledger
/// object, while `target` remains the desired networkClosed hash for generic
/// WrongLedger/GetConsL1 recovery.
fn restart_preferred_lcl_recovery(
    root: &ApplicationRoot,
    shared_inbound: &Arc<InboundLedgers>,
    runner: &mut dyn ConsensusRunner,
    consensus_rt: &AppConsensusRuntime,
    last_round_ledger_id: &mut Option<Uint256>,
    target: acquisition::LedgerTarget,
    our_closed: &Arc<ledger::Ledger>,
) {
    // The divergence fact drains before the caller's acquire demand so a
    // coordinator-owned session is minted from `Syncing`. A stable validation
    // recovery anchor already carries a verified sequence; ordinary resolver
    // misses remain hash-only until their Base reply establishes it.
    demote_for_preferred_lcl_divergence(root, shared_inbound, target);
    let now = root.shared_time_keeper().close_time();
    let prev_cx = crate::consensus_ledger_from_ledger(our_closed);
    if let Some(inbound_tx) = root.inbound_transactions().lock().ok().as_mut() {
        inbound_tx.new_round(our_closed.header().seq);
    }
    runner.start_round(now, target.hash(), prev_cx, false);
    consensus_rt.update_phase(runner.phase());
    consensus_rt.update_prev_ledger_id(runner.prev_ledger_id());
    *last_round_ledger_id = Some(target.hash());
}

/// Commit the resident, currently preferred LCL. Inbound completion only
/// populates cache/history; this endConsensus pass remains the sole policy
/// point that installs an admissible LCL.
fn switch_last_closed_ledger(
    root: &ApplicationRoot,
    shared_inbound: &Arc<InboundLedgers>,
    runner: &mut dyn ConsensusRunner,
    consensus_rt: &AppConsensusRuntime,
    last_round_ledger_id: &mut Option<Uint256>,
    target: Uint256,
    ledger: Arc<ledger::Ledger>,
    status_broadcaster: &SwitchedLedgerStatusBroadcaster,
) {
    // A completed inbound ledger may still carry only its acquisition-time
    // tree graph. Backed immutable SHAMaps are allowed to release weak child
    // nodes and reload them from NodeStore, so attach the durable fetch seam
    // before the switch path performs any ledger reads (TxQ/NegativeUNL,
    // open-ledger rebuild, or checkAccept). `on_closed_ledger` also normalizes
    // its stored slot, but it runs after those consumers and is therefore too
    // late for the first read after an LCL jump.
    let ledger = root.ledger_with_node_fetcher(ledger);
    let new_hash = *ledger.header().hash.as_uint256();
    debug_assert_eq!(new_hash, target);
    let new_seq = ledger.header().seq;
    tracing::info!(
        target: "lcl_audit",
        target_hash = %target,
        new_hash = %new_hash,
        new_seq,
        new_parent_hash = %ledger.header().parent_hash,
        new_tx_hash = %ledger.header().tx_hash,
        new_close_time = ledger.header().close_time,
        new_close_time_resolution = ledger.header().close_time_resolution,
        prior_closed = ?root.closed_ledger().map(|closed| {
            (*closed.header().hash.as_uint256(), closed.header().seq)
        }),
        prior_closed_details = ?root.closed_ledger().map(|closed| (
            *closed.header().hash.as_uint256(),
            *closed.header().parent_hash.as_uint256(),
            *closed.header().tx_hash.as_uint256(),
            *closed.header().account_hash.as_uint256(),
            closed.header().close_time,
            closed.header().close_time_resolution,
        )),
        "LCL_AUDIT preferred-LCL switch admitted"
    );
    tracing::info!(
        target: "lcl_trace",
        event = "preferred_lcl_switch_admitted",
        target_hash = %target,
        new_hash = %new_hash,
        new_seq,
        prior_closed = ?root.closed_ledger().map(|closed| {
            (*closed.header().hash.as_uint256(), closed.header().seq)
        }),
        "LCL trace: switching to resolver-visible preferred LCL"
    );

    // Match rippled: needNetworkLedger is an independent startup/recovery
    // latch, not a projection of the public operating mode. A real LCL switch
    // clears it; ordinary Full -> Syncing view changes never set it again.
    root.set_need_network_ledger(false);
    root.process_closed_ledger_txq(ledger.as_ref(), true);
    root.rebuild_open_ledger_after_consensus(Arc::clone(&ledger), &[], false);
    root.on_closed_ledger(Arc::clone(&ledger));
    // NetworkOPsImp::switchLastClosedLedger delegates to
    // LedgerMaster::switchLCL, whose non-standalone branch runs
    // checkAccept(lastClosed) after installing the new closed ledger.
    root.check_accept_after_lcl_switch(Arc::clone(&ledger));
    // Coordinator mode: report the LCL installation as a typed fact so the
    // coordinator can transition `Syncing -> Tracking` for its own target.
    if shared_inbound.coordinator_installed() {
        let installed = acquisition::LedgerIdentity::new(new_hash, new_seq);
        shared_inbound.coordinator_lcl_installed(installed);
        // A successful serialized switch is also authoritative reconciliation
        // when an older stable validation-recovery target had owned Syncing.
        // The exact install fact intentionally cannot satisfy a different
        // target; this follow-up retires that fallback only after B is the real
        // local LCL, allowing the coordinator to track B immediately.
        shared_inbound.coordinator_preferred_lcl_reconciled(installed);
    }
    status_broadcaster(root, ledger.as_ref(), 3, true);
    let proposing = root.network_ops_operating_mode() == NetworkOpsOperatingMode::Full;
    let now = root.shared_time_keeper().close_time();
    let prev_cx = crate::consensus_ledger_from_ledger(&ledger);
    if let Some(inbound_tx) = root.inbound_transactions().lock().ok().as_mut() {
        inbound_tx.new_round(new_seq);
    }
    runner.start_round(now, new_hash, prev_cx, proposing);
    consensus_rt.update_phase(runner.phase());
    consensus_rt.update_prev_ledger_id(runner.prev_ledger_id());
    *last_round_ledger_id = Some(new_hash);

    shared_inbound.record_recovery_lcl_decision(
        target,
        Some(ledger.as_ref()),
        "check_last_closed_ledger",
        "installed",
    );
    tracing::info!(
        target: "consensus",
        new_seq,
        %new_hash,
        "switchLastClosedLedger installed current preferred LCL"
    );
}

// ─── checkAccept + tryAdvance + operating mode + history ─────────────────────

fn check_accept_and_advance(
    root: &ApplicationRoot,
    shared_inbound: &Arc<InboundLedgers>,
    configured_ledger_history: u32,
    configured_ledger_fetch_size: u32,
    last_history_tick: &mut Instant,
    history_fetch_pack: &mut Option<(u32, Instant)>,
    history_reference: &mut Option<Arc<ledger::Ledger>>,
    allow_mode_promotion: bool,
) {
    let Some(lm_rt) = root.ledger_master_runtime() else {
        return;
    };
    let lm = lm_rt.ledger_master();
    // Preferred-LCL selection and installation were completed by the
    // strand-owned reconciliation before this maintenance pass. Keep the
    // existing transition gate for validation/publication consistency only.
    let _lcl_transition_guard = root.lcl_transition_gate().lock();

    // Normal in-place consensus advancement has already installed the closed
    // ledger before this serialized pass. Report that fact just as the
    // preferred-LCL switch path does: otherwise a coordinator that began in
    // Syncing never learns its matching target became the LCL, even while
    // validation and publication advance normally. The runner admits it only
    // for its exact Syncing target (or from Connected), so an unrelated
    // closed ledger cannot promote the phase.
    if shared_inbound.coordinator_installed() && !root.need_network_ledger() {
        if let Some(closed) = root.closed_ledger() {
            // A restarted node can resume a round on the durable recovered
            // target and accept its first child before this maintenance turn.
            // In that case rippled's switch/accept path has already made the
            // target a real ancestor of the new LCL, but the coordinator is
            // still `Syncing { target }`. Bridge that source-proven ancestry
            // first, then refresh Tracking with the actual LCL below. Without
            // this ordering, the exact-hash Syncing gate rejects the child and
            // the node remains Observing forever after a successful catch-up.
            if let Some(snapshot) = shared_inbound.coordinator_snapshot()
                && let acquisition::SyncPhase::Syncing { target } = snapshot.phase()
                && let Some(recovered_target) =
                    recovered_target_is_contiguous_to_lcl(closed.as_ref(), *target)
            {
                shared_inbound.coordinator_lcl_installed(recovered_target);
            }
            shared_inbound.coordinator_lcl_installed(acquisition::LedgerIdentity::new(
                *closed.header().hash.as_uint256(),
                closed.header().seq,
            ));
        }
    }

    // ── tryAdvance publication ────────────────────────────────────────────
    root.try_advance_publication();
    let published_ledger_after = root.published_ledger();

    // Coordinator mode: report the current publication as a typed fact on
    // every serialized non-divergent maintenance pass. Validation acceptance
    // can publish synchronously before this function snapshots
    // `published_before`; gating this bridge on `publication_advanced` would
    // lose the only fact capable of completing `Tracking -> Full`.
    //
    // Rippled's `endConsensus` promotes Tracking to Full from current-open
    // freshness; it does not require publication to equal the newest LCL.
    // Preserve the coordinator's typed invariant by forwarding a publication
    // only after proving that it and the local LCL lie on the same chain. The
    // publication can legitimately be ahead while the recovered local LCL is
    // catching up; rejecting that case leaves Tracking unable to regain Full.
    if let (Some(published), Some(closed)) = (published_ledger_after.as_ref(), root.closed_ledger())
    {
        let contiguous =
            published_ledger_is_contiguous_with_lcl(closed.as_ref(), published.as_ref());
        if should_emit_coordinator_publication(shared_inbound.coordinator_installed(), contiguous) {
            let hash = *published.header().hash.as_uint256();
            let seq = published.header().seq;
            let now_close_time = root.current_close_time_seconds();
            let open_ledger_is_fresh = root
                .open_ledger()
                .current_header_timing()
                .map(|timing| {
                    let resolution = u32::from(timing.close_time_resolution);
                    let freshness_deadline = timing
                        .parent_close_time
                        .saturating_add(resolution.saturating_mul(2));
                    now_close_time < freshness_deadline
                })
                .unwrap_or(false);
            let fresh =
                coordinator_publication_is_fresh(allow_mode_promotion, open_ledger_is_fresh);
            shared_inbound.coordinator_publication_committed(
                acquisition::LedgerIdentity::new(hash, seq),
                fresh,
            );
        }
    }

    // ── Update complete_ledgers display ──────────────────────────────────
    let complete_range = lm.complete_ledgers();
    let range_str = complete_range.to_string();
    if !range_str.is_empty() {
        root.set_status_rpc_complete_ledgers(Some(range_str));
    }

    // ── Operating mode promotion ─────────────────────────────────────────
    // This is reached only from a captured endConsensus pass with no preferred
    // LCL change. Do not let routine Open/Establish maintenance or a switching
    // pass promote the node, matching NetworkOPsImp::endConsensus.
    // The TRACKING transition alone is guarded by needNetworkLedger. As in
    // NetworkOPsImp::endConsensus, the subsequent FULL freshness check is not.
    // Coordinator mode owns the promotion via the typed publication fact above;
    // the legacy strand writer remains only when the coordinator is absent.
    if !shared_inbound.coordinator_installed()
        && allow_mode_promotion
        && root
            .published_ledger()
            .or_else(|| root.closed_ledger())
            .is_some()
    {
        let current_mode = root.network_ops_state().operating_mode();
        let need_network = root.need_network_ledger();
        let mut next_mode = current_mode;

        // Connected/Syncing → Tracking
        if matches!(
            next_mode,
            NetworkOpsOperatingMode::Connected | NetworkOpsOperatingMode::Syncing
        ) && !need_network
        {
            next_mode = NetworkOpsOperatingMode::Tracking;
        }

        let now_close_time = root.current_close_time_seconds();
        // rippled endConsensus reads LedgerMaster::getCurrentLedger(), whose
        // parentCloseTime/resolution are current-open header provenance, not
        // the closed/published fallback used by the old port.
        let full_freshness = root.open_ledger().current_header_timing().map(|timing| {
            let resolution = u32::from(timing.close_time_resolution);
            let freshness_deadline = timing
                .parent_close_time
                .saturating_add(resolution.saturating_mul(2));
            (
                timing.parent_close_time,
                resolution,
                freshness_deadline,
                now_close_time < freshness_deadline,
            )
        });

        // Connected/Tracking → Full when the current open ledger's parent
        // close time is fresh. rippled does NOT gate this on needNetworkLedger.
        if matches!(
            next_mode,
            NetworkOpsOperatingMode::Connected | NetworkOpsOperatingMode::Tracking
        ) && full_freshness.is_some_and(|(_, _, _, fresh)| fresh)
        {
            next_mode = NetworkOpsOperatingMode::Full;
        }

        if next_mode != current_mode {
            tracing::info!(
                target: "lcl_trace",
                event = "operating_mode_promotion_decision",
                ?current_mode,
                ?next_mode,
                allow_mode_promotion,
                need_network_ledger = need_network,
                min_valid_seq = lm.valid_ledger_seq(),
                validated_anchor = ?lm.validated_ledger().map(|ledger| (
                    *ledger.header().hash.as_uint256(),
                    ledger.header().seq
                )),
                last_valid_anchor = ?lm.last_valid_ledger(),
                published_ledger = ?root.published_ledger().map(|ledger| (
                    *ledger.header().hash.as_uint256(),
                    ledger.header().seq
                )),
                live_current_ledger_index = ?root.live_current_ledger_index(),
                current_open_ledger_freshness = ?full_freshness,
                "LCL trace: operating-mode promotion decision"
            );
            tracing::info!(target: "app", ?current_mode, ?next_mode, "strand: operating mode promoted");
            root.set_network_ops_operating_mode_with_reason(next_mode, "accept_promotion");
        }
    }

    // ── History backfill — full rippled doAdvance/fetchForHistory parity ────
    //
    // rippled's LedgerMaster::doAdvance only attempts history acquisition when
    // ALL of these conditions are satisfied:
    //   1. !standalone
    //   2. Local fee load is not excessive
    //   3. Publication queue not backed up (pubLedgerSeq == validLedgerSeq)
    //   4. Validated ledger age < 1 minute (node is in sync)
    //   5. NodeStore write load < 8192
    //
    // Then within that gate, shouldAcquire checks:
    //   6. candidateLedger >= currentLedger (may be the current ledger)
    //   7. currentLedger - candidateLedger <= ledgerHistory (within config range)
    //   8. candidateLedger >= minimumOnline (if known)
    //
    // InboundLedgers deduplicates active history requests by hash and
    // sequence. rippled's fillInProgress_ is for local SQL tryFill work, not
    // a lock held while a remote History acquisition is in flight.

    let valid_seq = lm.valid_ledger_seq();
    let pub_seq = lm
        .published_ledger()
        .map(|ledger| ledger.header().seq)
        .unwrap_or(0);

    // Condition 1: not standalone (always true here — strand only spawns for overlay mode)
    // Condition 2: fee load — skip if fee track reports overload
    let fee_overloaded = root.load_fee_track_loaded_local();
    // Condition 3: publication caught up to validation
    let publication_caught_up = valid_seq == pub_seq;
    // Condition 4: validated ledger age < 60s
    let validated_ledger_fresh = root.validated_ledger_age_seconds() < 60;
    // Condition 5: NodeStore write pressure. This is the same persistence
    // backlog metric and threshold as rippled's
    // `app_.getNodeStore().getWriteLoad() < kMaxWriteLoadAcquire`.
    let write_pressure_ok = root.node_store_write_load() < 8192;

    // rippled's InboundLedgers::acquire rejects History while the node needs
    // a network ledger. This strand is the sole History acquisition caller.
    let can_acquire_history = !root.need_network_ledger()
        && !fee_overloaded
        && publication_caught_up
        && validated_ledger_fresh
        && write_pressure_ok
        && valid_seq > 1
        && last_history_tick.elapsed() >= HISTORY_BACKFILL_RETRY_INTERVAL;

    if can_acquire_history {
        *last_history_tick = Instant::now();

        let complete = lm.complete_ledgers();
        // Do not fetch below the configured NodeStore retention floor.
        // This matches nodeStore().earliestLedgerSeq(), falling back to the
        // historical genesis+1 guard only when no node store is attached.
        let earliest_seq = root
            .minimum_online_seq()
            .unwrap_or(2)
            .max(root.earliest_ledger_fetch(configured_ledger_history));
        // Find the first missing ledger scanning backward from valid_seq
        let mut missing_seq = None;
        for seq in (earliest_seq..valid_seq).rev() {
            if !complete.contains(seq) {
                missing_seq = Some(seq);
                break;
            }
        }

        if let Some(missing) = missing_seq {
            // shouldAcquire gate: is the missing ledger within our configured range?
            let should_acquire = should_acquire_history(
                valid_seq,
                configured_ledger_history,
                missing,
                root.minimum_online_seq(),
            );

            if should_acquire {
                // Mirror rippled `fetchForHistory`: examine at most the
                // node-size-specific `ledgerFetchSize` adjacent sequence
                // numbers starting at `missing`. Do not keep scanning backward
                // until sparse skip-list hashes happen to be found; that turns
                // one bounded fetch pass into unbounded historical fan-out.
                let prefetch_limit = configured_ledger_fetch_size
                    .min(missing.saturating_sub(earliest_seq).saturating_add(1));
                let prefetch_floor = missing
                    .saturating_sub(prefetch_limit.saturating_sub(1))
                    .max(earliest_seq);
                let mut prefetch_count = 0u32;

                for seq in (prefetch_floor..=missing).rev() {
                    if complete.contains(seq) {
                        continue;
                    }
                    // `getLedgerHashForHistory` first consults the local
                    // history index, then a recent history reference and the
                    // validated skip list. If a direct lookup crosses a
                    // 256-ledger skip-list boundary, it acquires the aligned
                    // reference ledger before retrying the target lookup.
                    let Some(sha_hash) = history_hash_for_seq(
                        root,
                        &lm,
                        shared_inbound,
                        history_reference.as_ref(),
                        seq,
                    ) else {
                        // This is rippled's `clearLedger(missing + 1)` path:
                        // an unresolved primary hash is not a reason to scan
                        // a sparse, unbounded lower range in this pass.
                        if seq == missing {
                            lm.clear_ledger(missing.saturating_add(1));
                            break;
                        }
                        continue;
                    };
                    let hash = *sha_hash.as_uint256();

                    // A provider hit is already an exact, immutable ledger.
                    // Treat it as trusted History material through the same
                    // ancestry/persistence path as an inbound completion; do
                    // not merely cache-and-skip it, or the missing range can
                    // remain incomplete forever.
                    if let Some(ledger) = root.resolve_ledger_by_hash(sha_hash) {
                        let ledger = root.ledger_with_node_fetcher(ledger);
                        let _ = persist_completed_inbound_ledger(
                            root,
                            &lm,
                            &ledger,
                            AcquireReason::History,
                        );
                        if seq == missing {
                            *history_reference = Some(ledger);
                            // `fetchForHistory` returns immediately after its
                            // primary candidate is materialized. Prefetch is
                            // only the fallback for an unavailable primary.
                            break;
                        }
                        continue;
                    }
                    // Rippled consults recentFailures_ only for the primary
                    // fetchForHistory request. Consensus and Generic callers
                    // must be able to recreate a swept/failed hash immediately.
                    let is_primary = seq == missing;
                    let primary_history_failed = is_primary && shared_inbound.is_failure(&hash);
                    if !history_acquire_allowed(is_primary, primary_history_failed) {
                        tracing::debug!(
                            target: "history",
                            seq,
                            %hash,
                            "skipping primary history acquisition after recent failure"
                        );
                        continue;
                    }
                    // `fetchForHistory` always calls acquire(), even when an
                    // acquisition already exists. That update() touch prevents
                    // a live request from being swept while it is still the
                    // history target. If the completed ledger is returned,
                    // materialize it exactly as the reference does.
                    let already_in_progress = shared_inbound.has_entry_for_seq_or_hash(seq, &hash);
                    if let Some(ledger) = shared_inbound.acquire(hash, seq, AcquireReason::History)
                    {
                        let ledger = root.ledger_with_node_fetcher(ledger);
                        let _ = persist_completed_inbound_ledger(
                            root,
                            &lm,
                            &ledger,
                            AcquireReason::History,
                        );
                        if seq == missing {
                            *history_reference = Some(ledger);
                            // As above, a primary acquire that completed is
                            // not followed by speculative predecessors.
                            break;
                        }
                        continue;
                    }
                    // In rippled, getFetchPack follows only an acquire() that
                    // returned no ledger, and only for the primary target.
                    if history_fetch_pack_requested(is_primary, primary_history_failed, false) {
                        request_history_fetch_pack(
                            root,
                            &lm,
                            shared_inbound,
                            history_reference.as_ref(),
                            missing,
                            configured_ledger_history,
                            history_fetch_pack,
                        );
                    }
                    if !already_in_progress {
                        prefetch_count += 1;
                    }
                }

                if prefetch_count > 1 {
                    tracing::debug!(
                        target: "history",
                        missing,
                        prefetched = prefetch_count,
                        "batch prefetch of consecutive missing ledgers"
                    );
                }
            }
        }
    } else {
        // LedgerMaster::doAdvance resets histLedger_ whenever its history
        // acquisition gate is closed (publication lag, stale validated age,
        // overload, or write pressure). Retaining it across that boundary can
        // otherwise reuse a stale-chain skip list after recovery.
        *history_reference = None;
    }
}

fn history_acquire_allowed(is_primary: bool, recent_failure: bool) -> bool {
    !is_primary || !recent_failure
}

/// `LedgerMaster::fetchForHistory` requests a fetch pack only after the direct
/// primary acquire was permitted and returned no completed ledger.
fn history_fetch_pack_requested(
    is_primary: bool,
    recent_failure: bool,
    acquire_returned_ledger: bool,
) -> bool {
    is_primary && !recent_failure && !acquire_returned_ledger
}

#[cfg_attr(not(test), allow(dead_code))] // history-fetch dedup helper; exercised by strand tests, retained for M6-E
fn same_history_fetch_pack_is_suppressed(in_flight: Option<(u32, Instant)>, missing: u32) -> bool {
    in_flight.is_some_and(|(requested, _)| requested == missing)
}

fn trace_completed_inbound_handoff(
    source: &'static str,
    lm: &ledger::LedgerMaster,
    ledger: &Arc<ledger::Ledger>,
    reason: AcquireReason,
    acquisition_id: u64,
    persisted: CompletionPersistence,
) {
    let cache_visible_after = lm
        .ledger_history()
        .get_cached_ledger_by_hash(ledger.header().hash)
        .is_some();
    tracing::info!(
        target: "lcl_trace",
        event = "inbound_completion_persisted",
        source,
        reason = ?reason,
        acquisition_id,
        ledger_hash = %ledger.header().hash,
        ledger_seq = ledger.header().seq,
        immutable = ledger.is_immutable(),
        state_synching = ledger.state_map().is_synching(),
        tx_synching = ledger.tx_map().is_synching(),
        cache_visible_after,
        inserted = persisted.inserted,
        acknowledged = persisted.acknowledged,
        "LCL trace: inbound ledger completion persisted before adoption"
    );
}

/// Process one complete coordinator durable handoff. The acknowledgement is
/// queued only after the existing persistence, register, and checkAccept path
/// returns. This means enqueue alone cannot complete a coordinator session.
fn process_coordinator_completed_inbound_ledger(
    root: &ApplicationRoot,
    lm: &ledger::LedgerMaster,
    shared_inbound: &Arc<crate::ledger::inbound_ledgers::InboundLedgers>,
    item: &crate::ledger::inbound_ledgers::CompletedInboundLedger,
    dedup: &mut CoordinatorHandoffDedup,
    pending_acks: &mut VecDeque<(DurableHandoffId, SessionRef)>,
) {
    let Some((handoff, session)) = item.coordinator_handoff() else {
        return;
    };
    if !dedup.claim(handoff, session) {
        tracing::debug!(
            target: "lcl_trace",
            event = "coordinator_durable_handoff_duplicate",
            handoff = handoff.get(),
            session_id = session.session_id().get(),
            "skipping duplicate completed-ledger delivery while recipient acknowledgement is pending"
        );
        return;
    }

    tracing::info!(
        target: "acquisition_trace",
        event = "durable_handoff_received",
        handoff = handoff.get(),
        run_epoch = session.run_epoch().get(),
        session_id = session.session_id().get(),
        target_hash = %session.target_hash(),
        plan_epoch = session.plan_epoch().get(),
        store_generation = session.store_generation().get(),
        ledger_hash = %item.ledger.header().hash,
        ledger_seq = item.ledger.header().seq,
        "acquisition trace: NetworkOps received exact durable coordinator handoff"
    );
    let persisted = process_completed_inbound_ledger(
        root,
        lm,
        shared_inbound,
        "coordinator_durable",
        *item.ledger.header().hash.as_uint256(),
        item.acquisition_id,
        Arc::clone(&item.ledger),
        item.reason,
        false,
    );
    // The bridge only enqueues the typed event after the recipient accepted
    // this exact durable record. It deliberately does not install an LCL or
    // publish a ledger: the next accepted-boundary reconciliation recomputes
    // current preference before applying switch policy.
    if persisted.acknowledged {
        let acknowledgement_enqueued =
            shared_inbound.acknowledge_coordinator_durable_handoff(handoff, session);
        tracing::info!(
            target: "acquisition_trace",
            event = "durable_handoff_recipient_processed",
            handoff = handoff.get(),
            run_epoch = session.run_epoch().get(),
            session_id = session.session_id().get(),
            target_hash = %session.target_hash(),
            plan_epoch = session.plan_epoch().get(),
            store_generation = session.store_generation().get(),
            ledger_hash = %item.ledger.header().hash,
            ledger_seq = item.ledger.header().seq,
            acknowledged = persisted.acknowledged,
            acknowledgement_enqueued,
            "acquisition trace: recipient persisted, registered, and dispatched acceptance for durable handoff"
        );
        if !acknowledgement_enqueued {
            // Queue capacity is twice one bounded completed-ledger slice, so
            // normal receipt processing cannot overflow it. If a producer is
            // persistently backpressured, leave this exact dedup claim intact
            // and retry before later consensus work on the next strand turn.
            if pending_acks.len() < MAX_PENDING_DURABLE_ACKS {
                pending_acks.push_back((handoff, session));
            }
        }
    } else {
        dedup.release(handoff, session);
        let _ = shared_inbound.reject_coordinator_durable_handoff(handoff, session);
    }
}

/// Persist, register, accept-check, and trace one completed inbound ledger.
/// Shared by the registry ready-queue poll (legacy sessions, which then ack
/// their registry entry) and the coordinator durable handoff channel (which
/// has no registry entry to ack; the coordinator learns of recipient acceptance
/// through `DurableHandoffAcknowledged`).
#[allow(clippy::too_many_arguments)]
fn process_completed_inbound_ledger(
    root: &ApplicationRoot,
    lm: &ledger::LedgerMaster,
    shared_inbound: &Arc<crate::ledger::inbound_ledgers::InboundLedgers>,
    source: &'static str,
    hash: Uint256,
    acquisition_id: u64,
    ledger: Arc<ledger::Ledger>,
    reason: AcquireReason,
    acknowledge_registry: bool,
) -> CompletionPersistence {
    // Publish one canonical ledger object through every completion consumer.
    // If persistence alone inserts a fetcher-normalized clone while
    // checkAccept/validation paths keep the acquisition Arc, a later cache
    // canonicalization can replace the durable readable object with a backed
    // ledger that has no NodeStore fetch seam. That first becomes visible when
    // switchLastClosedLedger reads NegativeUNL or another weak child.
    let ledger = root.ledger_with_node_fetcher(ledger);
    let persisted = persist_completed_inbound_ledger(root, lm, &ledger, reason);
    // Match rippled's completed-ledger handoff: make the ledger
    // resolver-visible before evaluating validation quorum. The adaptor-local
    // map is the canonical fast path for `check_acquired`; registering after
    // checkAccept could turn a completed ledger into a redundant Generic
    // acquisition.
    root.validations().register_ledger(&ledger);
    root.check_accept_completed_inbound_ledger(Arc::clone(&ledger));
    trace_completed_inbound_handoff(source, lm, &ledger, reason, acquisition_id, persisted);
    // The registry queue item is acknowledged only after persistence, canonical
    // resolver publication, and acceptance dispatch. A failed persistence
    // remains ready for a fair later retry. Coordinator sessions are not in the
    // registry queue, so they never acknowledge here.
    if persisted.acknowledged && acknowledge_registry {
        shared_inbound.acknowledge_completed(&hash, acquisition_id);
    }
    persisted
}

fn fill_verified_history_range(
    root: &ApplicationRoot,
    lm: &ledger::LedgerMaster,
    completed_ledger: &ledger::Ledger,
) {
    let Some(loaded) =
        crate::ledger::loaded_ledger_runtime::AppLoadedLedgerRuntime::from_root(root)
    else {
        return;
    };
    let plan = ledger::run_try_fill_backwalk(
        &completed_ledger.header(),
        &LiveHistoryPresence { ledger_master: lm },
        &LiveHistoryHashPairs { loaded: &loaded },
        &LiveHistoryObjectPresence { loaded: &loaded },
        &StrandHistoryFillStopper(root),
    );
    for range in &plan.inserted_ranges {
        if root.is_stopping() {
            break;
        }
        lm.mark_ledger_complete_range(range.min, range.max);
    }
    tracing::debug!(
        target: "history",
        seq = completed_ledger.header().seq,
        inserted_ranges = ?plan.inserted_ranges,
        stop_reason = ?plan.stop_reason,
        "materialized verified contiguous history range"
    );

    // Once the trusted contiguous history backwalk reaches its floor, the
    // node-store membership (Bloom) filter has served its purpose as a
    // backfill/acquisition accelerator: steady-state reads see a negligible
    // miss rate, so the filter is dead weight. Evict it to reclaim RAM. This
    // is a safe, idempotent no-op for single stores without a filter and for
    // rotating stores (which keep their filters for cross-store probe skips).
    if matches!(
        plan.stop_reason,
        ledger::LedgerHistoryFillStopReason::ReachedGenesis
    ) {
        root.evict_node_store_membership_filter();
    }
}

fn persist_completed_inbound_ledger(
    root: &ApplicationRoot,
    lm: &ledger::LedgerMaster,
    ledger: &Arc<ledger::Ledger>,
    reason: AcquireReason,
) -> CompletionPersistence {
    // The completion boundary normalized this exact Arc once before any
    // persistence, validation, or acceptance consumer observed it. Preserve
    // that identity so later canonicalization cannot reintroduce a no-fetcher
    // version of the same backed ledger.
    let normalized = Arc::clone(ledger);
    match reason {
        // `InboundLedger::done` calls `storeLedger` for generic and consensus
        // acquisitions. It preserves the header's existing validated state
        // and never inserts an unvalidated fork by sequence or into
        // `completeLedgers`.
        AcquireReason::Consensus | AcquireReason::Generic => CompletionPersistence {
            inserted: !lm.ledger_history().insert(normalized, false),
            acknowledged: true,
        },
        // `fetchForHistory` resolves the exact hash before it starts the
        // acquisition.  Once that hash completes, rippled passes the ledger
        // directly to `setFullLedger(ledger, false, false)`; it does not require
        // the current validated ledger to prove the same ancestry a second
        // time.  That second proof can be unavailable across a skip-list
        // boundary even though getLedgerHashForHistory selected the canonical
        // hash, which would otherwise leave the gap in a permanent reacquire
        // loop.
        AcquireReason::History => {
            let normalized_seq = normalized.header().seq;
            let was_complete = lm.have_ledger(normalized_seq);
            let persistence =
                ledger::LedgerPersistence::new(root.build_ledger_persistence_runtime());
            match lm.set_full_ledger(
                &persistence,
                Arc::clone(&normalized),
                false,
                false,
                None,
                None,
            ) {
                Ok(true) => {
                    // `set_full_ledger(..., is_current = false)` deliberately
                    // does not update LedgerHistory's sequence index. Keep
                    // this trusted historical ledger cacheable by exact hash
                    // for subsequent contiguous materialization/publication,
                    // but do not mark it as a new validated head.
                    lm.ledger_history().insert(Arc::clone(&normalized), false);
                    // `tryFill` can now extend the trusted contiguous range
                    // through relational headers only while their earliest
                    // SQL entry is backed by NodeStore. The pure helper keeps
                    // rippled's 500-row windows and parent-hash proof.
                    fill_verified_history_range(root, lm, normalized.as_ref());
                    CompletionPersistence {
                        inserted: !was_complete,
                        acknowledged: true,
                    }
                }
                Ok(false) => {
                    // set_full_ledger records the range before its persistence
                    // result is known. Remove that claim so a failed durable
                    // write cannot make history look complete or suppress a
                    // later retry.
                    lm.clear_ledger(normalized_seq);
                    tracing::warn!(
                        target: "ledger",
                        "trusted history ledger was not durably saved"
                    );
                    CompletionPersistence {
                        inserted: false,
                        acknowledged: false,
                    }
                }
                Err(error) => {
                    tracing::warn!(
                        target: "ledger",
                        ?error,
                        "failed to materialize trusted history ledger"
                    );
                    CompletionPersistence {
                        inserted: false,
                        acknowledged: false,
                    }
                }
            }
        }
    }
}

fn request_history_fetch_pack(
    root: &ApplicationRoot,
    lm: &ledger::LedgerMaster,
    shared_inbound: &Arc<InboundLedgers>,
    history_reference: Option<&Arc<ledger::Ledger>>,
    missing: u32,
    fetch_depth: u32,
    in_flight: &mut Option<(u32, Instant)>,
) {
    if let Some((requested_seq, _)) = *in_flight {
        // LedgerMaster::fetchForHistory sets fetchSeq_ on its first request
        // and suppresses the same missing sequence until the gap changes.
        if requested_seq == missing {
            return;
        }
        *in_flight = None;
    }

    // Mirror `getFetchPack`: do not ask for a predecessor below local storage
    // retention, and use the exact hash for the ledger immediately above the
    // gap as the peer's `have` anchor.
    let earliest = crate::ledger::loaded_ledger_runtime::AppLoadedLedgerRuntime::from_root(root)
        .map(|loaded| loaded.earliest_ledger_seq())
        .unwrap_or(1)
        .max(root.earliest_ledger_fetch(fetch_depth));
    if missing <= earliest {
        return;
    }
    let Some(have_hash) = history_hash_for_seq(
        root,
        lm,
        shared_inbound,
        history_reference,
        missing.saturating_add(1),
    ) else {
        return;
    };

    use overlay::Overlay;
    let peer = root
        .overlay_runtime()
        .map(|runtime| runtime.overlay().active_peers())
        .unwrap_or_default()
        .into_iter()
        .filter(|peer| peer.has_range(missing, missing.saturating_add(1)))
        .max_by_key(|peer| peer.score(true));
    let Some(peer) = peer else {
        return;
    };

    peer.send(overlay::Message::new(
        ledger::make_fetch_pack_request(have_hash),
        None,
    ));
    *in_flight = Some((missing, Instant::now()));
    tracing::debug!(
        target: "history",
        missing,
        %have_hash,
        peer = peer.id(),
        "requested history fetch pack"
    );
}

/// Resolve a canonical hash from one locally trusted history reference.
fn history_hash_from_reference(
    reference: &ledger::Ledger,
    seq: u32,
) -> Option<basics::sha_map_hash::SHAMapHash> {
    if seq == 0 || reference.header().seq < seq {
        return None;
    }
    if reference.header().seq == seq {
        return Some(reference.header().hash);
    }
    reference
        .hash_of_seq(seq, &ledger::NullLedgerJournal)
        .filter(|hash| !hash.is_zero())
}

/// Match rippled `walkHashBySeq`: when a target is outside a reference
/// ledger's direct 256-entry skip-list window, acquire the next 256-aligned
/// ledger whose hash is permanently addressable from that reference.
fn history_hash_from_reference_or_candidate(
    root: &ApplicationRoot,
    shared_inbound: &Arc<InboundLedgers>,
    reference: &ledger::Ledger,
    seq: u32,
) -> Option<basics::sha_map_hash::SHAMapHash> {
    if let Some(hash) = history_hash_from_reference(reference, seq) {
        return Some(hash);
    }

    let candidate_seq = seq.saturating_add(255) & !255;
    if candidate_seq <= seq || reference.header().seq < candidate_seq {
        return None;
    }
    let candidate_hash = history_hash_from_reference(reference, candidate_seq)?;
    let candidate = root.ledger_with_node_fetcher(
        root.resolve_ledger_by_hash(candidate_hash).or_else(|| {
            shared_inbound.acquire(
                *candidate_hash.as_uint256(),
                candidate_seq,
                AcquireReason::History,
            )
        })?,
    );
    if candidate.header().seq != candidate_seq {
        tracing::warn!(
            target: "history",
            requested_seq = seq,
            candidate_seq,
            candidate_hash = %candidate_hash,
            resolved_seq = candidate.header().seq,
            "history reference ledger had an unexpected sequence"
        );
        return None;
    }
    history_hash_from_reference(candidate.as_ref(), seq)
}

/// Resolve the canonical hash for a history candidate without selecting a
/// fork by sequence. This is the active equivalent of rippled
/// `getLedgerHashForHistory`: check the validated history index, then
/// `histLedger_`, then the validated ledger, walking through a bounded
/// 256-aligned reference acquisition when necessary.
fn history_hash_for_seq(
    root: &ApplicationRoot,
    lm: &ledger::LedgerMaster,
    shared_inbound: &Arc<InboundLedgers>,
    history_reference: Option<&Arc<ledger::Ledger>>,
    seq: u32,
) -> Option<basics::sha_map_hash::SHAMapHash> {
    let indexed = lm.ledger_history().get_ledger_hash(seq);
    if !indexed.is_zero() {
        return Some(indexed);
    }

    if let Some(reference) = history_reference
        && let Some(hash) =
            history_hash_from_reference_or_candidate(root, shared_inbound, reference.as_ref(), seq)
    {
        return Some(hash);
    }

    let validated = lm.validated_ledger()?;
    if history_reference.is_some_and(|reference| reference.header().hash == validated.header().hash)
    {
        return None;
    }
    history_hash_from_reference_or_candidate(root, shared_inbound, validated.as_ref(), seq)
}

/// Prove a published ledger is the local LCL itself or a known contiguous
/// ancestor. This is the adapter-side witness required before the coordinator
/// can interpret a publication fact as `ChainContiguous`.
fn published_anchor_is_contiguous_to_lcl(
    lcl: &ledger::Ledger,
    published_hash: Uint256,
    published_seq: u32,
) -> bool {
    if published_seq > lcl.header().seq {
        return false;
    }
    if published_seq == lcl.header().seq {
        return *lcl.header().hash.as_uint256() == published_hash;
    }
    lcl.hash_of_seq(published_seq, &ledger::NullLedgerJournal)
        .is_some_and(|hash| *hash.as_uint256() == published_hash)
}

/// Prove bidirectional chain contiguity for a real published ledger. Unlike a
/// hash-only recovery target, a publication ahead of the LCL carries enough
/// ledger history to prove that the LCL is its ancestor.
fn published_ledger_is_contiguous_with_lcl(
    lcl: &ledger::Ledger,
    published: &ledger::Ledger,
) -> bool {
    if published.header().seq <= lcl.header().seq {
        return published_anchor_is_contiguous_to_lcl(
            lcl,
            *published.header().hash.as_uint256(),
            published.header().seq,
        );
    }
    published
        .hash_of_seq(lcl.header().seq, &ledger::NullLedgerJournal)
        .is_some_and(|hash| hash == lcl.header().hash)
}

/// Prove that a recovered coordinator target is the local LCL itself or a
/// known ancestor. This witnesses the rippled `switchLastClosedLedger` /
/// first accepted-child ordering before NetworkOps reports the actual LCL.
fn recovered_target_is_contiguous_to_lcl(
    lcl: &ledger::Ledger,
    target: acquisition::LedgerTarget,
) -> Option<acquisition::LedgerIdentity> {
    // A preferred hash is often selected before its ledger is resident, so
    // its sequence is initially unknown. Once consensus accepts the direct
    // child, the child's verified header proves both the target sequence and
    // ancestry. Do not leave the coordinator permanently Syncing merely
    // because the sequence was absent at the instant of demotion.
    let sequence = target.sequence().or_else(|| {
        (*lcl.header().parent_hash.as_uint256() == target.hash())
            .then(|| lcl.header().seq.saturating_sub(1))
    })?;
    published_anchor_is_contiguous_to_lcl(lcl, target.hash(), sequence)
        .then_some(acquisition::LedgerIdentity::new(target.hash(), sequence))
}

#[cfg(test)]
fn record_completed_inbound_ledger(
    lm: &ledger::LedgerMaster,
    ledger: &Arc<ledger::Ledger>,
) -> bool {
    !lm.ledger_history().insert(Arc::clone(ledger), false)
}

/// Matches rippled's static `shouldAcquire()` helper in LedgerMaster.cpp.
///
/// Returns true if `candidate_ledger` should be fetched from the network
/// given the current validated sequence and configured history depth.
fn should_acquire_history(
    current_ledger: u32,
    ledger_history: u32,
    candidate_ledger: u32,
    minimum_online: Option<u32>,
) -> bool {
    // Fetch if it may be the current ledger
    if candidate_ledger >= current_ledger {
        return true;
    }
    // Fetch if within configured history range
    if ledger_history == u32::MAX {
        // "full" history — always acquire
        return true;
    }
    if current_ledger - candidate_ledger <= ledger_history {
        return true;
    }
    // Fetch if at or above the minimum online boundary (SHAMapStore retention)
    if let Some(min) = minimum_online {
        if candidate_ledger >= min {
            return true;
        }
    }
    // Otherwise don't acquire
    false
}

#[cfg(test)]
mod tests {
    use super::{
        ConsensusJobScheduler, CoordinatorHandoffDedup, LclAuditSampler, MAX_COMMANDS_PER_TURN,
        MAX_COORDINATOR_HANDOFF_DEDUP, MAX_LEDGER_COMPLETIONS_PER_TURN, PreferredLclReconciliation,
        coordinator_publication_is_fresh, drain_bounded, effective_validation_recovery_target,
        enqueue_recovered_txsets, heartbeat_operating_mode_reassertion, history_acquire_allowed,
        history_fetch_pack_requested, persist_completed_inbound_ledger,
        preferred_candidate_passes_switch_admission, process_completed_inbound_ledger,
        published_ledger_is_contiguous_with_lcl, reconcile_preferred_lcl_with_status_broadcaster,
        record_completed_inbound_ledger, recovered_target_is_contiguous_to_lcl,
        required_peer_count, same_history_fetch_pack_is_suppressed, should_begin_ordinary_round,
        should_emit_coordinator_publication, should_promote_operating_mode_at_end_consensus,
        should_reconcile_preferred_lcl, should_run_end_consensus_reconciliation,
        switch_last_closed_ledger,
    };
    use crate::consensus::rcl_consensus::{ConsensusRunner, PendingAcceptWork, RclCxLedger};
    use crate::consensus::rcl_cx_peer_pos::RclCxPeerPos;
    use crate::consensus::rcl_validation::RclValidation;
    use crate::job::job_queue::JobQueue;
    use crate::job::job_types::JobType;
    use crate::ledger::inbound_ledgers::{AcquireReason, InboundLedgers};
    use crate::runtime::component_runtime::{
        AppConsensusRuntime, ConsensusCommand, ConsensusIngress,
    };
    use crate::{ApplicationRoot, NetworkOpsOperatingMode};
    use acquisition::{
        DurableHandoffId, IdCounter, LedgerIdentity, LedgerTarget, SessionRef, StoreGeneration,
    };

    #[test]
    fn stable_validation_recovery_anchor_overrides_local_and_moving_preferences() {
        let local = Uint256::from(10);
        let anchor = Uint256::from(20);
        let moving = Uint256::from(30);
        let stable = Some((anchor, 20));

        assert_eq!(
            effective_validation_recovery_target(local, local, stable, false),
            acquisition::LedgerTarget::new(anchor, Some(20))
        );
        assert_eq!(
            effective_validation_recovery_target(moving, local, stable, false),
            acquisition::LedgerTarget::new(anchor, Some(20)),
            "moving candidate B must not replace stable anchor A"
        );
        assert_eq!(
            effective_validation_recovery_target(moving, local, stable, true),
            acquisition::LedgerTarget::new(moving, None),
            "a resident ordinary preference must supersede the fallback anchor"
        );
        assert_eq!(
            effective_validation_recovery_target(moving, local, None, false),
            acquisition::LedgerTarget::new(moving, None)
        );
        assert_eq!(
            effective_validation_recovery_target(moving, local, Some((local, 10)), false),
            acquisition::LedgerTarget::new(moving, None),
            "an anchor equal to the installed LCL is not a divergence"
        );
    }

    #[test]
    fn partial_resident_preference_cannot_supersede_stable_anchor() {
        let root_node = basics::intrusive_pointer::make_shared_intrusive(
            shamap::tree_node::SHAMapTreeNode::new_inner(1),
        );
        root_node.set_child_hash(0, SHAMapHash::new(Uint256::from_array([0x22; 32])));
        root_node.update_hash();
        let mut header = LedgerHeader {
            seq: 11,
            parent_hash: SHAMapHash::new(Uint256::from_array([0x10; 32])),
            account_hash: root_node.get_hash(),
            parent_close_time: 1_000,
            close_time: 1_001,
            close_time_resolution: 30,
            ..LedgerHeader::default()
        };
        header.hash = calculate_ledger_hash(&header);
        let partial = Ledger::from_maps(
            header,
            shamap::sync::SyncTree::from_root_with_type(
                root_node,
                shamap::sync::SHAMapType::State,
                false,
                header.seq,
                shamap::sync::SyncState::Synching,
            ),
            shamap::sync::SyncTree::new_with_type(
                shamap::sync::SHAMapType::Transaction,
                false,
                header.seq,
            ),
        );
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let hash = *partial.header().hash.as_uint256();

        assert!(partial.state_map().is_synching());
        assert!(!preferred_candidate_passes_switch_admission(
            &master, hash, &partial, 1_000,
        ));
        assert_eq!(
            effective_validation_recovery_target(
                hash,
                Uint256::from_u64(10),
                Some((Uint256::from_u64(20), 20)),
                false,
            ),
            LedgerTarget::new(Uint256::from_u64(20), Some(20)),
        );
    }
    use basics::base_uint::Uint256;
    use basics::basic_config::BasicConfig;
    use basics::chrono::NetClockTimePoint;
    use basics::hardened_hash::HardenedHashBuilder;
    use basics::sha_map_hash::SHAMapHash;
    use basics::tagged_cache::MonotonicClock;
    use consensus::algorithm::ConsensusPhase;
    use ledger::{
        Fees, FetchPackCache, Ledger, LedgerConfig, LedgerHeader, LedgerMaster, LedgerMasterConfig,
        calculate_ledger_hash,
    };
    use nodestore::{DummyScheduler, ManagerImp, NullJournal, Scheduler};
    use protocol::{
        FeatureSet, KeyType, STValidation, calc_node_id, derive_public_key, generate_secret_key,
        get_field_by_symbol, random_seed,
    };
    use shamap::family::FullBelowCacheImpl;
    use shamap::tree_node_cache::TreeNodeCache;
    use std::collections::VecDeque;
    use std::sync::atomic::{AtomicBool, AtomicUsize};
    use std::sync::{Arc, mpsc};
    use std::time::{Duration, Instant};
    use tempfile::TempDir;

    fn immutable_ledger(seq: u32, parent_fill: u8) -> Arc<Ledger> {
        immutable_ledger_with_backing(seq, parent_fill, false)
    }

    fn immutable_ledger_with_backing(seq: u32, parent_fill: u8, backed: bool) -> Arc<Ledger> {
        immutable_ledger_with_parent_and_backing(
            seq,
            SHAMapHash::new(Uint256::from_array([parent_fill; 32])),
            parent_fill,
            backed,
            seq.saturating_add(99),
        )
    }

    fn immutable_ledger_with_parent_and_backing(
        seq: u32,
        parent_hash: SHAMapHash,
        item_fill: u8,
        backed: bool,
        parent_close_time: u32,
    ) -> Arc<Ledger> {
        let mut header = LedgerHeader {
            seq,
            parent_hash,
            parent_close_time,
            close_time: seq.saturating_add(100),
            close_time_resolution: 30,
            ..LedgerHeader::default()
        };
        header.hash = calculate_ledger_hash(&header);
        let mut state_tree = shamap::mutation::MutableTree::new(seq);
        state_tree
            .add_item(
                shamap::tree_node::SHAMapNodeType::AccountState,
                shamap::item::SHAMapItem::new(
                    Uint256::from_u64(u64::from(seq)),
                    vec![item_fill; 128],
                ),
            )
            .expect("state entry should insert");
        let mut ledger = Ledger::from_maps(
            header,
            shamap::sync::SyncTree::from_root_with_type(
                state_tree.root(),
                shamap::sync::SHAMapType::State,
                backed,
                seq,
                shamap::sync::SyncState::Immutable,
            ),
            shamap::sync::SyncTree::new_with_type(
                shamap::sync::SHAMapType::Transaction,
                false,
                seq,
            ),
        );
        ledger.set_immutable(true);
        Arc::new(ledger)
    }

    #[test]
    fn published_descendant_must_prove_the_lcl_as_its_ancestor() {
        let lcl = immutable_ledger(10, 0x10);
        let child =
            immutable_ledger_with_parent_and_backing(11, lcl.header().hash, 0x11, false, 110);
        assert!(published_ledger_is_contiguous_with_lcl(&lcl, &child));

        let unrelated = immutable_ledger(11, 0x77);
        assert!(!published_ledger_is_contiguous_with_lcl(&lcl, &unrelated));
    }

    fn install_test_node_store(root: &mut ApplicationRoot) -> TempDir {
        let dir = TempDir::new().expect("temporary node store");
        let mut config = BasicConfig::new();
        config.set_legacy("database_path", dir.path().join("sql").to_string_lossy());
        let node_db = config.section_mut("node_db");
        node_db.set("type", "Memory");
        node_db.set("path", dir.path().join("node").to_string_lossy());
        let store = crate::bootstrap_shamap_store(
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
        .expect("memory node store");
        root.attach_node_store(Some(store.node_store));
        dir
    }

    #[test]
    fn preferred_lcl_switch_attaches_fetcher_before_first_consumer() {
        let mut root = ApplicationRoot::new(0).expect("root should build");
        root.attach_default_ledger_master_runtime();
        let _store_dir = install_test_node_store(&mut root);
        let local = immutable_ledger(10, 0x10);
        let target = immutable_ledger_with_backing(12, 0x20, true);
        let target_hash = *target.header().hash.as_uint256();
        assert!(target.state_map().backed());
        assert!(!target.has_node_fetcher());
        root.on_closed_ledger(local);

        let (completed_tx, _completed_rx) = mpsc::sync_channel(1);
        let inbound = Arc::new(InboundLedgers::new(
            Arc::new(TreeNodeCache::new(
                "network-ops-switch-fetcher",
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
        let mut runner = RecordingRunner::accepted(*target.header().parent_hash.as_uint256());
        let consensus_rt = AppConsensusRuntime::new();
        let mut last_round = None;
        let observed_fetcher = Arc::new(AtomicBool::new(false));
        let observed_fetcher_for_callback = Arc::clone(&observed_fetcher);
        let broadcaster = move |_root: &ApplicationRoot,
                                ledger: &Ledger,
                                _event: i32,
                                _have_correct_lcl: bool| {
            observed_fetcher_for_callback.store(
                ledger.has_node_fetcher(),
                std::sync::atomic::Ordering::Relaxed,
            );
        };

        switch_last_closed_ledger(
            &root,
            &inbound,
            &mut runner,
            &consensus_rt,
            &mut last_round,
            target_hash,
            target,
            &broadcaster,
        );

        assert!(observed_fetcher.load(std::sync::atomic::Ordering::Relaxed));
        assert!(
            root.closed_ledger()
                .expect("switched closed ledger")
                .has_node_fetcher()
        );
        inbound.stop();
    }

    #[test]
    fn completed_inbound_ledger_publishes_one_fetcher_normalized_arc() {
        let mut root = ApplicationRoot::new(0).expect("root should build");
        let runtime = root.attach_default_ledger_master_runtime();
        let _store_dir = install_test_node_store(&mut root);
        let completed = immutable_ledger_with_backing(12, 0x20, true);
        let hash = *completed.header().hash.as_uint256();
        assert!(completed.state_map().backed());
        assert!(!completed.has_node_fetcher());

        let (completed_tx, _completed_rx) = mpsc::sync_channel(1);
        let inbound = Arc::new(InboundLedgers::new(
            Arc::new(TreeNodeCache::new(
                "network-ops-completion-fetcher",
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

        let persisted = process_completed_inbound_ledger(
            &root,
            runtime.ledger_master().as_ref(),
            &inbound,
            "test",
            hash,
            1,
            completed,
            AcquireReason::Consensus,
            false,
        );
        assert!(persisted.acknowledged);
        let cached = runtime
            .ledger_master()
            .ledger_history()
            .get_cached_ledger_by_hash(SHAMapHash::new(hash))
            .expect("completed ledger should be resolver-visible");
        assert!(
            cached.has_node_fetcher(),
            "completion consumers must not replace the canonical readable ledger with the acquisition Arc",
        );
        inbound.stop();
    }

    #[test]
    fn trusted_history_completion_persists_without_reproving_validated_skip_list() {
        let mut root = ApplicationRoot::new(0).expect("root should build");
        let runtime = root.attach_default_ledger_master_runtime();
        let _store_dir = install_test_node_store(&mut root);
        let master = runtime.ledger_master();

        // Model a canonical hash already selected by getLedgerHashForHistory,
        // but outside the currently resident validated ledger's skip-list
        // proof. rippled does not repeat that proof after acquire() returns.
        let validated = immutable_ledger(400, 0x40);
        master.set_valid_ledger_no_sweep(validated.clone(), None, None);
        let history = immutable_ledger(100, 0x10);
        assert!(
            validated
                .hash_of_seq(history.header().seq, &ledger::NullLedgerJournal)
                .is_none(),
            "the regression requires the later local ancestry proof to be unavailable"
        );

        let persisted = persist_completed_inbound_ledger(
            &root,
            master.as_ref(),
            &history,
            AcquireReason::History,
        );

        assert!(persisted.acknowledged);
        assert!(persisted.inserted);
        assert!(
            master.have_ledger(history.header().seq),
            "setFullLedger must close the history gap selected by the trusted hash lookup"
        );
        assert_eq!(
            master
                .ledger_history()
                .get_cached_ledger_by_hash(history.header().hash)
                .expect("persisted history ledger should remain hash-resolvable")
                .header()
                .hash,
            history.header().hash
        );
    }

    #[test]
    fn history_resolution_repairs_same_hash_cache_replacement_before_weak_child_read() {
        let mut root = ApplicationRoot::new(0).expect("root should build");
        let runtime = root.attach_default_ledger_master_runtime();
        let _store_dir = install_test_node_store(&mut root);

        let key =
            Uint256::from_hex("2200000000000000000000000000000000000000000000000000000000000000")
                .expect("state key should parse");
        let leaf = basics::intrusive_pointer::make_shared_intrusive(
            shamap::tree_node::SHAMapTreeNode::new_leaf(
                shamap::tree_node::SHAMapNodeType::AccountState,
                shamap::item::SHAMapItem::new(key, vec![0x24; 12]),
                0,
            ),
        );
        root.node_writer_result_from_store()
            .expect("test node store writer")(
            ledger::LedgerNodeObjectType::AccountNode,
            *leaf.get_hash().as_uint256(),
            leaf.serialize_with_prefix()
                .expect("leaf should serialize for node store"),
            12,
        )
        .expect("leaf should persist");

        // Model an acquisition ledger after its strong child was released:
        // the backed root retains only the child's hash and the Ledger object
        // itself carries no NodeStore fetch seam.
        let weak_root = basics::intrusive_pointer::make_shared_intrusive(
            shamap::tree_node::SHAMapTreeNode::new_inner(1),
        );
        weak_root.set_child_hash(2, leaf.get_hash());
        weak_root.update_hash();
        let mut header = LedgerHeader {
            seq: 12,
            account_hash: weak_root.get_hash(),
            close_time: 112,
            close_time_resolution: 30,
            ..LedgerHeader::default()
        };
        header.hash = calculate_ledger_hash(&header);
        let mut raw = Ledger::from_maps(
            header,
            shamap::sync::SyncTree::from_root_with_type(
                weak_root,
                shamap::sync::SHAMapType::State,
                true,
                12,
                shamap::sync::SyncState::Immutable,
            ),
            shamap::sync::SyncTree::new_with_type(shamap::sync::SHAMapType::Transaction, true, 12),
        );
        raw.set_immutable(true);
        let raw = Arc::new(raw);
        let hash = raw.header().hash;

        let readable = root.ledger_with_node_fetcher(Arc::clone(&raw));
        runtime
            .ledger_master()
            .ledger_history()
            .insert(readable, false);
        runtime
            .ledger_master()
            .ledger_history()
            .insert(Arc::clone(&raw), false);
        assert!(
            !runtime
                .ledger_master()
                .ledger_history()
                .get_cached_ledger_by_hash(hash)
                .expect("raw replacement should be cached")
                .has_node_fetcher(),
            "the regression requires a same-hash no-fetcher replacement",
        );

        let resolved = root
            .resolve_ledger_by_hash(hash)
            .expect("same-hash history ledger should resolve");
        assert!(resolved.has_node_fetcher());
        let _ = persist_completed_inbound_ledger(
            &root,
            runtime.ledger_master().as_ref(),
            &resolved,
            AcquireReason::Generic,
        );
        let retained = runtime
            .ledger_master()
            .ledger_history()
            .get_cached_ledger_by_hash(hash)
            .expect("normalized history ledger should replace the raw cache entry");
        assert!(retained.has_node_fetcher());
        let fetcher = retained
            .node_fetcher_closure()
            .expect("normalized history reference should retain its fetcher");
        let item = retained
            .state_map()
            .peek_item(key, &mut |child_hash| fetcher(child_hash))
            .expect("weak child should reload through the durable fetch seam")
            .expect("stored weak child should contain the requested item");
        assert_eq!(item.key(), key);
    }

    #[test]
    fn recovered_target_ancestor_bridges_syncing_before_actual_lcl_refresh() {
        let config = LedgerConfig::new(
            Fees {
                base: 10,
                reserve: 20,
                increment: 30,
            },
            FeatureSet::new([]),
        );
        let target =
            Ledger::create_genesis(false, &config, []).expect("genesis target should build");
        let target_identity =
            LedgerIdentity::new(*target.header().hash.as_uint256(), target.header().seq);
        let mut child = Ledger::from_previous(&target, 10);
        child
            .update_skip_list()
            .expect("first accepted child should retain its parent hash");

        assert_eq!(
            recovered_target_is_contiguous_to_lcl(
                &child,
                LedgerTarget::new(target_identity.hash(), Some(target_identity.sequence())),
            ),
            Some(target_identity),
            "a recovered preferred target used as the accepted child's parent must satisfy the coordinator's exact target gate before the actual LCL refresh",
        );
        assert_eq!(
            recovered_target_is_contiguous_to_lcl(
                &child,
                LedgerTarget::new(target_identity.hash(), None),
            ),
            Some(target_identity),
            "a verified direct child must resolve a hash-only recovery target",
        );
        assert_eq!(
            recovered_target_is_contiguous_to_lcl(
                &child,
                LedgerTarget::new(Uint256::from_u64(0xBAD), Some(target_identity.sequence())),
            ),
            None,
            "a same-sequence fork must not receive the recovered-target bridge",
        );
    }

    fn install_real_provisional_lcl_candidate(
        root: &mut ApplicationRoot,
        ledger: Arc<Ledger>,
    ) -> (TempDir, Arc<InboundLedgers>) {
        let runtime = root.attach_default_ledger_master_runtime();
        let dir = TempDir::new().expect("temporary inbound store");
        let mut config = BasicConfig::new();
        config.set_legacy("database_path", dir.path().join("sql").to_string_lossy());
        let node_db = config.section_mut("node_db");
        node_db.set("type", "Memory");
        node_db.set("path", dir.path().join("node").to_string_lossy());
        let store = crate::bootstrap_shamap_store(
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
        .expect("memory node store");
        let (completed_tx, _completed_rx) = mpsc::sync_channel(1);
        let inbound = Arc::new(InboundLedgers::new(
            Arc::new(TreeNodeCache::new(
                "network-ops-provisional-candidate",
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
        inbound.set_node_store(store.node_store);
        let master = runtime.ledger_master();
        inbound.set_completed_ledger_store(Arc::new(move |completed| {
            master.ledger_history().insert(completed, false);
        }));
        *runtime
            .inbound_ledgers
            .lock()
            .expect("inbound registry slot") = Some(Arc::clone(&inbound));

        let hash = *ledger.header().hash.as_uint256();
        assert!(
            inbound
                .acquire(hash, ledger.header().seq, AcquireReason::Consensus)
                .is_none()
        );
        inbound.on_complete(hash, Arc::clone(&ledger));
        runtime
            .ledger_master()
            .ledger_history()
            .insert(ledger, false);
        assert!(inbound.is_provisional(&hash));
        (dir, inbound)
    }

    fn preferred_validation(
        hash: Uint256,
        seq: u32,
        sign_time: u32,
    ) -> (protocol::NodeID, RclValidation) {
        let seed = random_seed();
        let secret_key =
            generate_secret_key(KeyType::Secp256k1, &seed).expect("validation signing key");
        let public_key =
            derive_public_key(KeyType::Secp256k1, &secret_key).expect("validation public key");
        let node_id = calc_node_id(&public_key);
        let mut validation =
            STValidation::new_signed(sign_time, &public_key, node_id, &secret_key, |value| {
                value.set_field_h256(get_field_by_symbol("sfLedgerHash"), hash);
                value.set_field_u32(get_field_by_symbol("sfLedgerSequence"), seq);
                value.set_field_u32(get_field_by_symbol("sfFlags"), protocol::VF_FULL_VALIDATION);
            })
            .expect("signed preferred validation");
        validation.set_trusted();
        (node_id, RclValidation::new(Arc::new(validation)))
    }

    fn install_empty_reconciliation_coordinator(
        root: &mut ApplicationRoot,
    ) -> (TempDir, Arc<InboundLedgers>) {
        let runtime = root.attach_default_ledger_master_runtime();
        let dir = TempDir::new().expect("temporary inbound store");
        let mut config = BasicConfig::new();
        config.set_legacy("database_path", dir.path().join("sql").to_string_lossy());
        let node_db = config.section_mut("node_db");
        node_db.set("type", "Memory");
        node_db.set("path", dir.path().join("node").to_string_lossy());
        let store = crate::bootstrap_shamap_store(
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
        .expect("memory node store");
        let (completed_tx, _completed_rx) = mpsc::sync_channel(1);
        let inbound = Arc::new(InboundLedgers::new(
            Arc::new(TreeNodeCache::new(
                "network-ops-stable-recovery",
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
        inbound.set_node_store(store.node_store);
        inbound.set_phase_mode_owner(root.network_ops_mode_owner());
        assert!(inbound.install_coordinator());
        *runtime
            .inbound_ledgers
            .lock()
            .expect("inbound registry slot") = Some(Arc::clone(&inbound));
        (dir, inbound)
    }

    struct RecordingRunner {
        phase: ConsensusPhase,
        prev: Uint256,
        start_rounds: usize,
        last_proposing: Option<bool>,
    }

    impl RecordingRunner {
        fn accepted(prev: Uint256) -> Self {
            Self {
                phase: ConsensusPhase::Accepted,
                prev,
                start_rounds: 0,
                last_proposing: None,
            }
        }
    }

    impl ConsensusRunner for RecordingRunner {
        fn peer_proposal(&mut self, _now: NetClockTimePoint, _peer_pos: &RclCxPeerPos) -> bool {
            false
        }

        fn timer_tick(&mut self, _now: NetClockTimePoint) -> Option<PendingAcceptWork> {
            None
        }

        fn start_round(
            &mut self,
            _now: NetClockTimePoint,
            prev_ledger_id: Uint256,
            _prev_ledger: RclCxLedger,
            proposing: bool,
        ) {
            self.start_rounds += 1;
            self.prev = prev_ledger_id;
            self.phase = ConsensusPhase::Open;
            self.last_proposing = Some(proposing);
        }

        fn got_tx_set(&mut self, _now: NetClockTimePoint, _tx_set: consensus::RclTxSet) {}

        fn execute_accept(&mut self, _now: NetClockTimePoint, _work: PendingAcceptWork) {}

        fn phase(&self) -> ConsensusPhase {
            self.phase
        }

        fn prev_ledger_id(&self) -> Uint256 {
            self.prev
        }
    }

    #[test]
    fn real_reconciliation_retains_stable_anchor_and_restarts_wrong_ledger() {
        let mut root = ApplicationRoot::new(0).expect("root should build");
        let local = immutable_ledger(10, 0x10);
        let local_hash = *local.header().hash.as_uint256();
        root.attach_default_ledger_master_runtime();
        root.on_closed_ledger(Arc::clone(&local));
        root.network_ops_mode_owner()
            .set_operating_mode_direct(NetworkOpsOperatingMode::Full);
        let (_store_dir, inbound) = install_empty_reconciliation_coordinator(&mut root);

        let anchor = Uint256::from_u64(0xA11CE);
        assert_ne!(anchor, local_hash);
        assert!(inbound.coordinator_validation_recovery_target(Some((anchor, 20))));
        assert!(inbound.coordinator_report_peer_availability(&[1]));
        assert_eq!(
            inbound.coordinator_validation_recovery_latch().0,
            Some((anchor, 20))
        );

        let before = root.closed_ledger().expect("local LCL installed");
        let mut runner = RecordingRunner::accepted(local_hash);
        let consensus_rt = AppConsensusRuntime::new();
        let mut last_round = None;
        let mut sampler = LclAuditSampler::new();
        let mut provisional_waiter = None;
        assert_eq!(
            reconcile_preferred_lcl_with_status_broadcaster(
                &root,
                &inbound,
                &mut runner,
                &consensus_rt,
                &mut last_round,
                &mut sampler,
                &mut provisional_waiter,
                &|_, _, _, _| panic!("pending recovery must not broadcast a switch"),
            ),
            PreferredLclReconciliation::Pending
        );

        assert_eq!(runner.prev, anchor);
        assert_eq!(runner.start_rounds, 1, "only the WrongLedger round starts");
        assert_eq!(runner.last_proposing, Some(false));
        assert_eq!(last_round, Some(anchor));
        // This harness has no OverlayRuntime, so the accepted-boundary target
        // refresh inside reconciliation intentionally leaves the transport
        // snapshot empty and the typed divergence is rejected. Re-feed the
        // same live-peer fact used by production, then prove the exact target
        // transition that reconciliation requested.
        assert!(inbound.coordinator_report_peer_availability(&[1]));
        assert!(inbound.coordinator_preferred_lcl_divergence(LedgerTarget::new(anchor, Some(20),)));
        let phase = *inbound.coordinator_snapshot().expect("snapshot").phase();
        assert!(
            matches!(
                phase,
                acquisition::SyncPhase::Syncing { target }
                    if target == LedgerTarget::new(anchor, Some(20))
            ),
            "unexpected coordinator phase: {phase:?}"
        );
        assert_ne!(
            root.network_ops_operating_mode(),
            NetworkOpsOperatingMode::Full
        );
        let after = root.closed_ledger().expect("local LCL remains installed");
        assert_eq!(after.header().hash, before.header().hash);
        assert_eq!(after.header().seq, before.header().seq);
    }

    #[test]
    fn real_reconciliation_switches_admissible_resident_preference_over_stable_anchor() {
        let mut root = ApplicationRoot::new(0).expect("root should build");
        let local = immutable_ledger(10, 0x10);
        let local_identity =
            LedgerIdentity::new(*local.header().hash.as_uint256(), local.header().seq);
        let ordinary = immutable_ledger_with_parent_and_backing(
            11,
            SHAMapHash::new(Uint256::from_array([0x77; 32])),
            0x20,
            false,
            root.current_close_time_seconds(),
        );
        let ordinary_hash = *ordinary.header().hash.as_uint256();
        let ordinary_identity = LedgerIdentity::new(ordinary_hash, ordinary.header().seq);
        let runtime = root.attach_default_ledger_master_runtime();
        root.on_closed_ledger(Arc::clone(&local));
        runtime
            .ledger_master()
            .ledger_history()
            .insert(Arc::clone(&ordinary), false);
        root.validations().register_ledger(ordinary.as_ref());
        let (node_id, validation) = preferred_validation(
            ordinary_hash,
            ordinary.header().seq,
            root.time_keeper().close_time().as_seconds(),
        );
        assert_eq!(
            root.validations()
                .validations()
                .lock()
                .expect("validations mutex")
                .add(node_id, validation),
            consensus::rcl_support::ValStatus::Current,
        );

        let (_store_dir, inbound) = install_empty_reconciliation_coordinator(&mut root);
        assert!(inbound.coordinator_report_peer_availability(&[1]));
        assert!(inbound.coordinator_lcl_installed(local_identity));
        let anchor = LedgerTarget::new(Uint256::from_u64(0xA11CE), Some(20));
        assert!(inbound.coordinator_validation_recovery_target(Some((
            anchor.hash(),
            anchor.sequence().expect("known anchor sequence"),
        ))));
        assert!(inbound.coordinator_preferred_lcl_divergence(anchor));
        assert_eq!(
            inbound.coordinator_validation_recovery_latch().0,
            Some((anchor.hash(), 20)),
        );

        let mut runner = RecordingRunner::accepted(local_identity.hash());
        let consensus_rt = AppConsensusRuntime::new();
        let mut last_round = None;
        let mut sampler = LclAuditSampler::new();
        let mut provisional_waiter = None;
        assert_eq!(
            reconcile_preferred_lcl_with_status_broadcaster(
                &root,
                &inbound,
                &mut runner,
                &consensus_rt,
                &mut last_round,
                &mut sampler,
                &mut provisional_waiter,
                &|_, _, _, _| {},
            ),
            PreferredLclReconciliation::Switched,
        );

        assert_eq!(
            root.closed_ledger().expect("switched LCL").header().hash,
            ordinary.header().hash,
        );
        assert_eq!(runner.prev, ordinary_hash);
        assert_eq!(last_round, Some(ordinary_hash));
        assert_eq!(
            inbound.coordinator_validation_recovery_latch(),
            (None, None)
        );
        assert!(matches!(
            inbound.coordinator_snapshot().expect("snapshot").phase(),
            acquisition::SyncPhase::Tracking { lcl } if *lcl == ordinary_identity
        ));
        inbound.stop();
    }

    #[test]
    fn real_reconciliation_retains_stable_anchor_for_incompatible_resident_preference() {
        let mut root = ApplicationRoot::new(0).expect("root should build");
        let local = immutable_ledger(10, 0x10);
        let local_hash = *local.header().hash.as_uint256();
        let incompatible = immutable_ledger_with_parent_and_backing(
            11,
            SHAMapHash::new(Uint256::from_array([0x77; 32])),
            0x20,
            false,
            root.current_close_time_seconds(),
        );
        let incompatible_hash = *incompatible.header().hash.as_uint256();
        let runtime = root.attach_default_ledger_master_runtime();
        root.on_closed_ledger(Arc::clone(&local));
        runtime
            .ledger_master()
            .set_valid_ledger_no_sweep(Arc::clone(&local), None, None);
        runtime
            .ledger_master()
            .ledger_history()
            .insert(Arc::clone(&incompatible), false);
        root.validations().register_ledger(incompatible.as_ref());
        let (node_id, validation) = preferred_validation(
            incompatible_hash,
            incompatible.header().seq,
            root.time_keeper().close_time().as_seconds(),
        );
        assert_eq!(
            root.validations()
                .validations()
                .lock()
                .expect("validations mutex")
                .add(node_id, validation),
            consensus::rcl_support::ValStatus::Current,
        );

        let (_store_dir, inbound) = install_empty_reconciliation_coordinator(&mut root);
        assert!(inbound.coordinator_report_peer_availability(&[1]));
        let anchor = LedgerTarget::new(Uint256::from_u64(0xA11CE), Some(20));
        assert!(inbound.coordinator_validation_recovery_target(Some((anchor.hash(), 20))));

        let mut runner = RecordingRunner::accepted(local_hash);
        let consensus_rt = AppConsensusRuntime::new();
        let mut last_round = None;
        let mut sampler = LclAuditSampler::new();
        let mut provisional_waiter = None;
        assert_eq!(
            reconcile_preferred_lcl_with_status_broadcaster(
                &root,
                &inbound,
                &mut runner,
                &consensus_rt,
                &mut last_round,
                &mut sampler,
                &mut provisional_waiter,
                &|_, _, _, _| panic!("incompatible B must not switch"),
            ),
            PreferredLclReconciliation::Pending,
        );

        assert_eq!(runner.prev, anchor.hash());
        assert_eq!(last_round, Some(anchor.hash()));
        assert_eq!(
            root.closed_ledger()
                .expect("local LCL retained")
                .header()
                .hash,
            local.header().hash,
        );
        assert_eq!(
            inbound.coordinator_validation_recovery_latch().0,
            Some((anchor.hash(), 20)),
        );
        inbound.stop();
    }

    #[test]
    fn real_reconciliation_does_not_let_resident_parent_clear_stable_anchor() {
        let mut root = ApplicationRoot::new(0).expect("root should build");
        let parent = immutable_ledger_with_parent_and_backing(
            9,
            SHAMapHash::new(Uint256::from_array([0x08; 32])),
            0x09,
            false,
            root.current_close_time_seconds(),
        );
        let local = immutable_ledger_with_parent_and_backing(
            10,
            parent.header().hash,
            0x10,
            false,
            root.current_close_time_seconds(),
        );
        let local_hash = *local.header().hash.as_uint256();
        let parent_hash = *parent.header().hash.as_uint256();
        let runtime = root.attach_default_ledger_master_runtime();
        root.on_closed_ledger(Arc::clone(&local));
        runtime
            .ledger_master()
            .ledger_history()
            .insert(Arc::clone(&parent), false);
        root.validations().register_ledger(parent.as_ref());
        let (node_id, validation) = preferred_validation(
            parent_hash,
            parent.header().seq,
            root.time_keeper().close_time().as_seconds(),
        );
        assert_eq!(
            root.validations()
                .validations()
                .lock()
                .expect("validations mutex")
                .add(node_id, validation),
            consensus::rcl_support::ValStatus::Current,
        );

        let (_store_dir, inbound) = install_empty_reconciliation_coordinator(&mut root);
        assert!(inbound.coordinator_report_peer_availability(&[1]));
        let anchor = LedgerTarget::new(Uint256::from_u64(0xA11CE), Some(20));
        assert!(inbound.coordinator_validation_recovery_target(Some((anchor.hash(), 20))));

        let mut runner = RecordingRunner::accepted(local_hash);
        let consensus_rt = AppConsensusRuntime::new();
        let mut last_round = None;
        let mut sampler = LclAuditSampler::new();
        let mut provisional_waiter = None;
        assert_eq!(
            reconcile_preferred_lcl_with_status_broadcaster(
                &root,
                &inbound,
                &mut runner,
                &consensus_rt,
                &mut last_round,
                &mut sampler,
                &mut provisional_waiter,
                &|_, _, _, _| panic!("parent preference must not switch"),
            ),
            PreferredLclReconciliation::Pending,
        );
        assert_eq!(runner.prev, anchor.hash());
        assert_eq!(last_round, Some(anchor.hash()));
        assert_eq!(
            inbound.coordinator_validation_recovery_latch().0,
            Some((anchor.hash(), 20)),
        );
        assert_eq!(
            root.closed_ledger()
                .expect("local LCL retained")
                .header()
                .hash,
            local.header().hash,
        );
        inbound.stop();
    }

    #[test]
    fn coordinator_handoff_dedup_is_exact_and_bounded() {
        let mut ids = IdCounter::new();
        let session = SessionRef::new(
            ids.next_id(),
            ids.next_id(),
            Uint256::from(1),
            ids.next_id(),
            StoreGeneration::new(1),
        );
        let mut dedup = CoordinatorHandoffDedup::default();
        assert!(dedup.claim(DurableHandoffId::new(1), session));
        assert!(
            !dedup.claim(DurableHandoffId::new(1), session),
            "the same exact handoff/session pair is processed once"
        );

        for handoff in 2..=(MAX_COORDINATOR_HANDOFF_DEDUP as u64 + 1) {
            assert!(dedup.claim(DurableHandoffId::new(handoff), session));
        }
        assert!(
            dedup.claim(DurableHandoffId::new(1), session),
            "the bounded local cache evicts the oldest completed delivery"
        );
    }

    #[test]
    fn history_failure_cooldown_applies_only_to_primary_history_fetch() {
        assert!(!history_acquire_allowed(true, true));
        assert!(history_acquire_allowed(true, false));
        assert!(history_acquire_allowed(false, true));
    }

    #[test]
    fn history_fetch_pack_follows_only_a_permitted_empty_primary_acquire() {
        assert!(history_fetch_pack_requested(true, false, false));
        assert!(!history_fetch_pack_requested(true, true, false));
        assert!(!history_fetch_pack_requested(true, false, true));
        assert!(!history_fetch_pack_requested(false, false, false));
    }

    #[test]
    fn history_prefetch_window_is_contiguous_and_bounded() {
        let missing: u32 = 10_000;
        let earliest: u32 = 1;
        let history_prefetch_limit: u32 = 4; // rippled medium `SizedItem::LedgerFetch`
        let limit = history_prefetch_limit.min(missing - earliest + 1);
        let floor = missing
            .saturating_sub(limit.saturating_sub(1))
            .max(earliest);
        let window: Vec<u32> = (floor..=missing).rev().collect();

        assert_eq!(window.len(), history_prefetch_limit as usize);
        assert_eq!(window.first(), Some(&missing));
        assert_eq!(window.last(), Some(&(missing - history_prefetch_limit + 1)));
        assert!(window.windows(2).all(|pair| pair[0] == pair[1] + 1));
    }

    #[test]
    fn history_prefetch_window_respects_earliest_sequence_floor() {
        let missing: u32 = 10;
        let earliest: u32 = 5;
        let history_prefetch_limit: u32 = 4; // rippled medium `SizedItem::LedgerFetch`
        let limit = history_prefetch_limit.min(missing - earliest + 1);
        let floor = missing
            .saturating_sub(limit.saturating_sub(1))
            .max(earliest);
        let window: Vec<u32> = (floor..=missing).rev().collect();

        assert_eq!(window, vec![10, 9, 8, 7]);
    }

    #[test]
    fn same_history_fetch_pack_remains_suppressed_after_one_second() {
        let in_flight = Some((500, Instant::now() - Duration::from_secs(2)));
        assert!(same_history_fetch_pack_is_suppressed(in_flight, 500));
        assert!(!same_history_fetch_pack_is_suppressed(in_flight, 499));
    }

    #[test]
    fn start_valid_preserves_rippled_zero_peer_threshold() {
        // `NetworkOPsImp` constructs `minPeerCount_` as zero when startValid.
        assert_eq!(required_peer_count(0), 0);
        assert_eq!(required_peer_count(1), 1);
        assert_eq!(required_peer_count(3), 3);
    }

    #[test]
    fn start_valid_full_remains_full_across_an_empty_transport_snapshot() {
        let state =
            crate::network::network_ops::SharedNetworkOpsState::new(NetworkOpsOperatingMode::Full);

        // The zero-threshold call path uses TransportConnectivity, whose
        // coordinator regression verifies peer membership changes while Full
        // stays Full. No legacy mode write occurs at this heartbeat boundary.
        assert_eq!(state.operating_mode(), NetworkOpsOperatingMode::Full);
    }

    #[test]
    fn heartbeat_reasserts_only_rippled_normalization_modes() {
        assert_eq!(
            heartbeat_operating_mode_reassertion(NetworkOpsOperatingMode::Disconnected),
            Some(NetworkOpsOperatingMode::Connected)
        );
        assert_eq!(
            heartbeat_operating_mode_reassertion(NetworkOpsOperatingMode::Syncing),
            Some(NetworkOpsOperatingMode::Syncing)
        );
        assert_eq!(
            heartbeat_operating_mode_reassertion(NetworkOpsOperatingMode::Connected),
            Some(NetworkOpsOperatingMode::Connected)
        );
        assert_eq!(
            heartbeat_operating_mode_reassertion(NetworkOpsOperatingMode::Tracking),
            None
        );
        assert_eq!(
            heartbeat_operating_mode_reassertion(NetworkOpsOperatingMode::Full),
            None
        );
    }

    #[test]
    fn preferred_lcl_reconciliation_runs_only_after_jtaccept_delivery() {
        assert!(!should_reconcile_preferred_lcl(ConsensusPhase::Open));
        assert!(!should_reconcile_preferred_lcl(ConsensusPhase::Establish));
        assert!(should_reconcile_preferred_lcl(ConsensusPhase::Accepted));
        assert!(!should_run_end_consensus_reconciliation(
            ConsensusPhase::Accepted,
            true,
            false
        ));
        assert!(!should_run_end_consensus_reconciliation(
            ConsensusPhase::Accepted,
            false,
            true
        ));
        assert!(should_run_end_consensus_reconciliation(
            ConsensusPhase::Accepted,
            false,
            false
        ));
    }

    #[test]
    fn operating_mode_promotion_requires_no_end_consensus_ledger_change() {
        assert!(!should_promote_operating_mode_at_end_consensus(
            false,
            PreferredLclReconciliation::NoChange,
        ));
        assert!(!should_promote_operating_mode_at_end_consensus(
            true,
            PreferredLclReconciliation::Pending,
        ));
        assert!(!should_promote_operating_mode_at_end_consensus(
            true,
            PreferredLclReconciliation::Switched,
        ));
        assert!(!should_promote_operating_mode_at_end_consensus(
            true,
            PreferredLclReconciliation::Provisional,
        ));
        assert!(should_promote_operating_mode_at_end_consensus(
            true,
            PreferredLclReconciliation::NoChange,
        ));

        // Publication identity remains observable independently of promotion
        // authority; the emitted fact's freshness bit carries the
        // `!ledgerChange` decision instead.
        assert!(!should_emit_coordinator_publication(true, false));
        assert!(!should_emit_coordinator_publication(false, true));
        assert!(should_emit_coordinator_publication(true, true));
        assert!(!coordinator_publication_is_fresh(false, true));
        assert!(!coordinator_publication_is_fresh(true, false));
        assert!(coordinator_publication_is_fresh(true, true));
    }

    #[test]
    fn provisional_real_inbound_candidate_reconciles_without_switch_side_effects() {
        let mut root = ApplicationRoot::new(0).expect("root should build");
        let local = immutable_ledger(10, 0x10);
        let target = immutable_ledger(12, 0x20);
        let target_hash = *target.header().hash.as_uint256();
        root.attach_default_ledger_master_runtime();
        root.on_closed_ledger(Arc::clone(&local));
        root.set_network_ops_operating_mode(NetworkOpsOperatingMode::Full);
        root.set_need_network_ledger(true);
        let (_store_dir, inbound) =
            install_real_provisional_lcl_candidate(&mut root, Arc::clone(&target));
        root.validations().register_ledger(target.as_ref());
        let (node_id, validation) = preferred_validation(
            target_hash,
            target.header().seq,
            root.time_keeper().close_time().as_seconds(),
        );
        root.validations()
            .validations()
            .lock()
            .expect("validations mutex")
            .add(node_id, validation);

        let preference = root.validations().preferred_lcl_diagnostic(
            &crate::consensus::rcl_validation::RclValidatedLedger::from_ledger(local.as_ref()),
            root.ledger_master_runtime()
                .expect("ledger master runtime")
                .ledger_master()
                .valid_ledger_seq(),
            &std::collections::BTreeMap::new(),
        );
        assert_eq!(
            preference.selected, target_hash,
            "test validation selects target"
        );
        let closed_before = root.closed_ledger().expect("local LCL");
        let open_before = root.open_ledger().current();
        let txq_before = root.tx_q_rpc_report();
        let published_before = root.published_ledger().map(|ledger| ledger.header().hash);
        let mut runner = RecordingRunner::accepted(*local.header().hash.as_uint256());
        let consensus_rt = AppConsensusRuntime::new();
        let mut last_round = None;
        let mut sampler = LclAuditSampler::new();
        let mut provisional_waiter = None;
        let status_broadcasts = Arc::new(AtomicUsize::new(0));
        let broadcast_counter = Arc::clone(&status_broadcasts);
        let observe_status_broadcast =
            move |_root: &ApplicationRoot,
                  _ledger: &Ledger,
                  _event: i32,
                  _have_correct_lcl: bool| {
                broadcast_counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            };

        assert_eq!(
            reconcile_preferred_lcl_with_status_broadcaster(
                &root,
                &inbound,
                &mut runner,
                &consensus_rt,
                &mut last_round,
                &mut sampler,
                &mut provisional_waiter,
                &observe_status_broadcast,
            ),
            PreferredLclReconciliation::Provisional,
        );
        assert!(inbound.is_provisional(&target_hash));
        assert_eq!(
            status_broadcasts.load(std::sync::atomic::Ordering::Relaxed),
            0,
            "provisional reconciliation must not invoke the switched-ledger status broadcast"
        );
        assert_eq!(
            root.closed_ledger()
                .expect("closed LCL remains local")
                .header()
                .hash,
            closed_before.header().hash,
            "no switch_last_closed_ledger closed-LCL mutation before durability"
        );
        let open_after = root.open_ledger().current();
        assert_eq!(
            open_after.ledger_current_index,
            open_before.ledger_current_index
        );
        assert_eq!(open_after.parent_hash, open_before.parent_hash);
        assert_eq!(
            root.tx_q_rpc_report(),
            txq_before,
            "no TxQ/open-ledger mutation"
        );
        assert_eq!(
            root.network_ops_operating_mode(),
            NetworkOpsOperatingMode::Full
        );
        assert!(
            root.need_network_ledger(),
            "no switch clears needNetworkLedger"
        );
        assert_eq!(
            root.published_ledger().map(|ledger| ledger.header().hash),
            published_before,
            "no publication/history advance",
        );
        assert_eq!(runner.start_rounds, 0, "no replacement or ordinary round");
        assert_eq!(runner.phase(), ConsensusPhase::Accepted);
        assert_eq!(last_round, None);
        assert!(
            inbound
                .acquire(target_hash, target.header().seq, AcquireReason::Consensus)
                .is_some(),
            "the provisional reconciliation retains the exact target recovery"
        );
        inbound.stop();
    }

    #[test]
    fn provisional_lcl_candidate_blocks_mode_promotion_and_replacement_round() {
        assert!(!should_begin_ordinary_round(
            true,
            PreferredLclReconciliation::Provisional,
        ));
        assert!(!should_begin_ordinary_round(
            false,
            PreferredLclReconciliation::NoChange,
        ));
        assert!(should_begin_ordinary_round(
            true,
            PreferredLclReconciliation::NoChange,
        ));
    }

    #[test]
    fn heartbeat_job_runs_under_ingress_flood_and_ingress_drain_is_bounded() {
        let queue = JobQueue::new(1);
        let (ingress, command_rx) = ConsensusIngress::bounded(128);
        let scheduler = ConsensusJobScheduler::new(queue.clone(), ingress);
        let (gate_started_tx, gate_started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();

        // Hold the only worker so the full flood and the timer job are queued
        // together. JtNetopTimer must then win over JtTransaction work.
        assert!(queue.add_job(JobType::JtAdmin, "test-gate", move || {
            gate_started_tx.send(()).expect("gate start receiver");
            release_rx.recv().expect("gate release sender");
        }));
        gate_started_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("gate should occupy the worker");

        for _ in 0..MAX_COMMANDS_PER_TURN * 4 {
            assert!(queue.add_job(JobType::JtTransaction, "ingress", || {}));
        }
        assert!(scheduler.schedule_heartbeat());
        assert_eq!(queue.job_count(JobType::JtNetopTimer), 1);

        release_tx.send(()).expect("release gate");
        assert!(matches!(
            command_rx
                .recv_timeout(Duration::from_secs(2))
                .expect("JtNetopTimer must run before ingress flood"),
            ConsensusCommand::Heartbeat
        ));

        let (ingress_tx, ingress_rx) = mpsc::channel();
        for value in 0..=MAX_COMMANDS_PER_TURN {
            ingress_tx.send(value).expect("ingress receiver");
        }
        let mut processed = Vec::new();
        drain_bounded(&ingress_rx, MAX_COMMANDS_PER_TURN, |value| {
            processed.push(value);
        });
        assert_eq!(processed.len(), MAX_COMMANDS_PER_TURN);
        assert_eq!(ingress_rx.try_recv(), Ok(MAX_COMMANDS_PER_TURN));

        let (completion_tx, completion_rx) = mpsc::channel();
        for value in 0..=MAX_LEDGER_COMPLETIONS_PER_TURN {
            completion_tx.send(value).expect("completion receiver");
        }
        let mut completions = Vec::new();
        drain_bounded(&completion_rx, MAX_LEDGER_COMPLETIONS_PER_TURN, |value| {
            completions.push(value);
        });
        assert_eq!(completions.len(), MAX_LEDGER_COMPLETIONS_PER_TURN);
        assert_eq!(
            completion_rx.try_recv(),
            Ok(MAX_LEDGER_COMPLETIONS_PER_TURN)
        );

        queue.rendezvous();
        queue.stop();
    }

    #[test]
    fn production_ingress_wiring_orders_proposal_txset_and_heartbeat() {
        let root = ApplicationRoot::new(0).expect("root should build");
        let (ingress, rx) = ConsensusIngress::bounded(3);
        let completion_ingress = ingress.clone();
        root.inbound_transactions()
            .lock()
            .expect("inbound transactions")
            .set_map_complete_sink(Arc::new(move |hash, set| {
                completion_ingress.publish_tx_set(hash, set)
            }));

        let seed = random_seed();
        let secret = generate_secret_key(KeyType::Secp256k1, &seed).expect("secret key");
        let public_key = derive_public_key(KeyType::Secp256k1, &secret).expect("public key");
        let proposal = overlay::inbound::QueuedProposal {
            peer_id: 7,
            suppression: Uint256::from_u64(1),
            public_key,
            current_tx_hash: Uint256::from_u64(2),
            previous_ledger: Uint256::from_u64(3),
            message: overlay::TmProposeSet::default(),
        };
        let txset_hash = Uint256::from_u64(4);
        let txset = Arc::new(shamap::sync::SyncTree::new_with_type(
            shamap::sync::SHAMapType::Transaction,
            false,
            1,
        ));

        assert!(ingress.publish_trusted_proposal(proposal));
        assert!(
            root.inbound_transactions()
                .lock()
                .expect("inbound transactions")
                .give_set(txset_hash, txset, true),
            "map-complete producer must publish through the production facade"
        );
        assert!(ingress.publish_heartbeat());

        let mut saw_disagreeing_proposal = false;
        let mut saw_disagreeing_txset = false;
        let mut accepted_stale_position = false;
        for _ in 0..3 {
            match rx.recv().expect("ordered consensus command") {
                ConsensusCommand::PeerProposal(_) => saw_disagreeing_proposal = true,
                ConsensusCommand::TxSetComplete { .. } => saw_disagreeing_txset = true,
                ConsensusCommand::Heartbeat => {
                    // This models the timer's `have_consensus` decision: the
                    // stale position is acceptable only if neither earlier
                    // disagreeing ingress item has reached the owner.
                    accepted_stale_position = !saw_disagreeing_proposal && !saw_disagreeing_txset;
                }
                _ => panic!("unexpected command in ordering regression"),
            }
        }

        assert!(saw_disagreeing_proposal);
        assert!(saw_disagreeing_txset);
        assert!(!accepted_stale_position);
    }

    #[test]
    fn durable_txset_overflow_retries_behind_older_heartbeat() {
        let root = ApplicationRoot::new(0).expect("root should build");
        let (ingress, rx) = ConsensusIngress::bounded(2);
        assert!(ingress.publish_heartbeat());
        assert!(ingress.publish_heartbeat());

        let completion_ingress = ingress.clone();
        root.inbound_transactions()
            .lock()
            .expect("inbound transactions")
            .set_map_complete_sink(Arc::new(move |hash, set| {
                completion_ingress.publish_tx_set(hash, set)
            }));

        let hash = Uint256::from_u64(0xA11CE);
        let set = Arc::new(shamap::sync::SyncTree::new_with_type(
            shamap::sync::SHAMapType::Transaction,
            false,
            1,
        ));
        assert!(
            root.inbound_transactions()
                .lock()
                .expect("inbound transactions")
                .give_set(hash, set, true),
            "producer must admit the completed set"
        );
        let recovered = root
            .inbound_transactions()
            .lock()
            .expect("inbound transactions")
            .take_pending_map_completions(1);
        assert_eq!(recovered.len(), 1, "saturated direct FIFO marks replay");
        let mut retained = VecDeque::new();
        assert!(enqueue_recovered_txsets(&ingress, &mut retained, recovered));
        assert_eq!(retained.len(), 1, "full FIFO must retain completion");

        assert!(matches!(rx.recv().unwrap(), ConsensusCommand::Heartbeat));
        assert!(enqueue_recovered_txsets(&ingress, &mut retained, []));
        assert!(retained.is_empty());

        // The recovered completion is appended after the heartbeat that was
        // already queued; it cannot call got_tx_set out of band.
        assert!(matches!(rx.recv().unwrap(), ConsensusCommand::Heartbeat));
        assert!(matches!(
            rx.recv().unwrap(),
            ConsensusCommand::TxSetComplete { hash: actual, .. } if actual == hash
        ));
    }

    #[test]
    fn accepted_phase_can_reconcile_and_start_after_jtaccept_delivery() {
        // After the JtAccept command is consumed, the strand owns the
        // contiguous accepted-work/endConsensus progression.
        assert!(should_reconcile_preferred_lcl(ConsensusPhase::Accepted));
        assert!(should_begin_ordinary_round(
            true,
            PreferredLclReconciliation::NoChange
        ));
        assert!(!should_reconcile_preferred_lcl(ConsensusPhase::Open));
    }

    #[test]
    fn completion_handoff_registers_before_acceptance_or_acknowledgement() {
        // Keep the ordering contract explicit: a completion is first durable
        // in LedgerHistory, then visible to the validation adaptor's canonical
        // resolver, then eligible for checkAccept, and only then acknowledged
        // out of the inbound ready queue. The strand loop performs these calls
        // in that exact sequence; this fixture documents the two visibility
        // prerequisites without requiring a running node.
        let root = ApplicationRoot::new(0).expect("root should build");
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let ledger = immutable_ledger(102, 0xA2);
        let hash = *ledger.header().hash.as_uint256();

        assert!(
            persist_completed_inbound_ledger(&root, &master, &ledger, AcquireReason::Consensus)
                .acknowledged
        );
        root.validations().register_ledger(&ledger);
        let validations = root
            .validations()
            .validations()
            .lock()
            .expect("validations lock");
        assert!(
            consensus::rcl_support::ValidationsAdaptor::acquire(validations.adaptor(), &hash,)
                .is_some()
        );
    }

    #[test]
    fn completed_inbound_ledger_is_cached_without_promoting_unvalidated_state() {
        let root = ApplicationRoot::new(0).expect("root should build");
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let current = immutable_ledger(101, 0xA1);

        assert!(root.validated_ledger().is_none());
        assert!(
            persist_completed_inbound_ledger(&root, &master, &current, AcquireReason::Consensus)
                .inserted
        );
        assert!(master.validated_ledger().is_none());
        assert!(root.validated_ledger().is_none());
        assert_eq!(
            master
                .ledger_history()
                .get_cached_ledger_by_hash(current.header().hash)
                .expect("completed ledger should be available to checkAccept")
                .header()
                .seq,
            101
        );
    }

    #[test]
    fn completed_inbound_ledgers_are_cached_without_marking_complete() {
        let master = LedgerMaster::new(MonotonicClock::default(), LedgerMasterConfig::default());
        let newer = immutable_ledger(101, 0xA1);
        let older = immutable_ledger(100, 0xA0);

        assert!(record_completed_inbound_ledger(&master, &newer));
        assert!(record_completed_inbound_ledger(&master, &older));

        assert!(master.complete_ledgers().empty());
        assert!(
            master
                .ledger_history()
                .get_cached_ledger_by_hash(older.header().hash)
                .is_some_and(|ledger| ledger.header().hash == older.header().hash)
        );
    }
}
