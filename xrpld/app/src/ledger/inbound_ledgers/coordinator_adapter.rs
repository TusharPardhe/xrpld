//! M4.2-B coordinator adapter: hosts the serialized [`CoordinatorRunner`] and
//! binds the acquisition ports to app resources.
//!
//! Ownership boundary: this adapter is the production host of the coordinator
//! runner, which is the single acquisition session lifecycle owner. The adapter
//! owns:
//!
//! * the [`CoordinatorRunner`] (built by the caller with whatever [`PlanSeed`]
//!   the switchover needs);
//! * a typed [`AcquisitionEvent`] queue (bounded packet admission happens at
//!   the per-session [`AdmissionGate`]; control completions are never dropped);
//! * a published immutable [`Arc<RoutingSnapshot>`] that overlay ingress uses
//!   to look up a session route and reserve admission without touching mutable
//!   coordinator state;
//! * the fetch-pack cache that by-hash (`TMGetObjectByHash`) replies populate.
//!
//! No port invokes coordinator logic while holding an adapter lock, and
//! completions return as typed events the owner drains with
//! [`CoordinatorAdapter::drain`].
//!
//! ## Rippled parity notes
//!
//! * `TMGetLedger` replies (`TmLedgerData`) carry node ids on the wire;
//!   rippled's `getSHAMapNodeID` (`LedgerNodeHelpers.cpp`) emits the `nodeid`
//!   field for inner nodes and derives leaf ids from the node key. The Quaxar
//!   wire `TmLedgerNode` carries `nodeid`; the adapter preserves it verbatim
//!   into [`InboundLedgerNodeData`]. The engine's Base path applies the header
//!   and root by node data alone (`InboundLedger.cpp` root handling), and its
//!   state/tx path requires every node id (a missing id is rejected the same
//!   way rippled rejects a bad node).
//! * `TMGetObjectByHash` replies are fetch-pack data keyed by hash, never
//!   routed to a session mailbox and never carrying node ids
//!   (`PeerImp::processGetObjectByHash` -> `addFetchPack`); the SHAMap sync
//!   filter consumes them by hash during traversal. Quaxar mirrors this with
//!   [`CoordinatorAdapter::stash_fetch_pack`].
//!
//! References: `rippled/src/xrpld/app/ledger/detail/InboundLedger.cpp`,
//! `rippled/src/xrpld/app/ledger/detail/LedgerNodeHelpers.cpp`,
//! `rippled/src/xrpld/peer/PeerImp.cpp` (`processGetObjectByHash`).

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::mpsc;
use std::sync::{Arc, Mutex, RwLock};

use basics::base_uint::Uint256;
use basics::sha_map_hash::SHAMapHash;
use bytes::Bytes;
use ledger::{
    FetchPackCache, InboundLedgerDataType, InboundLedgerNodeData, InboundLedgerObjectType,
    InboundLedgerPacket, make_get_ledger_with_node_ids, make_inbound_needed_by_hash_request,
};
use overlay::{Peer, PeerId as OverlayPeerId, PeerSet, ProtocolMessage, SimplePeerSet};

use acquisition::{
    AcquisitionEffect, AcquisitionEvent, AdmissionBudget, AdmissionGate, AdmittedLedgerPacket,
    BackpressureOutcome, CancellationPort, CoordinatorPorts, CoordinatorRunner,
    DurableHandoffAcknowledgement, DurableHandoffId, HandoffPort, LedgerDataRequest,
    LedgerRequestPort, PeerAvailabilitySnapshot, PeerId, PeerRequest, PhasePort, ReadCompletion,
    ReadOutcome, ReadPort, ReadPriority, ReadRequest, ReferenceDecision, RouteEntry,
    RoutingGeneration, RoutingSnapshot, RunEpoch, SessionPhase, SessionRef, ShadowConfig,
    ShadowObservation, ShadowOutcome, ShadowRunner, ShadowSnapshot, TimerPort, WritePort,
};

use super::read_broker::{
    NodeReadBroker, ReadAdmission, ReadKey, ReadOutcome as BrokerReadOutcome, ReadReady,
    ReadReadySink, ReadTicket,
};
use crate::shamap::shamap_store_backend::SHAMapStoreNodeStore;

/// The wire `liBASE` request type: a full-ledger header request.
const LI_BASE: i32 = 0;
const LI_TX_NODE: i32 = 1;
const LI_AS_NODE: i32 = 2;
const QT_INDIRECT: i32 = 0;

/// Lifecycle, cancellation, handoff, write, and timer facts use this bounded
/// reserved channel. Producers use `send`, applying backpressure instead of
/// dropping an exact terminal fact; packet ingress has a distinct channel and
/// cannot consume this capacity.
pub(crate) type EventSender = mpsc::SyncSender<AcquisitionEvent>;
pub(crate) type EventReceiver = mpsc::Receiver<AcquisitionEvent>;

/// Exact control events produced off the coordinator owner thread. A producer
/// never waits on the owner that consumes this bounded lane: full events remain
/// in this resource-local FIFO until its port is flushed from an owner turn.
#[derive(Clone)]
pub(crate) struct RetainedControlEvents {
    tx: EventSender,
    pending: Arc<Mutex<VecDeque<AcquisitionEvent>>>,
}

impl RetainedControlEvents {
    pub(crate) fn new(tx: EventSender) -> Self {
        Self {
            tx,
            pending: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    pub(crate) fn push(&self, event: AcquisitionEvent) {
        let mut pending = self.pending.lock().expect("retained control events lock");
        pending.push_back(event);
        Self::flush_locked(&self.tx, &mut pending);
    }

    /// Retain an exact completion without competing for the shared control
    /// lane from its producer thread. High-volume read callbacks use this and
    /// let the coordinator owner admit a bounded wave, leaving capacity for
    /// write/fence and timer lifecycle completions.
    pub(crate) fn retain(&self, event: AcquisitionEvent) {
        self.pending
            .lock()
            .expect("retained control events lock")
            .push_back(event);
    }

    pub(crate) fn flush(&self) {
        let mut pending = self.pending.lock().expect("retained control events lock");
        Self::flush_locked(&self.tx, &mut pending);
    }

    pub(crate) fn flush_bounded(&self, limit: usize) {
        let mut pending = self.pending.lock().expect("retained control events lock");
        for _ in 0..limit {
            let Some(event) = pending.pop_front() else {
                break;
            };
            match self.tx.try_send(event) {
                Ok(()) => {}
                Err(mpsc::TrySendError::Full(event))
                | Err(mpsc::TrySendError::Disconnected(event)) => {
                    pending.push_front(event);
                    break;
                }
            }
        }
    }

    fn flush_locked(tx: &EventSender, pending: &mut VecDeque<AcquisitionEvent>) {
        while let Some(event) = pending.pop_front() {
            match tx.try_send(event) {
                Ok(()) => {}
                Err(mpsc::TrySendError::Full(event))
                | Err(mpsc::TrySendError::Disconnected(event)) => {
                    pending.push_front(event);
                    break;
                }
            }
        }
    }
}

/// Reserved lifecycle capacity. This queue is separate from the packet lane,
/// so normal packet pressure cannot displace cancellation, write/fence, timer,
/// or durable-handoff facts.
pub(crate) const CONTROL_EVENT_QUEUE_CAPACITY: usize = 256;

/// Packet ingress is isolated from control/completion facts in a bounded
/// channel. Only overlay admission uses this sender; it must use `try_send` so
/// a full ingress queue settles its admission lease and defers the frame.
type PacketEventSender = mpsc::SyncSender<AcquisitionEvent>;
type PacketEventReceiver = mpsc::Receiver<AcquisitionEvent>;

/// Global retained packet events between overlay ingress and the serialized
/// owner. This is intentionally below the per-session 128-packet admission
/// gate so queue-full handling is exercised before a single route consumes its
/// whole lease budget.
pub(crate) const PACKET_INGRESS_QUEUE_CAPACITY: usize = 64;

/// One owner-loop pass gives completion/control facts priority, but remains
/// bounded so a continuously ready channel cannot monopolize the runner.
const CONTROL_EVENTS_PER_DRAIN: usize = 512;

/// Wall-clock guard for one production owner burst. A complete rippled-sized
/// read batch is kept atomic, but successive control facts yield promptly to
/// consensus and packet work.
const CONTROL_DRAIN_TIME_SLICE: std::time::Duration = std::time::Duration::from_millis(5);

/// One owner-loop pass then advances a bounded packet slice, preserving packet
/// progress without allowing ingress to starve lifecycle control facts.
const PACKET_EVENTS_PER_DRAIN: usize = 32;

/// The disposition of one wire ledger-data reply for tracing and overlay
/// backpressure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LedgerDataIngressDisposition {
    /// The packet was admitted and enqueued for the owner loop.
    Delivered,
    /// Admission capacity is exhausted; the overlay defers the frame. A
    /// deferred packet has no actor-side effect.
    Deferred,
    /// No route exists for the ledger hash (unknown session or terminal).
    Unmatched,
    /// The coordinator is shutting down or the session is terminal.
    Terminal,
    /// The wire packet could not be decoded.
    Invalid,
}

/// Bounded per-session ingress accounting and routing generation state.
///
/// `packets_invalid` and `fetch_pack_stashes` are incremented today but not
/// yet read; they feed the M6/M7 metrics emission (required observability:
/// packet admissions/deferrals/drops by disposition).
#[derive(Debug, Default)]
struct AdapterStats {
    packets_admitted: u64,
    packets_deferred: u64,
    packets_unmatched: u64,
    #[allow(dead_code)]
    packets_invalid: u64,
    packets_terminal: u64,
    #[allow(dead_code)]
    fetch_pack_stashes: u64,
}

/// Immutable overlay-ingress capability. It owns no coordinator lifecycle
/// state: it only reads the published route snapshot, reserves the exact
/// route's admission gate, and queues a typed packet event. Keeping this
/// separate from [`CoordinatorAdapter`] lets a peer reply synchronously while
/// request-effect dispatch still holds the adapter's mutable owner lock.
#[derive(Clone)]
pub(crate) struct CoordinatorIngress {
    routing_snapshot: Arc<RwLock<Arc<RoutingSnapshot>>>,
    packet_tx: PacketEventSender,
    stats: Arc<Mutex<AdapterStats>>,
}

impl CoordinatorIngress {
    /// Route a wire `TmLedgerData` reply without accessing mutable coordinator
    /// state. The selected route and its gate remain valid through the moved
    /// admission lease even if the owner replaces the route before draining.
    pub(crate) fn route_ledger_data(
        &self,
        peer_id: OverlayPeerId,
        message: &overlay::TmLedgerData,
    ) -> LedgerDataIngressDisposition {
        let Some(packet_type) = map_wire_ledger_type(message.r#type) else {
            return LedgerDataIngressDisposition::Invalid;
        };
        let Some(hash) = Uint256::from_slice(&message.ledger_hash) else {
            return LedgerDataIngressDisposition::Invalid;
        };
        let mut nodes = Vec::with_capacity(message.nodes.len());
        for (packet_index, node) in message.nodes.iter().enumerate() {
            let Some(data) = decode_wire_ledger_node(node, packet_type, packet_index) else {
                return LedgerDataIngressDisposition::Invalid;
            };
            nodes.push(data);
        }
        self.admit(hash, InboundLedgerPacket::new(packet_type, nodes), peer_id)
    }

    fn admit(
        &self,
        hash: Uint256,
        packet: InboundLedgerPacket,
        peer_id: OverlayPeerId,
    ) -> LedgerDataIngressDisposition {
        let snapshot = Arc::clone(
            &self
                .routing_snapshot
                .read()
                .expect("coordinator routing snapshot read"),
        );
        let Some(route) = snapshot.route(&hash) else {
            self.stats
                .lock()
                .expect("adapter stats lock")
                .packets_unmatched += 1;
            return LedgerDataIngressDisposition::Unmatched;
        };
        let bytes = packet
            .nodes
            .iter()
            .map(|node| node.node_data.len() as u64)
            .sum::<u64>();
        // Admission capacity is measured in complete `TMLedgerData` frames,
        // matching rippled's received-data queue and the legacy 128-packet
        // bound. The independent byte reservation still measures all nodes.
        match route.gate().try_reserve(1, bytes) {
            BackpressureOutcome::Admitted(lease) => {
                let admitted = match AdmittedLedgerPacket::new(
                    lease,
                    route.session(),
                    PeerId::new(u64::from(peer_id)),
                    packet,
                ) {
                    Ok(packet) => packet,
                    Err(_) => return LedgerDataIngressDisposition::Invalid,
                };
                match self
                    .packet_tx
                    .try_send(AcquisitionEvent::PacketAdmitted(admitted))
                {
                    Ok(()) => {
                        self.stats
                            .lock()
                            .expect("adapter stats lock")
                            .packets_admitted += 1;
                        LedgerDataIngressDisposition::Delivered
                    }
                    Err(mpsc::TrySendError::Full(error)) => {
                        if let AcquisitionEvent::PacketAdmitted(mut packet) = error {
                            let _ = packet.settle();
                        }
                        self.stats
                            .lock()
                            .expect("adapter stats lock")
                            .packets_deferred += 1;
                        LedgerDataIngressDisposition::Deferred
                    }
                    Err(mpsc::TrySendError::Disconnected(error)) => {
                        if let AcquisitionEvent::PacketAdmitted(mut packet) = error {
                            let _ = packet.settle();
                        }
                        self.stats
                            .lock()
                            .expect("adapter stats lock")
                            .packets_terminal += 1;
                        LedgerDataIngressDisposition::Terminal
                    }
                }
            }
            BackpressureOutcome::Deferred => {
                self.stats
                    .lock()
                    .expect("adapter stats lock")
                    .packets_deferred += 1;
                LedgerDataIngressDisposition::Deferred
            }
            BackpressureOutcome::Rejected(_) => {
                self.stats
                    .lock()
                    .expect("adapter stats lock")
                    .packets_terminal += 1;
                LedgerDataIngressDisposition::Terminal
            }
        }
    }
}

/// The coordinator adapter: hosts the runner and its event queue, publishes the
/// routing snapshot, and adapts overlay/data completions into typed events.
///
/// Generic over the seven port types so deterministic tests inject
/// `acquisition::fake::*` ports and production instantiates the app ports below.
pub(crate) struct CoordinatorAdapter<R, RD, WR, T, H, P, C> {
    runner: CoordinatorRunner,
    /// Read-only mirror driven on this same serialized owner. It receives the
    /// exact event before production consumes it and observes the resulting
    /// effects before any port executes them; it can therefore compare state
    /// without becoming a second lifecycle authority.
    shadow: ShadowRunner,
    pub(crate) requests: R,
    reads: RD,
    writes: WR,
    timers: T,
    pub(crate) handoffs: H,
    phase: P,
    cancellations: C,
    tx: EventSender,
    rx: EventReceiver,
    // Retained solely for deterministic adapter tests that inject packets through
    // the same isolated packet lane as overlay ingress.
    #[cfg_attr(not(test), allow(dead_code))]
    packet_tx: PacketEventSender,
    packet_rx: PacketEventReceiver,
    routes: BTreeMap<Uint256, RouteEntry>,
    ingress: CoordinatorIngress,
    routing_generation: u64,
    /// Round-robin producer selected after each freed control-lane slot. Read,
    /// write, and timer ports retain completions independently, so a fixed flush
    /// order lets a continuously ready earlier producer starve every later one.
    completion_flush_cursor: u8,
    /// One non-read fact observed while coalescing a consecutive read wave.
    /// It is processed first on the next control iteration, preserving channel
    /// order without preventing the read barrier from resuming once.
    pending_control_event: Option<AcquisitionEvent>,
    /// Whether the preceding bounded drain stopped with owner work remaining.
    /// NetworkOps uses this signal to avoid an artificial 50ms sleep without
    /// turning the coordinator into a separate scheduler.
    last_drain_has_more: bool,
    fetch_pack: Arc<FetchPackCache>,
    /// Exact target hashes whose coordinator sessions terminally failed. The
    /// registry drains this bounded-per-owner-turn set after releasing the
    /// coordinator lock and records rippled-compatible failure cooldowns.
    /// Cancellations remain excluded: only `SessionPhase::Failed` represents
    /// an acquisition failure eligible for history re-admission suppression.
    terminal_failures: BTreeSet<Uint256>,
    /// Recipient acknowledgements retained outside the shared control channel.
    /// They are consumed before any completion producer can refill a freed
    /// control slot, preventing a permanently ready producer from starving the
    /// `DurablePending -> Complete` transition and its graph-release receipt.
    priority_durable_acks: VecDeque<DurableHandoffAcknowledgement>,
    /// Exact durable acknowledgements that the runner accepted and processed.
    /// Enqueue success is insufficient: NetworkOps may release graph ownership
    /// only after this receipt proves `DurablePending -> Complete` occurred for
    /// the same `(handoff, session)`.
    processed_durable_acks: VecDeque<(DurableHandoffId, SessionRef)>,
    /// Last exact owners whose already-retained Generic reads were upgraded.
    /// These mirrors carry no lifecycle authority; the runner remains the
    /// source of truth and each transition is applied idempotently to the
    /// resource-local broker queues.
    promoted_recovery_read_owner: Option<SessionRef>,
    promoted_validation_read_owner: Option<SessionRef>,
}

impl<R, RD, WR, T, H, P, C> CoordinatorAdapter<R, RD, WR, T, H, P, C>
where
    R: LedgerRequestPort,
    RD: ReadPort,
    WR: WritePort,
    T: TimerPort,
    H: HandoffPort,
    P: PhasePort,
    C: CancellationPort,
{
    /// Builds an adapter around an externally supplied event channel, so the
    /// production wiring can hand the same sender to the read/timer ports
    /// before the adapter exists.
    pub(crate) fn with_event_channel(
        runner: CoordinatorRunner,
        shadow_config: ShadowConfig,
        requests: R,
        reads: RD,
        writes: WR,
        timers: T,
        handoffs: H,
        phase: P,
        cancellations: C,
        #[cfg_attr(not(test), allow(dead_code))]
        // read via test-only stash_fetch_pack until M6-C wiring
        fetch_pack: Arc<FetchPackCache>,
        tx: EventSender,
        rx: EventReceiver,
        packet_tx: PacketEventSender,
        packet_rx: PacketEventReceiver,
    ) -> Self {
        let shadow = ShadowRunner::new(shadow_config, runner.run_epoch());
        let ingress = CoordinatorIngress {
            routing_snapshot: Arc::new(RwLock::new(Arc::new(RoutingSnapshot::new(
                RoutingGeneration::new(0),
                BTreeMap::new(),
            )))),
            packet_tx: packet_tx.clone(),
            stats: Arc::new(Mutex::new(AdapterStats::default())),
        };
        let mut adapter = Self {
            runner,
            shadow,
            requests,
            reads,
            writes,
            timers,
            handoffs,
            phase,
            cancellations,
            tx,
            rx,
            packet_tx,
            packet_rx,
            routes: BTreeMap::new(),
            ingress,
            routing_generation: 0,
            completion_flush_cursor: 0,
            pending_control_event: None,
            last_drain_has_more: false,
            fetch_pack,
            terminal_failures: BTreeSet::new(),
            priority_durable_acks: VecDeque::new(),
            processed_durable_acks: VecDeque::new(),
            promoted_recovery_read_owner: None,
            promoted_validation_read_owner: None,
        };
        adapter.publish_routing();
        adapter
    }

    /// The immutable routing snapshot overlay ingress reads. Routes are cached
    /// per session and refreshed after every event; a gate is never rebuilt
    /// while its session still has in-flight leases.
    #[allow(dead_code)] // overlay ingress consumes the snapshot in M4.2-C3
    pub(crate) fn routing_snapshot(&self) -> Arc<RoutingSnapshot> {
        Arc::clone(
            &self
                .ingress
                .routing_snapshot
                .read()
                .expect("coordinator routing snapshot read"),
        )
    }

    /// Clone the immutable overlay-ingress capability. It remains usable while
    /// the owner is dispatching effects under its mutable adapter lock.
    pub(crate) fn ingress(&self) -> CoordinatorIngress {
        self.ingress.clone()
    }

    /// A cloneable sender for typed completions (reads, writes, timers,
    /// handoffs) posted from worker threads. Backpressure is lossless: the
    /// reserved control channel blocks the producer rather than discarding an
    /// exact lifecycle completion. Reserved for M6-C wiring of completion ports.
    #[allow(dead_code)]
    pub(crate) fn event_sender(&self) -> EventSender {
        self.tx.clone()
    }

    /// The coordinator run epoch, for cross-thread identity checks.
    /// Reserved for M6-C completion-identity checks.
    #[allow(dead_code)]
    pub(crate) const fn run_epoch(&self) -> RunEpoch {
        self.runner.run_epoch()
    }

    /// Return and clear exact hashes whose sessions failed since the last
    /// drain. Callers must consume this only after releasing any coordinator
    /// lock; failure recording is registry-owned resource state, not a second
    /// session lifecycle authority.
    pub(crate) fn take_terminal_failures(&mut self) -> Vec<Uint256> {
        std::mem::take(&mut self.terminal_failures)
            .into_iter()
            .collect()
    }

    /// Return and clear exact durable acknowledgements only after the runner
    /// consumed them and completed the matching session lifecycle transition.
    pub(crate) fn take_processed_durable_acks(&mut self) -> Vec<(DurableHandoffId, SessionRef)> {
        self.processed_durable_acks.drain(..).collect()
    }

    /// Retain an exact recipient acknowledgement for the next owner drain.
    /// This mutates no runner lifecycle state and deliberately bypasses the
    /// shared completion channel, whose slots may be continuously refilled.
    pub(crate) fn retain_durable_handoff_ack(
        &mut self,
        handoff: DurableHandoffId,
        session: SessionRef,
    ) -> bool {
        if !self.durable_handoff_is_pending(handoff, session) {
            return false;
        }
        if self
            .priority_durable_acks
            .iter()
            .any(|ack| ack.handoff() == handoff && ack.session() == session)
        {
            return true;
        }
        if self.priority_durable_acks.len() >= CONTROL_EVENT_QUEUE_CAPACITY {
            return false;
        }
        self.priority_durable_acks
            .push_back(DurableHandoffAcknowledgement::new(handoff, session));
        true
    }

    /// Whether the runner is still awaiting this exact durable handoff.
    pub(crate) fn durable_handoff_is_pending(
        &self,
        handoff: DurableHandoffId,
        session: SessionRef,
    ) -> bool {
        self.runner.session(session).is_some_and(|state| {
            state.phase() == &SessionPhase::DurablePending
                && state.pending_handoff() == Some(handoff)
        })
    }

    /// Immutable shadow state for RPC/metrics consumers. Disabled mode reports
    /// a zero-work snapshot and never records observations.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn shadow_snapshot(&self) -> ShadowSnapshot {
        self.shadow.snapshot()
    }

    /// Drain bounded shadow observations for tracing/metrics publication.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn drain_shadow_observations(&mut self) -> Vec<ShadowObservation> {
        self.shadow.drain_observations()
    }

    /// Handle one typed event and dispatch its effects through the ports.
    /// Effects are executed only after the runner has mutated its state, so no
    /// port observes coordinator state mid-mutation.
    pub(crate) fn handle_fact(&mut self, event: AcquisitionEvent) -> Vec<AcquisitionEffect> {
        // Keep a moved `AdmittedLedgerPacket`'s exact lease charged through
        // ingress and its session mailbox. It is settled when fed, rejected,
        // cancelled, or dropped, so the immutable route gate provides real
        // cross-thread backpressure instead of permitting a late mailbox drop.
        if let AcquisitionEvent::TimerFired {
            operation,
            timer: acquisition::TimerKind::AcquireTimeout,
        } = &event
            && let Some(target) = self
                .runner
                .session(operation.session())
                .map(|session| session.target())
            && let Some(peers) = self.requests.peer_target_capabilities(target)
        {
            self.runner.update_target_peer_capabilities(target, peers);
        }
        let processed_ack_candidate = match &event {
            AcquisitionEvent::DurableHandoffAcknowledged(acknowledgement)
                if self
                    .runner
                    .session(acknowledgement.session())
                    .is_some_and(|state| {
                        state.phase() == &SessionPhase::DurablePending
                            && state.pending_handoff() == Some(acknowledgement.handoff())
                    }) =>
            {
                Some((acknowledgement.handoff(), acknowledgement.session()))
            }
            _ => None,
        };
        let reference_session = event_session(&event);
        self.shadow.record(&event);
        let effects = self.runner.handle_event(event);
        if let Some((handoff, session)) = processed_ack_candidate
            && self.runner.session(session).is_some_and(|state| {
                state.phase() == &SessionPhase::Complete && state.pending_handoff().is_none()
            })
        {
            self.processed_durable_acks.push_back((handoff, session));
        }
        self.reconcile_exact_read_priorities();
        self.observe_shadow_result(reference_session, &effects);
        self.note_terminal_failures(&effects);
        // A request can synchronously produce an overlay reply. Publish the
        // route created by this event before dispatching its outbound effects,
        // otherwise that reply sees the previous snapshot and is rejected.
        self.refresh_routes();
        self.dispatch(&effects);
        effects
    }

    fn handle_read_batch(&mut self, completions: Vec<ReadCompletion>) {
        let reference_sessions = completions
            .iter()
            .map(|completion| completion.operation().session())
            .collect::<BTreeSet<_>>();
        for completion in &completions {
            self.shadow
                .record(&AcquisitionEvent::ReadCompleted(completion.clone()));
        }
        let effects = self.runner.handle_read_batch(completions);
        self.reconcile_exact_read_priorities();
        self.shadow.observe_effects(&effects);
        for session in reference_sessions {
            self.compare_shadow_session(session);
        }
        self.compare_shadow_effect_sessions(&effects);
        self.note_terminal_failures(&effects);
        self.refresh_routes();
        self.dispatch(&effects);
    }

    /// Advance one bounded owner-loop slice. Control/completion facts run
    /// first except that an acquisition deadline gives already-admitted
    /// packets their bounded turn before evaluating progress. Neither queue
    /// is drained without a fixed bound, so continuous traffic cannot
    /// monopolize the owner.
    /// Returns the number of facts handled.
    pub(crate) fn drain(&mut self) -> usize {
        let mut handled = 0;
        let mut control_handled = 0;
        let mut packets_handled = 0;
        let mut packet_limited = false;
        let started = std::time::Instant::now();
        let mut control_limited = false;
        while control_handled < CONTROL_EVENTS_PER_DRAIN {
            let Some(acknowledgement) = self.priority_durable_acks.pop_front() else {
                break;
            };
            self.handle_fact(AcquisitionEvent::DurableHandoffAcknowledged(
                acknowledgement,
            ));
            handled += 1;
            control_handled += 1;
        }
        // Bootstrap an empty control lane from one producer. Subsequent free
        // slots rotate producers, preventing continuous read traffic from
        // indefinitely hiding write/fence and timer lifecycle facts.
        self.flush_next_completion_source();
        while control_handled < CONTROL_EVENTS_PER_DRAIN {
            if !cfg!(test) && control_handled != 0 && started.elapsed() >= CONTROL_DRAIN_TIME_SLICE
            {
                control_limited = true;
                break;
            }
            let event = match self.pending_control_event.take() {
                Some(event) => event,
                None => match self.rx.try_recv() {
                    Ok(event) => event,
                    Err(_) => {
                        // An empty channel may simply mean the round-robin
                        // cursor visited an empty producer while another port
                        // retains completions. Give all three sources one fair
                        // nonblocking flush before declaring the owner idle.
                        self.flush_all_completion_sources();
                        match self.rx.try_recv() {
                            Ok(event) => event,
                            Err(_) => break,
                        }
                    }
                },
            };
            if let AcquisitionEvent::ReadCompleted(first) = event {
                let mut completions = Vec::with_capacity(CONTROL_EVENT_QUEUE_CAPACITY);
                completions.push(first);
                while completions.len() < 512 {
                    match self.rx.try_recv() {
                        Ok(AcquisitionEvent::ReadCompleted(completion)) => {
                            completions.push(completion);
                        }
                        Ok(other) => {
                            self.pending_control_event = Some(other);
                            break;
                        }
                        Err(_) => break,
                    }
                }
                handled += completions.len();
                control_handled += completions.len();
                self.handle_read_batch(completions);
                self.flush_next_completion_source();
                continue;
            }
            if matches!(
                &event,
                AcquisitionEvent::TimerFired {
                    timer: acquisition::TimerKind::AcquireTimeout,
                    ..
                }
            ) {
                // Ledger-data jobs admitted before this deadline must have an
                // opportunity to publish useful-node progress before the
                // timeout consumes a no-progress interval. The two bounded
                // channels cannot otherwise preserve rippled's serialized
                // ledger-data/timer ordering. Keep every other control fact
                // ahead of packet ingress.
                let drained = self.drain_packet_events(PACKET_INGRESS_QUEUE_CAPACITY);
                handled += drained;
                packets_handled += drained;
                packet_limited |= drained == PACKET_INGRESS_QUEUE_CAPACITY;
            }
            handled += 1;
            control_handled += 1;
            self.handle_fact(event);
            self.flush_next_completion_source();
        }
        self.flush_next_completion_source();
        let packet_tail = PACKET_EVENTS_PER_DRAIN
            .min(PACKET_INGRESS_QUEUE_CAPACITY.saturating_sub(packets_handled));
        let drained = self.drain_packet_events(packet_tail);
        handled += drained;
        packet_limited |= packet_tail != 0 && drained == packet_tail;
        self.last_drain_has_more = control_limited
            || control_handled >= CONTROL_EVENTS_PER_DRAIN
            || packet_limited
            || self.pending_control_event.is_some()
            || !self.priority_durable_acks.is_empty();
        handled
    }

    fn drain_packet_events(&mut self, limit: usize) -> usize {
        let mut handled = 0;
        for _ in 0..limit {
            let Ok(event) = self.packet_rx.try_recv() else {
                break;
            };
            handled += 1;
            self.handle_fact(event);
        }
        handled
    }

    /// True when the previous bounded owner slice reached a work boundary and
    /// NetworkOps should immediately run another ordinary strand iteration.
    pub(crate) const fn drain_has_more(&self) -> bool {
        self.last_drain_has_more
    }

    fn flush_next_completion_source(&mut self) {
        match self.completion_flush_cursor % 3 {
            0 => self.reads.flush_completions(),
            1 => self.writes.flush_completions(),
            _ => self.timers.flush_completions(),
        }
        self.completion_flush_cursor = (self.completion_flush_cursor + 1) % 3;
    }

    fn flush_all_completion_sources(&mut self) {
        for _ in 0..3 {
            self.flush_next_completion_source();
        }
    }

    /// Enqueue a fact only for deterministic adapter tests. Production owner
    /// facts use `handle_fact`; cross-thread control producers use a retained
    /// nonblocking port rather than this potentially blocking test helper.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn push(&self, event: AcquisitionEvent) {
        match event {
            AcquisitionEvent::PacketAdmitted(packet) => {
                match self
                    .packet_tx
                    .try_send(AcquisitionEvent::PacketAdmitted(packet))
                {
                    Ok(()) => {}
                    Err(mpsc::TrySendError::Full(AcquisitionEvent::PacketAdmitted(mut packet)))
                    | Err(mpsc::TrySendError::Disconnected(AcquisitionEvent::PacketAdmitted(
                        mut packet,
                    ))) => {
                        let _ = packet.settle();
                    }
                    Err(_) => unreachable!("packet queue only receives packet events"),
                }
            }
            event => {
                let _ = self.tx.send(event);
            }
        }
    }

    /// Try to enqueue a control fact without waiting for the owner that drains
    /// this bounded queue. Callers on the NetworkOps strand retain exact facts
    /// and retry them on a later turn when this reports `false`.
    pub(crate) fn try_push_control(&self, event: AcquisitionEvent) -> bool {
        !matches!(
            self.tx.try_send(event),
            Err(mpsc::TrySendError::Full(_)) | Err(mpsc::TrySendError::Disconnected(_))
        )
    }

    /// Test-only: consume queued events without dispatching them, preserving
    /// the owner-loop priority order (control before packet ingress).
    #[cfg(test)]
    pub(crate) fn pending_events(&mut self) -> Vec<AcquisitionEvent> {
        self.rx
            .try_iter()
            .chain(self.packet_rx.try_iter())
            .collect()
    }

    /// The runner's observable snapshot (counters, phase, sessions).
    pub(crate) fn snapshot(&self) -> acquisition::RunnerSnapshot {
        self.runner.snapshot()
    }

    /// True when the runner retained a latest consensus demand because all
    /// non-durable capacity was occupied. The adapter uses this only to retain
    /// origin metadata for the eventual owner replay.
    pub(crate) fn has_deferred_consensus_target(&self, target: acquisition::LedgerTarget) -> bool {
        self.runner.has_deferred_consensus_target(target)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn current_validation_target(&self) -> Option<acquisition::LedgerTarget> {
        self.runner.latest_validation_target()
    }

    pub(crate) fn has_unbound_validation_recovery_target(
        &self,
        target: acquisition::LedgerTarget,
    ) -> bool {
        self.runner.has_unbound_validation_recovery_target(target)
    }

    pub(crate) fn has_validation_recovery_candidate(
        &self,
        target: acquisition::LedgerTarget,
    ) -> bool {
        self.runner.has_validation_recovery_candidate(target)
    }

    pub(crate) fn current_validation_recovery_target(&self) -> Option<acquisition::LedgerTarget> {
        self.runner.validation_recovery_target()
    }

    pub(crate) fn current_validation_recovery_candidate(
        &self,
    ) -> Option<acquisition::LedgerTarget> {
        self.runner.validation_recovery_candidate()
    }

    pub(crate) fn retains_session_origin_for_hash(&self, hash: Uint256) -> bool {
        self.runner.retains_session_origin_for_hash(hash)
    }

    /// Report a usable-peer snapshot (overlay connectivity fact).
    pub(crate) fn connectivity(&mut self, snapshot: &[OverlayPeerId]) -> Vec<AcquisitionEffect> {
        for target in self.runner.active_targets() {
            if let Some(peers) = self.requests.peer_target_capabilities(target) {
                self.runner.update_target_peer_capabilities(target, peers);
            }
        }
        let peers = snapshot
            .iter()
            .map(|&id| PeerId::new(u64::from(id)))
            .collect::<Vec<_>>();
        self.handle_fact(AcquisitionEvent::Connectivity(
            PeerAvailabilitySnapshot::new(peers),
        ))
    }

    /// Report an acquisition-transport snapshot without changing the public
    /// or coordinator operating phase.
    pub(crate) fn transport_connectivity(
        &mut self,
        snapshot: &[OverlayPeerId],
    ) -> Vec<AcquisitionEffect> {
        for target in self.runner.active_targets() {
            if let Some(peers) = self.requests.peer_target_capabilities(target) {
                self.runner.update_target_peer_capabilities(target, peers);
            }
        }
        let peers = snapshot
            .iter()
            .map(|&id| PeerId::new(u64::from(id)))
            .collect::<Vec<_>>();
        self.handle_fact(AcquisitionEvent::TransportConnectivity(
            PeerAvailabilitySnapshot::new(peers),
        ))
    }

    pub(crate) fn consensus_quorum_lost(&mut self) -> Vec<AcquisitionEffect> {
        self.handle_fact(AcquisitionEvent::ConsensusQuorumLost)
    }

    pub(crate) fn consensus_quorum_available(&mut self) -> Vec<AcquisitionEffect> {
        self.handle_fact(AcquisitionEvent::ConsensusQuorumAvailable)
    }

    /// Report an acquisition demand fact.
    pub(crate) fn acquire_requested(
        &mut self,
        target: acquisition::LedgerTarget,
        reason: acquisition::AcquireReason,
    ) -> Vec<AcquisitionEffect> {
        if let Some(peers) = self.requests.peer_target_capabilities(target) {
            self.runner.update_target_peer_capabilities(target, peers);
        }
        self.handle_fact(AcquisitionEvent::AcquireRequested { target, reason })
    }

    /// Request the newest trusted-validation ledger needed by `GetConsL2`.
    /// This starts/reuses consensus-priority cache work without changing the
    /// coordinator service phase or preferred-LCL target.
    pub(crate) fn validation_target(
        &mut self,
        target: acquisition::LedgerTarget,
    ) -> Vec<AcquisitionEffect> {
        if let Some(peers) = self.requests.peer_target_capabilities(target) {
            self.runner.update_target_peer_capabilities(target, peers);
        }
        self.handle_fact(AcquisitionEvent::ValidationTarget(target))
    }

    /// Observe the accepted-boundary validation-recovery candidate. The
    /// runner latches the first exact target phase-neutrally; `None` withdraws
    /// only a future candidate.
    pub(crate) fn validation_recovery_target(
        &mut self,
        target: Option<acquisition::LedgerTarget>,
    ) -> Vec<AcquisitionEffect> {
        if let Some(target) = target
            && let Some(peers) = self.requests.peer_target_capabilities(target)
        {
            self.runner.update_target_peer_capabilities(target, peers);
        }
        self.handle_fact(AcquisitionEvent::ValidationRecoveryTarget(target))
    }

    /// Report the authoritative preferred-LCL target selected by NetworkOps
    /// `checkLastClosedLedger`. This is the sole event that may select the
    /// active consensus permit; ordinary consensus acquires remain demand-only.
    pub(crate) fn consensus_target(
        &mut self,
        target: acquisition::LedgerTarget,
    ) -> Vec<AcquisitionEffect> {
        if let Some(peers) = self.requests.peer_target_capabilities(target) {
            self.runner.update_target_peer_capabilities(target, peers);
        }
        self.handle_fact(AcquisitionEvent::ConsensusTarget(
            acquisition::ConsensusTarget::new(target, acquisition::AcquireReason::Consensus),
        ))
    }

    /// Report rippled's mode-only `consensusViewChange`. This demotes
    /// `Tracking/Full -> Connected` without selecting an acquisition target.
    pub(crate) fn consensus_view_change(&mut self) -> Vec<AcquisitionEffect> {
        self.handle_fact(AcquisitionEvent::ConsensusViewChange)
    }

    /// Report a target-bearing preferred-LCL divergence fact from the
    /// serialized `checkLastClosedLedger` path.
    /// Demotes `Connected/Tracking/Full -> Syncing { target }` without minting a
    /// session; the missing/incomplete path reports its own `acquire_requested`
    /// demand, and a resident-and-compatible switch performs no peer fetch.
    pub(crate) fn preferred_lcl_divergence(
        &mut self,
        target: acquisition::LedgerTarget,
    ) -> Vec<AcquisitionEffect> {
        self.handle_fact(AcquisitionEvent::PreferredLclDivergence { target })
    }

    /// Report a no-consensus-positions fact (Quaxar-specific). Demotes
    /// `Full -> Connected` when consensus accepted a round with no usable peer
    /// positions; no session and no target are named.
    pub(crate) fn blocked_with_no_target(&mut self) -> Vec<AcquisitionEffect> {
        self.handle_fact(AcquisitionEvent::BlockedWithNoTarget)
    }

    /// Route a wire `TmLedgerData` reply through the cloneable immutable
    /// ingress capability. The production overlay holds that capability
    /// independently, so an inline reply cannot re-enter this mutable owner.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn route_ledger_data(
        &self,
        peer_id: OverlayPeerId,
        message: &overlay::TmLedgerData,
    ) -> LedgerDataIngressDisposition {
        self.ingress.route_ledger_data(peer_id, message)
    }

    /// Stash a `TMGetObjectByHash` reply into the fetch-pack cache. By-hash
    /// replies never carry node ids and never enter a session mailbox; the
    /// SHAMap sync filter consumes them by hash during traversal (rippled
    /// `addFetchPack` parity). Wiring to overlay ingress lands with M6-C.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn stash_fetch_pack(&self, hash: Uint256, data: Bytes) {
        self.ingress
            .stats
            .lock()
            .expect("adapter stats lock")
            .fetch_pack_stashes += 1;
        self.fetch_pack.add_fetch_pack(hash, data.to_vec());
    }

    /// Observe terminal effects after the runner has applied the event. The
    /// effect identifies the one session that changed; the runner remains the
    /// sole owner that decides whether it is a failure or a cancellation.
    fn note_terminal_failures(&mut self, effects: &[AcquisitionEffect]) {
        for session in effects.iter().filter_map(|effect| match effect {
            AcquisitionEffect::CancelSession(session) => Some(*session),
            _ => None,
        }) {
            if self
                .runner
                .session(session)
                .is_some_and(|state| matches!(state.phase(), SessionPhase::Failed { .. }))
            {
                self.terminal_failures.insert(session.target_hash());
            }
        }
    }

    fn observe_shadow_result(
        &mut self,
        reference_session: Option<SessionRef>,
        effects: &[AcquisitionEffect],
    ) {
        self.shadow.observe_effects(effects);
        if let Some(session) = reference_session {
            self.compare_shadow_session(session);
        }
        self.compare_shadow_effect_sessions(effects);
    }

    fn reconcile_exact_read_priorities(&mut self) {
        let recovery = self.runner.recovery_anchor_session();
        if recovery != self.promoted_recovery_read_owner {
            if let Some(session) = recovery {
                self.reads.promote_session_priority(session);
            }
            self.promoted_recovery_read_owner = recovery;
        }
        let validation = self.runner.validation_recovery_session();
        if validation != self.promoted_validation_read_owner {
            if let Some(session) = validation {
                self.reads.promote_session_priority(session);
            }
            self.promoted_validation_read_owner = validation;
        }
    }

    fn compare_shadow_effect_sessions(&mut self, effects: &[AcquisitionEffect]) {
        let sessions = effects
            .iter()
            .filter_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session)
                | AcquisitionEffect::CancelSession(session) => Some(*session),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        for session in sessions {
            self.compare_shadow_session(session);
        }
    }

    fn compare_shadow_session(&mut self, session: SessionRef) {
        let Some(production) = self.runner.session(session) else {
            return;
        };
        let outcome = match production.phase() {
            SessionPhase::Complete => Some(ShadowOutcome::Durable),
            SessionPhase::Failed { reason } => Some(ShadowOutcome::Failed { reason: *reason }),
            SessionPhase::Cancelled { reason } => {
                Some(ShadowOutcome::Cancelled { reason: *reason })
            }
            SessionPhase::Active
            | SessionPhase::Dormant
            | SessionPhase::Persisting
            | SessionPhase::DurablePending => None,
        };
        self.shadow.compare_reference(&ReferenceDecision::new(
            session,
            Some(*self.runner.phase()),
            outcome,
            Some(production.target().hash()),
            production.packet_count() as usize,
        ));
    }

    /// Publish a fresh immutable routing snapshot reflecting the runner's live
    /// (non-terminal) sessions. Gates are cached per session: rebuilding a gate
    /// while its session still has in-flight leases would double-admit those
    /// leases on the next lookup.
    fn refresh_routes(&mut self) {
        let live = self
            .runner
            .live_sessions()
            .map(|session| (session.target_hash(), session))
            .collect::<BTreeMap<_, _>>();
        let mut changed = false;
        self.routes.retain(|hash, entry| {
            let keep = live
                .get(hash)
                .is_some_and(|session| entry.session() == *session);
            if !keep {
                changed = true;
            }
            keep
        });
        for (hash, session) in live {
            if let std::collections::btree_map::Entry::Vacant(entry) = self.routes.entry(hash) {
                entry.insert(RouteEntry::new(
                    session,
                    Arc::new(AdmissionGate::new(AdmissionBudget::default(), session)),
                ));
                changed = true;
            }
        }
        if changed {
            self.publish_routing();
        }
    }

    fn publish_routing(&mut self) {
        self.routing_generation += 1;
        *self
            .ingress
            .routing_snapshot
            .write()
            .expect("coordinator routing snapshot write") = Arc::new(RoutingSnapshot::new(
            RoutingGeneration::new(self.routing_generation),
            self.routes.clone(),
        ));
    }

    fn dispatch(&mut self, effects: &[AcquisitionEffect]) {
        if effects.is_empty() {
            return;
        }
        let mut ports = CoordinatorPorts {
            requests: &mut self.requests,
            reads: &mut self.reads,
            writes: &mut self.writes,
            timers: &mut self.timers,
            handoffs: &mut self.handoffs,
            phase: &mut self.phase,
            cancellations: &mut self.cancellations,
        };
        for effect in effects {
            ports.dispatch(effect.clone());
        }
    }
}

fn event_session(event: &AcquisitionEvent) -> Option<SessionRef> {
    match event {
        AcquisitionEvent::PacketAdmitted(packet) => Some(packet.lease().session()),
        AcquisitionEvent::ReadCompleted(completion) => Some(completion.operation().session()),
        AcquisitionEvent::WriteCompleted(completion) => Some(completion.operation().session()),
        AcquisitionEvent::DurabilityFenced(completion) => Some(completion.operation().session()),
        AcquisitionEvent::DurableHandoffAcknowledged(acknowledgement) => {
            Some(acknowledgement.session())
        }
        AcquisitionEvent::DurableHandoffRejected { session, .. } => Some(*session),
        AcquisitionEvent::TimerFired { operation, .. } => Some(operation.session()),
        AcquisitionEvent::StartupMode { .. }
        | AcquisitionEvent::Connectivity(_)
        | AcquisitionEvent::TransportConnectivity(_)
        | AcquisitionEvent::ConsensusQuorumLost
        | AcquisitionEvent::ConsensusQuorumAvailable
        | AcquisitionEvent::AcquireRequested { .. }
        | AcquisitionEvent::ValidationTarget(_)
        | AcquisitionEvent::ValidationRecoveryTarget(_)
        | AcquisitionEvent::ConsensusTarget(_)
        | AcquisitionEvent::ConsensusViewChange
        | AcquisitionEvent::PreferredLclDivergence { .. }
        | AcquisitionEvent::PreferredLclReconciled { .. }
        | AcquisitionEvent::BlockedWithNoTarget
        | AcquisitionEvent::LclInstalled(_)
        | AcquisitionEvent::PublicationCommitted { .. }
        | AcquisitionEvent::StoreRotated(_)
        | AcquisitionEvent::FetchPackAvailable
        | AcquisitionEvent::Heartbeat
        | AcquisitionEvent::RegistrySweep
        | AcquisitionEvent::Shutdown => None,
    }
}

/// Maps a wire `TmLedgerData.r#type` to the packet type. Values match the
/// protobuf `liBASE`/`liTX_NODE`/`liAS_NODE` constants.
fn map_wire_ledger_type(value: i32) -> Option<InboundLedgerDataType> {
    match value {
        0 => Some(InboundLedgerDataType::Base),
        1 => Some(InboundLedgerDataType::TransactionNode),
        2 => Some(InboundLedgerDataType::StateNode),
        _ => None,
    }
}

/// Decodes one wire ledger node with rippled-compatible legacy or
/// `LedgerNodeDepth` reference validation. Base packets reject all references.
fn decode_wire_ledger_node(
    node: &overlay::message::wire::TmLedgerNode,
    packet_type: InboundLedgerDataType,
    packet_index: usize,
) -> Option<InboundLedgerNodeData> {
    super::wire_ledger_node::decode_wire_ledger_node(node, packet_type, packet_index)
}

/// Frames a coordinator peer request exactly like the acquisition actor framed
/// it. Separated from the port so tests assert framing deterministically.
fn frame_ledger_request(
    sequences: &BTreeMap<SessionRef, u32>,
    request: &PeerRequest,
) -> Option<ProtocolMessage> {
    let session = request.session();
    match request.request() {
        LedgerDataRequest::GetLedger { sequence } => Some(make_get_ledger_with_node_ids(
            SHAMapHash::new(session.target_hash()),
            sequence.unwrap_or(0),
            LI_BASE,
            &[],
            0,
            None,
        )),
        LedgerDataRequest::GetLedgerNodes {
            kind,
            node_ids,
            sequence,
            query_depth,
            indirect,
        } => Some(make_get_ledger_with_node_ids(
            SHAMapHash::new(session.target_hash()),
            *sequence,
            match kind {
                ledger::TreeKind::State => LI_AS_NODE,
                ledger::TreeKind::Transaction => LI_TX_NODE,
            },
            node_ids,
            *query_depth,
            indirect.then_some(QT_INDIRECT),
        )),
        LedgerDataRequest::GetNodes { nodes, sequence } => {
            let first = nodes.first()?;
            if nodes.iter().any(|node| node.kind() != first.kind()) {
                // TMGetObjectByHash carries one `type`; mixed tree kinds must
                // have been split by the runner and must never be filtered.
                return None;
            }
            let object_type = match first.kind() {
                ledger::TreeKind::State => InboundLedgerObjectType::StateNode,
                ledger::TreeKind::Transaction => InboundLedgerObjectType::TransactionNode,
            };
            let needed = nodes
                .iter()
                .map(|node| (object_type, node.hash()))
                .collect::<Vec<_>>();
            make_inbound_needed_by_hash_request(
                SHAMapHash::new(session.target_hash()),
                sequence
                    .or_else(|| sequences.get(&session).copied())
                    .unwrap_or(0),
                &needed,
            )
        }
    }
}

/// Overlay delivery of coordinator-produced peer requests. Frames the request
/// exactly like the actor and delivers to the targeted peer.
pub(crate) struct OverlayLedgerRequestPort {
    peers: SimplePeerSet,
    sequences: Mutex<BTreeMap<SessionRef, u32>>,
}

impl OverlayLedgerRequestPort {
    /// A port over a peer set. `SimplePeerSet` tracks availability and delivers
    /// to a specific peer by ID.
    pub(crate) fn new(peers: SimplePeerSet) -> Self {
        Self {
            peers,
            sequences: Mutex::new(BTreeMap::new()),
        }
    }

    /// Refresh the tracked peer list (overlay availability fact).
    pub(crate) fn refresh_peers(&self, peers: impl IntoIterator<Item = Arc<dyn Peer>>) {
        self.peers.refresh_peers(peers);
    }
}

impl LedgerRequestPort for OverlayLedgerRequestPort {
    fn peer_target_capabilities(
        &self,
        target: acquisition::LedgerTarget,
    ) -> Option<Vec<acquisition::PeerTargetCapability>> {
        let sequence = target.sequence().unwrap_or(0);
        Some(
            self.peers
                .available_peers()
                .into_iter()
                .filter(|peer| peer.has_ledger(target.hash(), sequence))
                .map(|peer| {
                    acquisition::PeerTargetCapability::new(
                        PeerId::new(u64::from(peer.id())),
                        peer.is_high_latency(),
                    )
                })
                .collect(),
        )
    }

    fn send_ledger_request(&mut self, request: PeerRequest) {
        {
            let mut sequences = self.sequences.lock().expect("request port sequences lock");
            if let LedgerDataRequest::GetLedger {
                sequence: Some(sequence),
            } = request.request()
            {
                sequences.insert(request.session(), *sequence);
            }
        }
        let Some(message) = frame_ledger_request(
            &self.sequences.lock().expect("request port sequences lock"),
            &request,
        ) else {
            return;
        };
        let peer_id = request.peer_id().get() as OverlayPeerId;
        // Deliver to the exact peer the coordinator selected from its current
        // availability snapshot. Coordinator sessions do not call the legacy
        // `PeerSet::add_peers` lifecycle, so `find_peer` would incorrectly
        // require an empty legacy membership set and silently drop every
        // request. The selected peer remains current-overlay availability;
        // peer-loss facts cancel its session instead of re-broadcasting.
        if let Some(peer) = self.peers.find_available_peer(peer_id) {
            self.peers.send_request(&message, Some(&peer));
        }
    }
}

/// Shared broker ticket state between the read port and the cancellation
/// dispatcher. Holds only resource-local tickets; the coordinator owns session
/// lifecycle.
#[derive(Clone, Debug, Default)]
pub(crate) struct BrokerTicketState {
    tickets: Arc<Mutex<BTreeMap<SessionRef, Vec<ReadTicket>>>>,
    capacity_backlog: Arc<Mutex<PriorityReadBacklog>>,
}

#[derive(Debug, Default)]
struct PriorityReadBacklog {
    consensus: VecDeque<ReadRequest>,
    history: VecDeque<ReadRequest>,
}

impl PriorityReadBacklog {
    fn push_back(&mut self, request: ReadRequest) {
        match request.priority() {
            ReadPriority::Consensus => self.consensus.push_back(request),
            ReadPriority::History => self.history.push_back(request),
        }
    }

    fn pop_front(&mut self) -> Option<ReadRequest> {
        self.consensus
            .pop_front()
            .or_else(|| self.history.pop_front())
    }

    fn push_front(&mut self, request: ReadRequest) {
        match request.priority() {
            ReadPriority::Consensus => self.consensus.push_front(request),
            ReadPriority::History => self.history.push_front(request),
        }
    }

    fn retain(&mut self, mut keep: impl FnMut(&ReadRequest) -> bool) {
        self.consensus.retain(&mut keep);
        self.history.retain(keep);
    }

    fn promote_session(&mut self, session: SessionRef) -> usize {
        let mut retained = VecDeque::with_capacity(self.history.len());
        let mut promoted = 0;
        while let Some(request) = self.history.pop_front() {
            if request.operation().session() == session {
                self.consensus.push_back(ReadRequest::new(
                    request.operation(),
                    request.key(),
                    request.ledger_sequence(),
                    request.store_generation(),
                    ReadPriority::Consensus,
                ));
                promoted += 1;
            } else {
                retained.push_back(request);
            }
        }
        self.history = retained;
        promoted
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.consensus.len() + self.history.len()
    }

    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.consensus.is_empty() && self.history.is_empty()
    }
}

/// Brokered NodeStore read submission backed by the shared [`NodeReadBroker`].
/// Maps the broker's typed `ReadReady` completions into coordinator
/// `ReadCompleted` events; a rejected admission reports a terminal read so a
/// plan never stalls on an in-flight read.
pub(crate) struct BrokerReadPort {
    broker: NodeReadBroker,
    tickets: BrokerTicketState,
    node_store: SHAMapStoreNodeStore,
    completions: RetainedControlEvents,
}

impl BrokerReadPort {
    /// Builds a read port over a broker, its physical NodeStore target, and
    /// the shared ticket state.
    pub(crate) fn new(
        broker: NodeReadBroker,
        tickets: BrokerTicketState,
        node_store: SHAMapStoreNodeStore,
        tx: EventSender,
    ) -> Self {
        Self {
            broker,
            tickets,
            node_store,
            completions: RetainedControlEvents::new(tx),
        }
    }

    /// Attempts one exact coordinator read. A `false` result means the broker
    /// retained neither a ticket nor a callback; callers keep the request in
    /// the port's per-priority FIFO until a real broker completion reopens
    /// capacity.
    fn try_submit(&mut self, request: ReadRequest) -> bool {
        let operation = request.operation();
        let session = operation.session();
        let key = ReadKey::new(
            *request.key().as_uint256(),
            request.ledger_sequence(),
            request.store_generation().get(),
        );
        let acquisition_id = session.session_id().get();
        let plan_id = session.plan_epoch().get();
        let sink_completions = self.completions.clone();
        let tickets = self.tickets.clone();
        let sink: ReadReadySink = Arc::new(move |ready: ReadReady| {
            if let Some(set) = tickets
                .tickets
                .lock()
                .expect("broker ticket state lock")
                .get_mut(&session)
            {
                set.retain(|ticket| *ticket != ready.ticket);
            }
            let outcome = match ready.outcome {
                BrokerReadOutcome::Found(object) => ReadOutcome::Settled {
                    node: Some(Bytes::from(object.get_data().clone())),
                },
                BrokerReadOutcome::Miss => ReadOutcome::Settled { node: None },
                BrokerReadOutcome::Cancelled => ReadOutcome::Cancelled,
                BrokerReadOutcome::Fault(_) => ReadOutcome::Settled { node: None },
            };
            sink_completions.retain(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
                operation, outcome,
            )));
        });
        match self.broker.request_with_priority(
            key,
            acquisition_id,
            plan_id,
            request.priority(),
            sink,
        ) {
            ReadAdmission::Accepted(ticket)
            | ReadAdmission::Attached(ticket)
            | ReadAdmission::Deferred(ticket) => {
                self.tickets
                    .tickets
                    .lock()
                    .expect("broker ticket state lock")
                    .entry(session)
                    .or_default()
                    .push(ticket);
                self.broker.submit_ready_to_node_store(&self.node_store);
                true
            }
            ReadAdmission::CapacityDeferred => false,
            ReadAdmission::Rejected(_) => {
                self.completions
                    .retain(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
                        operation,
                        ReadOutcome::Stale,
                    )));
                true
            }
        }
    }

    fn promote_session_priority(&mut self, session: SessionRef) -> usize {
        let retained = self
            .broker
            .promote_session_priority(session.session_id().get(), session.plan_epoch().get());
        let backlog = self
            .tickets
            .capacity_backlog
            .lock()
            .expect("broker capacity backlog lock")
            .promote_session(session);
        self.broker.submit_ready_to_node_store(&self.node_store);
        retained + backlog
    }
}

impl ReadPort for BrokerReadPort {
    fn submit_read(&mut self, request: ReadRequest) {
        if !self.try_submit(request.clone()) {
            self.tickets
                .capacity_backlog
                .lock()
                .expect("broker capacity backlog lock")
                .push_back(request);
        }
    }

    fn promote_session_priority(&mut self, session: SessionRef) -> usize {
        BrokerReadPort::promote_session_priority(self, session)
    }

    fn flush_completions(&mut self) {
        // A physical completion may admit a broker-retained successor from
        // inside the NodeStore callback. Hand that ready dispatch back to the
        // store before retrying port-owned capacity backlog.
        self.broker.submit_ready_to_node_store(&self.node_store);
        // Retry Consensus before History, preserving FIFO inside each class.
        // A still-full broker leaves the first request queued and stops; no
        // synthetic completion is generated, so capacity pressure cannot form
        // a self-waking owner loop.
        loop {
            let request = self
                .tickets
                .capacity_backlog
                .lock()
                .expect("broker capacity backlog lock")
                .pop_front();
            let Some(request) = request else { break };
            if !self.try_submit(request.clone()) {
                self.tickets
                    .capacity_backlog
                    .lock()
                    .expect("broker capacity backlog lock")
                    .push_front(request);
                break;
            }
        }
        // Reads are the high-volume producer. Never let one flush occupy the
        // whole shared lifecycle lane: the other half remains available for
        // write/fence and timer completions which unblock session state.
        self.completions
            .flush_bounded(CONTROL_EVENT_QUEUE_CAPACITY / 2);
    }
}

/// Cancellation dispatch for brokered reads. Shares [`BrokerTicketState`] with
/// the [`BrokerReadPort`] so a session cancellation releases exactly its own
/// tickets. The broker settles each cancelled ticket through its sink after the
/// broker lock is released; the coordinator ignores completions for a cancelled
/// session.
#[derive(Clone)]
pub(crate) struct BrokerCancellationDispatcher {
    broker: NodeReadBroker,
    tickets: BrokerTicketState,
    node_store: SHAMapStoreNodeStore,
}

impl BrokerCancellationDispatcher {
    /// Builds a cancellation dispatcher sharing the broker and ticket state.
    pub(crate) fn new(
        broker: NodeReadBroker,
        tickets: BrokerTicketState,
        node_store: SHAMapStoreNodeStore,
    ) -> Self {
        Self {
            broker,
            tickets,
            node_store,
        }
    }
}

impl CancellationPort for BrokerCancellationDispatcher {
    fn session_cancelled(&mut self, session: SessionRef) {
        self.tickets
            .capacity_backlog
            .lock()
            .expect("broker capacity backlog lock")
            .retain(|request| request.operation().session() != session);
        let tickets = self
            .tickets
            .tickets
            .lock()
            .expect("broker ticket state lock")
            .remove(&session)
            .unwrap_or_default()
            .into_iter()
            .collect::<Vec<_>>();
        for ticket in tickets {
            let _ = self.broker.cancel(ticket);
        }
        self.broker.submit_ready_to_node_store(&self.node_store);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ReadBrokerConfig;
    use crate::ledger::inbound_ledgers::coordinator_ports::CoordinatorTimerPort;
    use crate::ledger::inbound_ledgers::read_broker::ACQ_READS_PER_SCAN;
    use crate::ledger::inbound_ledgers::worker_pool::WorkerPool;
    use acquisition::fake::{
        FakeCancellationPort, FakeHandoffPort, FakeLedgerRequestPort, FakePhasePort, FakeReadPort,
        FakeTimerPort, FakeWritePort,
    };
    use acquisition::{
        AcquireReason, AdmissionBudget, BudgetState, IdCounter, LedgerTarget, OperationKind,
        OperationRef, PersistNode, PlanEpoch, PlanSeed, ReadPriority, ScriptedEngine, ScriptedStep,
        SessionId, SessionPersistence, StoreGeneration, StoredObjectKind, SyncPhase, TimerKind,
        TreeEngine, TreePlanId, WriteCompletion, WriteOutcome,
    };
    use overlay::TmLedgerData;
    use overlay::message::wire::TmLedgerNode;
    use shamap::node_id::{SHAMapNodeId, deserialize_shamap_node_id};
    use shamap::tree_node::SHAMapTreeNode;
    use std::collections::VecDeque;
    use std::sync::Mutex;
    use std::time::Duration;

    const SEQ: u32 = 77;

    fn session(n: u64) -> SessionRef {
        SessionRef::new(
            RunEpoch::new(1),
            SessionId::new(n),
            Uint256::from(n),
            PlanEpoch::new(1),
            StoreGeneration::new(1),
        )
    }

    fn target(hash: u64, seq: u32) -> LedgerTarget {
        LedgerTarget::new(Uint256::from(hash), Some(seq))
    }

    fn fetch_pack() -> Arc<FetchPackCache> {
        Arc::new(FetchPackCache::new(
            1024,
            time::Duration::seconds(600),
            basics::tagged_cache::MonotonicClock::default(),
        ))
    }

    fn runner() -> CoordinatorRunner {
        CoordinatorRunner::new(RunEpoch::new(1))
    }

    type TestAdapter = CoordinatorAdapter<
        FakeLedgerRequestPort,
        FakeReadPort,
        FakeWritePort,
        FakeTimerPort,
        FakeHandoffPort,
        FakePhasePort,
        FakeCancellationPort,
    >;

    #[derive(Clone)]
    struct InlineReplyRequestPort {
        ingress: Arc<Mutex<Option<CoordinatorIngress>>>,
        dispositions: Arc<Mutex<Vec<LedgerDataIngressDisposition>>>,
    }

    impl LedgerRequestPort for InlineReplyRequestPort {
        fn send_ledger_request(&mut self, request: PeerRequest) {
            let reply = wire_ledger_data(
                request.session().target_hash(),
                LI_BASE,
                vec![(None, vec![1, 2, 3])],
            );
            let disposition = self
                .ingress
                .lock()
                .expect("inline ingress slot lock")
                .as_ref()
                .expect("ingress is published before dispatch")
                .route_ledger_data(request.peer_id().get() as OverlayPeerId, &reply);
            self.dispositions
                .lock()
                .expect("inline reply dispositions lock")
                .push(disposition);
        }
    }

    type InlineReplyAdapter = CoordinatorAdapter<
        InlineReplyRequestPort,
        FakeReadPort,
        FakeWritePort,
        FakeTimerPort,
        FakeHandoffPort,
        FakePhasePort,
        FakeCancellationPort,
    >;

    #[derive(Clone)]
    struct SaturatingReadPort {
        completions: RetainedControlEvents,
    }

    impl ReadPort for SaturatingReadPort {
        fn submit_read(&mut self, _request: ReadRequest) {}

        fn flush_completions(&mut self) {
            // Model a permanently ready read producer. With a fixed
            // reads-before-timers flush order, this event takes every newly
            // freed control slot and the expiry can never enter the owner lane.
            self.completions.push(AcquisitionEvent::Heartbeat);
        }
    }

    fn adapter() -> (TestAdapter, Arc<FetchPackCache>) {
        adapter_with_shadow(ShadowConfig::disabled())
    }

    fn adapter_with_shadow(shadow_config: ShadowConfig) -> (TestAdapter, Arc<FetchPackCache>) {
        let cache = fetch_pack();
        let runner = runner();
        let (tx, rx) = std::sync::mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let (packet_tx, packet_rx) = std::sync::mpsc::sync_channel(PACKET_INGRESS_QUEUE_CAPACITY);
        let adapter = TestAdapter::with_event_channel(
            runner,
            shadow_config,
            FakeLedgerRequestPort::new(),
            FakeReadPort::new(),
            FakeWritePort::new(),
            FakeTimerPort::new(),
            FakeHandoffPort::new(),
            FakePhasePort::new(),
            FakeCancellationPort::new(),
            Arc::clone(&cache),
            tx,
            rx,
            packet_tx,
            packet_rx,
        );
        (adapter, cache)
    }

    #[test]
    fn bounded_read_flush_reserves_control_lane_for_retained_write_completion() {
        let (tx, rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let reads = RetainedControlEvents::new(tx.clone());
        let writes = RetainedControlEvents::new(tx);

        for _ in 0..CONTROL_EVENT_QUEUE_CAPACITY * 2 {
            reads.retain(AcquisitionEvent::Heartbeat);
        }
        writes.retain(AcquisitionEvent::Shutdown);

        reads.flush_bounded(CONTROL_EVENT_QUEUE_CAPACITY / 2);
        writes.flush();

        for index in 0..CONTROL_EVENT_QUEUE_CAPACITY / 2 {
            assert!(
                matches!(rx.try_recv(), Ok(AcquisitionEvent::Heartbeat)),
                "read completion #{index} preserves FIFO order"
            );
        }
        assert!(
            matches!(rx.try_recv(), Ok(AcquisitionEvent::Shutdown)),
            "a retained write/fence lifecycle fact must enter the reserved lane"
        );
        assert_eq!(
            reads
                .pending
                .lock()
                .expect("retained read completions")
                .len(),
            CONTROL_EVENT_QUEUE_CAPACITY * 3 / 2,
            "excess reads remain owned for the next bounded owner turn"
        );
    }

    #[derive(Debug)]
    struct IncrementalPersistenceSeed;

    impl PlanSeed for IncrementalPersistenceSeed {
        fn build(
            &mut self,
            _session: SessionRef,
            _header: &ledger::InboundLedgerPacket,
        ) -> Option<Box<dyn TreeEngine + Send + Sync>> {
            Some(Box::new(
                ScriptedEngine::new(
                    TreePlanId::new(1),
                    [ScriptedStep::NeedsNetwork(vec![(
                        SHAMapNodeId::default(),
                        Uint256::from(0x9001),
                    )])],
                    vec![PersistNode::new(
                        SHAMapHash::new(Uint256::from(0x9002)),
                        bytes::Bytes::from_static(b"accepted-node"),
                        StoredObjectKind::AccountNode,
                    )],
                )
                .with_persistence_sequence(SEQ),
            ))
        }
    }

    #[derive(Debug)]
    struct DurableCompletionSeed {
        ledger: Arc<ledger::Ledger>,
    }

    impl PlanSeed for DurableCompletionSeed {
        fn build(
            &mut self,
            _session: SessionRef,
            _header: &ledger::InboundLedgerPacket,
        ) -> Option<Box<dyn TreeEngine + Send + Sync>> {
            Some(Box::new(
                ScriptedEngine::new(TreePlanId::new(2), [ScriptedStep::Complete], Vec::new())
                    .with_persistence_sequence(SEQ)
                    .with_durable_ledger(Arc::clone(&self.ledger)),
            ))
        }
    }

    fn immutable_test_ledger(hash: u64) -> Arc<ledger::Ledger> {
        let mut header = ledger::LedgerHeader {
            seq: SEQ,
            ..ledger::LedgerHeader::default()
        };
        header.hash = SHAMapHash::new(Uint256::from(hash));
        let mut ledger = ledger::Ledger::new(header, false);
        ledger.set_immutable(true);
        Arc::new(ledger)
    }

    #[derive(Debug)]
    struct UsefulPacketSeed;

    impl PlanSeed for UsefulPacketSeed {
        fn build(
            &mut self,
            _session: SessionRef,
            _header: &ledger::InboundLedgerPacket,
        ) -> Option<Box<dyn TreeEngine + Send + Sync>> {
            Some(Box::new(ScriptedEngine::new(
                TreePlanId::new(1),
                [ScriptedStep::NeedsNetwork(vec![(
                    SHAMapNodeId::default(),
                    Uint256::from(0x9001),
                )])],
                Vec::new(),
            )))
        }
    }

    fn adapter_with_useful_packet_seed() -> (TestAdapter, Arc<FetchPackCache>) {
        let cache = fetch_pack();
        let runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            BudgetState::default(),
            Box::new(UsefulPacketSeed),
        );
        let (tx, rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let (packet_tx, packet_rx) = mpsc::sync_channel(PACKET_INGRESS_QUEUE_CAPACITY);
        (
            TestAdapter::with_event_channel(
                runner,
                ShadowConfig::disabled(),
                FakeLedgerRequestPort::new(),
                FakeReadPort::new(),
                FakeWritePort::new(),
                FakeTimerPort::new(),
                FakeHandoffPort::new(),
                FakePhasePort::new(),
                FakeCancellationPort::new(),
                Arc::clone(&cache),
                tx,
                rx,
                packet_tx,
                packet_rx,
            ),
            cache,
        )
    }

    #[test]
    fn write_completion_reaches_incremental_plan_before_retained_reads_drain() {
        let cache = fetch_pack();
        let runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            BudgetState::default(),
            Box::new(IncrementalPersistenceSeed),
        );
        let (tx, rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let (packet_tx, packet_rx) = mpsc::sync_channel(PACKET_INGRESS_QUEUE_CAPACITY);
        let mut adapter = TestAdapter::with_event_channel(
            runner,
            ShadowConfig::disabled(),
            FakeLedgerRequestPort::new(),
            FakeReadPort::new(),
            FakeWritePort::new(),
            FakeTimerPort::new(),
            FakeHandoffPort::new(),
            FakePhasePort::new(),
            FakeCancellationPort::new(),
            Arc::clone(&cache),
            tx.clone(),
            rx,
            packet_tx,
            packet_rx,
        );

        adapter.connectivity(&[1]);
        let live_session = adapter
            .acquire_requested(target(9, SEQ), AcquireReason::Consensus)
            .into_iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(session),
                _ => None,
            })
            .expect("session");
        assert_eq!(
            adapter.route_ledger_data(
                1,
                &wire_ledger_data(Uint256::from(9), 0, vec![(None, base_root_wire())]),
            ),
            LedgerDataIngressDisposition::Delivered
        );
        assert_eq!(adapter.drain(), 1);
        let write = adapter.writes.submitted[0].operation();
        assert!(matches!(
            adapter
                .runner
                .session(live_session)
                .expect("session")
                .plan()
                .persistence(),
            SessionPersistence::IncrementalWritePending { .. }
        ));

        let reads = RetainedControlEvents::new(tx.clone());
        let writes = RetainedControlEvents::new(tx);
        let stale_read = OperationRef::new(
            session(999),
            OperationKind::Read,
            acquisition::OperationId::new(1),
            acquisition::OperationGeneration::new(1),
        );
        for _ in 0..CONTROL_EVENT_QUEUE_CAPACITY * 2 {
            reads.retain(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
                stale_read,
                ReadOutcome::Stale,
            )));
        }
        writes.retain(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            write,
            WriteOutcome::Accepted,
        )));
        reads.flush_bounded(CONTROL_EVENT_QUEUE_CAPACITY / 2);
        writes.flush();

        adapter.drain();
        assert!(matches!(
            adapter
                .runner
                .session(live_session)
                .expect("session")
                .plan()
                .persistence(),
            SessionPersistence::None
        ));
        assert_eq!(
            reads.pending.lock().expect("retained reads").len(),
            CONTROL_EVENT_QUEUE_CAPACITY * 3 / 2,
            "write acknowledgement resumes the plan before the read backlog drains"
        );
    }

    #[test]
    fn processed_handoff_receipt_waits_for_exact_ack_after_control_backpressure() {
        let cache = fetch_pack();
        let runner = CoordinatorRunner::with_plan_seed(
            RunEpoch::new(1),
            BudgetState::default(),
            Box::new(DurableCompletionSeed {
                ledger: immutable_test_ledger(9),
            }),
        );
        let (tx, rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let (packet_tx, packet_rx) = mpsc::sync_channel(PACKET_INGRESS_QUEUE_CAPACITY);
        let read_completions = RetainedControlEvents::new(tx.clone());
        let mut adapter = CoordinatorAdapter::with_event_channel(
            runner,
            ShadowConfig::disabled(),
            FakeLedgerRequestPort::new(),
            SaturatingReadPort {
                completions: read_completions.clone(),
            },
            FakeWritePort::new(),
            FakeTimerPort::new(),
            FakeHandoffPort::new(),
            FakePhasePort::new(),
            FakeCancellationPort::new(),
            Arc::clone(&cache),
            tx,
            rx,
            packet_tx,
            packet_rx,
        );

        adapter.connectivity(&[1]);
        let session = adapter
            .acquire_requested(target(9, SEQ), AcquireReason::Consensus)
            .into_iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(session),
                _ => None,
            })
            .expect("session");
        assert_eq!(
            adapter.route_ledger_data(
                1,
                &wire_ledger_data(Uint256::from(9), 0, vec![(None, base_root_wire())]),
            ),
            LedgerDataIngressDisposition::Delivered
        );
        assert!(
            adapter.drain() >= 1,
            "the packet and continuously ready producer both make progress"
        );
        let batch = adapter.writes.submitted[0].clone();
        adapter.handle_fact(AcquisitionEvent::WriteCompleted(WriteCompletion::new(
            batch.operation(),
            WriteOutcome::Accepted,
        )));
        adapter.handle_fact(AcquisitionEvent::DurabilityFenced(
            acquisition::DurabilityCompletion::new(
                batch.fence().expect("final fence"),
                acquisition::DurabilityOutcome::Passed,
            ),
        ));
        let published = adapter.handoffs.published[0].clone();
        assert_eq!(published.session(), session);

        while adapter.try_push_control(AcquisitionEvent::Heartbeat) {}
        assert!(
            !adapter.try_push_control(AcquisitionEvent::DurableHandoffAcknowledged(
                acquisition::DurableHandoffAcknowledgement::new(published.handoff(), session,),
            )),
            "the shared control lane is saturated"
        );
        assert!(
            adapter.retain_durable_handoff_ack(published.handoff(), session),
            "production acknowledgement retention bypasses shared-lane starvation"
        );
        assert!(
            adapter.take_processed_durable_acks().is_empty(),
            "retention is still not coordinator processing"
        );

        adapter.drain();
        assert_eq!(
            adapter.take_processed_durable_acks(),
            vec![(published.handoff(), session)],
            "the priority acknowledgement is processed before the ready producer refills slots"
        );
        assert_eq!(
            adapter
                .runner
                .session(session)
                .expect("retained session")
                .phase(),
            &SessionPhase::Complete
        );
    }

    #[test]
    fn disabled_shadow_is_a_no_op_on_the_live_owner_path() {
        let (mut adapter, _) = adapter();
        adapter.connectivity(&[1]);
        adapter.acquire_requested(target(9, SEQ), AcquireReason::Consensus);

        let snapshot = adapter.shadow_snapshot();
        assert!(!snapshot.enabled());
        assert_eq!(snapshot.mirror_sessions(), 0);
        assert!(adapter.drain_shadow_observations().is_empty());
    }

    #[test]
    fn live_owner_drives_shadow_events_effect_identity_and_reference_comparison() {
        let (mut adapter, _) = adapter_with_shadow(ShadowConfig::default());
        adapter.connectivity(&[1]);
        let started = adapter.acquire_requested(target(9, SEQ), AcquireReason::Consensus);
        let session = started
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("production session start is visible to the shadow probe");
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
            .expect("new acquisition probes the local header");
        let mut expiry = started
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::ArmTimer(request)
                    if request.timer() == TimerKind::SessionExpiry =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("production expiry identity is observed");

        let read_effects = adapter.handle_fact(AcquisitionEvent::ReadCompleted(
            ReadCompletion::new(header_read, ReadOutcome::Settled { node: None }),
        ));
        if let Some(rearmed) = read_effects.iter().find_map(|effect| match effect {
            AcquisitionEffect::ArmTimer(request) if request.timer() == TimerKind::SessionExpiry => {
                Some(request.operation())
            }
            _ => None,
        }) {
            expiry = rearmed;
        }
        adapter.handle_fact(AcquisitionEvent::TimerFired {
            operation: expiry,
            timer: TimerKind::SessionExpiry,
        });
        adapter.handle_fact(AcquisitionEvent::RegistrySweep);

        assert!(adapter.runner.session(session).is_none());
        assert_eq!(adapter.cancellations.cancelled, vec![session]);
        let snapshot = adapter.shadow_snapshot();
        assert!(snapshot.enabled());
        assert_eq!(snapshot.mirror_sessions(), 1);
        let observations = adapter.drain_shadow_observations();
        assert_eq!(snapshot.stale_events(), 0, "{observations:#?}");
        assert_eq!(snapshot.disagreements(), 0, "{observations:#?}");
        assert!(snapshot.matches() > 0);
    }

    #[test]
    fn production_timer_port_delivers_session_expiry_through_adapter_owner_loop() {
        type TimerAdapter = CoordinatorAdapter<
            FakeLedgerRequestPort,
            FakeReadPort,
            FakeWritePort,
            CoordinatorTimerPort,
            FakeHandoffPort,
            FakePhasePort,
            FakeCancellationPort,
        >;

        let cache = fetch_pack();
        let runner = CoordinatorRunner::with_budget(
            RunEpoch::new(1),
            BudgetState::new(
                usize::MAX,
                AdmissionBudget::default(),
                Duration::from_secs(120),
            ),
        );
        let pool = Arc::new(WorkerPool::new_with_manual_timer_for_test(0));
        let (tx, rx) = std::sync::mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let (packet_tx, packet_rx) = std::sync::mpsc::sync_channel(PACKET_INGRESS_QUEUE_CAPACITY);
        let timers = CoordinatorTimerPort::new(Arc::clone(&pool), tx.clone());
        let mut adapter = TimerAdapter::with_event_channel(
            runner,
            ShadowConfig::disabled(),
            FakeLedgerRequestPort::new(),
            FakeReadPort::new(),
            FakeWritePort::new(),
            timers,
            FakeHandoffPort::new(),
            FakePhasePort::new(),
            FakeCancellationPort::new(),
            Arc::clone(&cache),
            tx,
            rx,
            packet_tx,
            packet_rx,
        );

        adapter.connectivity(&[1]);
        let effects = adapter.acquire_requested(target(9, SEQ), AcquireReason::Consensus);
        let session = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("acquisition starts a routed session");
        assert_eq!(
            pool.scheduled_timer_delays_for_test(),
            vec![Duration::from_secs(120), Duration::from_secs(60)]
        );

        assert_eq!(
            pool.fire_next_timer_for_test(),
            Some(Duration::from_secs(60))
        );
        assert_eq!(adapter.drain(), 1, "timer fact reaches the owner queue");
        assert_eq!(adapter.snapshot().session_count(), 1);
        adapter.handle_fact(AcquisitionEvent::RegistrySweep);
        assert_eq!(adapter.snapshot().session_count(), 0);
        assert_eq!(adapter.cancellations.cancelled, vec![session]);
        pool.stop();
    }

    #[test]
    fn saturated_read_completions_cannot_starve_session_expiry() {
        type TimerAdapter = CoordinatorAdapter<
            FakeLedgerRequestPort,
            SaturatingReadPort,
            FakeWritePort,
            CoordinatorTimerPort,
            FakeHandoffPort,
            FakePhasePort,
            FakeCancellationPort,
        >;

        let cache = fetch_pack();
        let runner = CoordinatorRunner::with_budget(
            RunEpoch::new(1),
            BudgetState::new(
                usize::MAX,
                AdmissionBudget::default(),
                Duration::from_secs(120),
            ),
        );
        let pool = Arc::new(WorkerPool::new_with_manual_timer_for_test(0));
        let (tx, rx) = std::sync::mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let (packet_tx, packet_rx) = std::sync::mpsc::sync_channel(PACKET_INGRESS_QUEUE_CAPACITY);
        let read_completions = RetainedControlEvents::new(tx.clone());
        let reads = SaturatingReadPort {
            completions: read_completions.clone(),
        };
        let timers = CoordinatorTimerPort::new(Arc::clone(&pool), tx.clone());
        let mut adapter = TimerAdapter::with_event_channel(
            runner,
            ShadowConfig::disabled(),
            FakeLedgerRequestPort::new(),
            reads,
            FakeWritePort::new(),
            timers,
            FakeHandoffPort::new(),
            FakePhasePort::new(),
            FakeCancellationPort::new(),
            Arc::clone(&cache),
            tx,
            rx,
            packet_tx,
            packet_rx,
        );

        adapter.connectivity(&[1]);
        let effects = adapter.acquire_requested(target(19, SEQ), AcquireReason::Consensus);
        let session = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("acquisition starts a routed session");
        let original_expiry = adapter
            .runner
            .session(session)
            .and_then(|state| state.pending_expiry_timer());
        for _ in 0..CONTROL_EVENT_QUEUE_CAPACITY {
            read_completions.push(AcquisitionEvent::Heartbeat);
        }
        assert_eq!(
            pool.fire_next_timer_for_test(),
            Some(Duration::from_secs(60))
        );

        adapter.drain();
        assert!(
            adapter.drain_has_more(),
            "a continuously ready completion producer must suppress the strand's idle wait"
        );
        let expiry_delivered = adapter
            .runner
            .session(session)
            .is_none_or(|state| state.pending_expiry_timer() != original_expiry);
        assert!(
            expiry_delivered,
            "round-robin completion flush must deliver expiry despite an always-ready read producer"
        );
        adapter.handle_fact(AcquisitionEvent::RegistrySweep);
        assert_eq!(adapter.snapshot().session_count(), 0);
        assert_eq!(adapter.cancellations.cancelled, vec![session]);
        pool.stop();
    }

    /// Connect and acquire a session, returning the session the coordinator
    /// minted.
    fn acquired(adapter: &mut TestAdapter) -> SessionRef {
        let effects = adapter.connectivity(&[1]);
        assert!(
            effects.contains(&AcquisitionEffect::SetServicePhase(SyncPhase::Connected)),
            "connectivity must promote to Connected"
        );
        let effects = adapter.acquire_requested(target(9, SEQ), AcquireReason::Consensus);
        effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("an acquisition session must start")
    }

    fn settle_initial_header_miss<R, RD, WR, T, H, P, C>(
        adapter: &mut CoordinatorAdapter<R, RD, WR, T, H, P, C>,
        effects: &[AcquisitionEffect],
    ) -> Vec<AcquisitionEffect>
    where
        R: LedgerRequestPort,
        RD: ReadPort,
        WR: WritePort,
        T: TimerPort,
        H: HandoffPort,
        P: PhasePort,
        C: CancellationPort,
    {
        let operation = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SubmitRead(request)
                    if request.operation().kind() == OperationKind::HeaderRead =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("new acquisition starts with an exact local header probe");
        adapter.handle_fact(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
            operation,
            ReadOutcome::Settled { node: None },
        )))
    }

    fn valid_inner_wire() -> Vec<u8> {
        let mut wire = vec![0; 16 * 32];
        wire.push(shamap::tree_node::WIRE_TYPE_INNER);
        wire
    }

    fn base_root_wire() -> Vec<u8> {
        let root = shamap::tree_node::SHAMapTreeNode::new_inner(1);
        root.set_child_hash(3, SHAMapHash::new(Uint256::from(0x73)));
        root.update_hash();
        root.serialize_for_wire().expect("root wire serializes")
    }

    fn wire_ledger_data(
        hash: Uint256,
        r#type: i32,
        nodes: Vec<(Option<Vec<u8>>, Vec<u8>)>,
    ) -> TmLedgerData {
        TmLedgerData {
            ledger_hash: hash.data().to_vec(),
            ledger_seq: SEQ,
            r#type,
            nodes: nodes
                .into_iter()
                .map(|(nodeid, nodedata)| TmLedgerNode {
                    nodedata,
                    nodeid,
                    ..TmLedgerNode::default()
                })
                .collect(),
            ..TmLedgerData::default()
        }
    }

    #[test]
    fn synchronous_reply_uses_immutable_ingress_while_request_dispatches() {
        let cache = fetch_pack();
        let (tx, rx) = std::sync::mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let (packet_tx, packet_rx) = std::sync::mpsc::sync_channel(PACKET_INGRESS_QUEUE_CAPACITY);
        let ingress = Arc::new(Mutex::new(None));
        let dispositions = Arc::new(Mutex::new(Vec::new()));
        let requests = InlineReplyRequestPort {
            ingress: Arc::clone(&ingress),
            dispositions: Arc::clone(&dispositions),
        };
        let mut adapter = InlineReplyAdapter::with_event_channel(
            runner(),
            ShadowConfig::disabled(),
            requests,
            FakeReadPort::new(),
            FakeWritePort::new(),
            FakeTimerPort::new(),
            FakeHandoffPort::new(),
            FakePhasePort::new(),
            FakeCancellationPort::new(),
            cache,
            tx,
            rx,
            packet_tx,
            packet_rx,
        );
        *ingress.lock().expect("inline ingress slot lock") = Some(adapter.ingress());

        adapter.connectivity(&[1]);
        let started = adapter.acquire_requested(target(9, SEQ), AcquireReason::Consensus);
        let effects = settle_initial_header_miss(&mut adapter, &started);
        assert!(effects.iter().any(|effect| matches!(
            effect,
            AcquisitionEffect::SendLedgerRequest(request) if request.session().target_hash() == Uint256::from(9)
        )));
        assert_eq!(
            dispositions
                .lock()
                .expect("inline reply dispositions lock")
                .as_slice(),
            &[LedgerDataIngressDisposition::Delivered],
            "an inline reply must enqueue through immutable ingress rather than re-enter the mutable owner"
        );
        assert_eq!(
            adapter.drain(),
            1,
            "the owner consumes the queued reply later"
        );
        assert_eq!(adapter.snapshot().packets_admitted(), 1);
    }

    #[test]
    fn validation_target_does_not_publish_an_operating_mode_change() {
        let (mut adapter, _cache) = adapter();
        let full = SyncPhase::Full {
            lcl: acquisition::LedgerIdentity::new(Uint256::from(40), 40),
            published: acquisition::LedgerIdentity::new(Uint256::from(40), 40),
        };
        let _ = adapter.handle_fact(AcquisitionEvent::StartupMode { phase: full });
        let _ = adapter.connectivity(&[1]);
        adapter.phase.phases.clear();

        let effects = adapter.validation_target(LedgerTarget::new(Uint256::from(99), None));

        assert_eq!(adapter.snapshot().phase(), &full);
        assert!(adapter.phase.phases.is_empty());
        assert!(
            effects
                .iter()
                .all(|effect| !matches!(effect, AcquisitionEffect::SetServicePhase(_)))
        );
        assert!(
            effects
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::SessionStarted(_)))
        );
    }

    #[test]
    fn acquire_dispatches_request_and_publishes_a_route() {
        let (mut adapter, _cache) = adapter();
        let session = acquired(&mut adapter);
        assert_eq!(
            adapter.snapshot().phase(),
            &SyncPhase::Syncing {
                target: target(9, SEQ)
            }
        );
        assert_eq!(
            adapter.snapshot().session_count(),
            1,
            "one live session must be tracked"
        );

        let snapshot = adapter.routing_snapshot();
        let route = snapshot
            .route(&Uint256::from(9))
            .expect("a route must exist for the acquired target");
        assert_eq!(route.session(), session);
    }

    #[test]
    fn preferred_lcl_divergence_demotes_tracking_without_a_session() {
        let (mut adapter, _cache) = adapter();
        let _session = acquired(&mut adapter);
        adapter.push(AcquisitionEvent::LclInstalled(
            acquisition::LedgerIdentity::new(Uint256::from(9), SEQ),
        ));
        assert_eq!(adapter.drain(), 1);
        assert_eq!(
            adapter.snapshot().phase(),
            &SyncPhase::Tracking {
                lcl: acquisition::LedgerIdentity::new(Uint256::from(9), SEQ)
            }
        );

        let effects = adapter.preferred_lcl_divergence(target(11, 11));
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                target: target(11, 11)
            })]
        );
        // A divergence fact is phase-only: it never mints a session. The
        // demand arrives as a separate acquire_requested fact.
        assert_eq!(adapter.snapshot().session_count(), 1);
        assert_eq!(
            adapter.snapshot().phase(),
            &SyncPhase::Syncing {
                target: target(11, 11)
            }
        );
    }

    #[test]
    fn consensus_view_change_demotes_tracking_without_a_target_or_session() {
        let (mut adapter, _cache) = adapter();
        let _session = acquired(&mut adapter);
        adapter.push(AcquisitionEvent::LclInstalled(
            acquisition::LedgerIdentity::new(Uint256::from(9), SEQ),
        ));
        assert_eq!(adapter.drain(), 1);

        let sessions_before = adapter.snapshot().session_count();
        let effects = adapter.consensus_view_change();
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Connected)]
        );
        assert_eq!(adapter.snapshot().phase(), &SyncPhase::Connected);
        assert_eq!(adapter.snapshot().session_count(), sessions_before);
    }

    #[test]
    fn preferred_lcl_divergence_then_acquire_mints_the_session() {
        let (mut adapter, _cache) = adapter();
        let _session = acquired(&mut adapter);
        adapter.push(AcquisitionEvent::LclInstalled(
            acquisition::LedgerIdentity::new(Uint256::from(9), SEQ),
        ));
        assert_eq!(adapter.drain(), 1);

        let effects = adapter.preferred_lcl_divergence(target(11, 11));
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Syncing {
                target: target(11, 11)
            })]
        );
        let effects = adapter.acquire_requested(target(11, 11), AcquireReason::Consensus);
        let session = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("the recovery demand must mint a session");
        assert_eq!(session.target_hash(), Uint256::from(11));
        assert_eq!(adapter.snapshot().session_count(), 2);
        assert_eq!(adapter.snapshot().rejected_events(), 0);
    }

    #[test]
    fn blocked_with_no_target_demotes_full_to_connected() {
        let (mut adapter, _cache) = adapter();
        let _session = acquired(&mut adapter);
        adapter.push(AcquisitionEvent::LclInstalled(
            acquisition::LedgerIdentity::new(Uint256::from(9), SEQ),
        ));
        adapter.push(AcquisitionEvent::PublicationCommitted {
            identity: acquisition::LedgerIdentity::new(Uint256::from(9), SEQ),
            fresh: true,
        });
        assert_eq!(adapter.drain(), 2);
        assert_eq!(
            adapter.snapshot().phase(),
            &SyncPhase::Full {
                lcl: acquisition::LedgerIdentity::new(Uint256::from(9), SEQ),
                published: acquisition::LedgerIdentity::new(Uint256::from(9), SEQ),
            }
        );

        let effects = adapter.blocked_with_no_target();
        assert_eq!(
            effects,
            vec![AcquisitionEffect::SetServicePhase(SyncPhase::Connected)]
        );
        assert_eq!(adapter.snapshot().phase(), &SyncPhase::Connected);
        assert_eq!(adapter.snapshot().session_count(), 1);
    }

    #[test]
    fn wire_ledger_data_routes_by_hash_and_preserves_node_ids() {
        let (mut adapter, _cache) = adapter();
        let session = acquired(&mut adapter);
        let snapshot = adapter.routing_snapshot();
        let gate = snapshot.route(&Uint256::from(9)).unwrap().gate().clone();

        let node_id = SHAMapNodeId::default().get_raw_string().to_vec();
        let message = wire_ledger_data(
            Uint256::from(9),
            2, // liAS_NODE
            vec![(Some(node_id.clone()), valid_inner_wire())],
        );
        let disposition = adapter.route_ledger_data(1, &message);
        assert_eq!(disposition, LedgerDataIngressDisposition::Delivered);
        assert_eq!(gate.current_packets(), 1, "admission reserves one packet");

        // The admitted packet preserves the wire node id verbatim through
        // ingress and into the owner queue.
        let mut pending = adapter.pending_events();
        assert_eq!(pending.len(), 1, "exactly one admitted packet is queued");
        let packet = match pending.remove(0) {
            AcquisitionEvent::PacketAdmitted(packet) => packet,
            other => panic!("expected an admitted packet, got {other:?}"),
        };
        assert_eq!(packet.peer_id(), PeerId::new(1));
        assert_eq!(packet.packet().nodes.len(), 1);
        assert_eq!(
            packet.packet().nodes[0].node_id.as_deref(),
            Some(node_id.as_slice()),
            "wire node ids survive into the admission packet"
        );

        // With the null plan seed the packet is retained by the session mailbox,
        // so its immutable ingress lease remains charged until terminal cleanup.
        adapter.push(AcquisitionEvent::PacketAdmitted(packet));
        assert_eq!(adapter.drain(), 1);
        assert_eq!(adapter.snapshot().packets_admitted(), 1);
        assert_eq!(
            gate.current_packets(),
            1,
            "the retained mailbox packet keeps immutable ingress admission charged"
        );
        assert_eq!(
            adapter
                .runner
                .session(session)
                .expect("live session")
                .packet_count(),
            1,
            "the packet is retained by the session mailbox (no engine seeded)"
        );
        adapter.handle_fact(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));
        assert_eq!(
            gate.current_packets(),
            0,
            "terminal cleanup settles the retained lease"
        );
    }

    #[test]
    fn missing_node_id_is_invalid_for_state_packets() {
        let (mut adapter, _cache) = adapter();
        acquired(&mut adapter);
        let message = wire_ledger_data(
            Uint256::from(9),
            2, // liAS_NODE
            vec![(None, vec![1, 2, 3])],
        );
        assert_eq!(
            adapter.route_ledger_data(1, &message),
            LedgerDataIngressDisposition::Invalid
        );
    }

    #[test]
    fn base_packets_apply_without_node_ids() {
        let (mut adapter, _cache) = adapter();
        acquired(&mut adapter);
        let message = wire_ledger_data(
            Uint256::from(9),
            0, // liBASE
            vec![(None, vec![1, 2, 3])],
        );
        assert_eq!(
            adapter.route_ledger_data(1, &message),
            LedgerDataIngressDisposition::Delivered
        );
    }

    #[test]
    fn live_base_ingress_admits_rippled_network_wire_roots_without_rewriting() {
        let (mut adapter, _cache) = adapter();
        acquired(&mut adapter);
        let expected_wire = base_root_wire();
        let message = wire_ledger_data(
            Uint256::from(9),
            0, // liBASE
            vec![(None, vec![0xAB; 123]), (None, expected_wire.clone())],
        );

        assert_eq!(
            adapter.route_ledger_data(1, &message),
            LedgerDataIngressDisposition::Delivered
        );
        let mut pending = adapter.pending_events();
        let AcquisitionEvent::PacketAdmitted(packet) = pending.remove(0) else {
            panic!("Base reply must enter coordinator as an admitted packet");
        };
        assert_eq!(packet.packet().nodes[0].node_data, vec![0xAB; 123]);
        assert_eq!(packet.packet().nodes[1].node_data, expected_wire);
        assert!(
            SHAMapTreeNode::make_from_wire(&packet.packet().nodes[1].node_data)
                .expect("rippled root decodes as network wire")
                .is_some()
        );
        adapter.push(AcquisitionEvent::PacketAdmitted(packet));
        assert_eq!(adapter.drain(), 1);
        assert_eq!(adapter.snapshot().packets_admitted(), 1);
    }

    #[test]
    fn live_base_ingress_rejects_malformed_network_wire_roots() {
        let (mut adapter, _cache) = adapter();
        acquired(&mut adapter);
        let message = wire_ledger_data(
            Uint256::from(9),
            0, // liBASE
            vec![(None, vec![0xAB; 123]), (None, vec![0xFF])],
        );
        assert_eq!(
            adapter.route_ledger_data(1, &message),
            LedgerDataIngressDisposition::Invalid
        );
        assert!(adapter.pending_events().is_empty());
    }

    #[test]
    fn failed_terminal_session_is_reported_once_for_registry_cooldown() {
        let (mut adapter, _cache) = adapter();
        adapter.connectivity(&[1]);
        let started = adapter.acquire_requested(target(9, SEQ), AcquireReason::Generic);
        let session = started
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("acquisition starts a session");
        let mut timeout = started
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::ArmTimer(request)
                    if request.timer() == TimerKind::AcquireTimeout =>
                {
                    Some(request.clone().operation())
                }
                _ => None,
            })
            .expect("acquisition arms its timeout");
        let effects = settle_initial_header_miss(&mut adapter, &started);
        assert!(effects.iter().any(|effect| matches!(
            effect,
            AcquisitionEffect::SendLedgerRequest(request) if request.session() == session
        )));

        // rippled permits six no-progress recovery intervals; only the
        // seventh exact timeout terminalizes the acquisition.
        for _ in 0..6 {
            let effects = adapter.handle_fact(AcquisitionEvent::TimerFired {
                operation: timeout,
                timer: TimerKind::AcquireTimeout,
            });
            timeout = effects
                .iter()
                .find_map(|effect| match effect {
                    AcquisitionEffect::ArmTimer(request)
                        if request.timer() == TimerKind::AcquireTimeout =>
                    {
                        Some(request.clone().operation())
                    }
                    _ => None,
                })
                .expect("pre-terminal timeout rearms with an exact new operation");
        }

        let effects = adapter.handle_fact(AcquisitionEvent::TimerFired {
            operation: timeout,
            timer: TimerKind::AcquireTimeout,
        });
        assert!(effects.contains(&AcquisitionEffect::CancelSession(session)));
        assert_eq!(
            adapter.take_terminal_failures(),
            vec![Uint256::from(9)],
            "the registry must receive the failed target once for cooldown admission"
        );
        assert!(
            adapter.take_terminal_failures().is_empty(),
            "draining terminal failures must not repeatedly extend the cooldown"
        );
    }

    fn advance_to_seventh_timeout(adapter: &mut TestAdapter) -> (SessionRef, OperationRef) {
        adapter.connectivity(&[1]);
        let started = adapter.acquire_requested(target(9, SEQ), AcquireReason::Generic);
        let session = started
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("acquisition starts a session");
        let mut timeout = started
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::ArmTimer(request)
                    if request.timer() == TimerKind::AcquireTimeout =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("acquisition arms its timeout");
        settle_initial_header_miss(adapter, &started);
        for _ in 0..6 {
            timeout = adapter
                .handle_fact(AcquisitionEvent::TimerFired {
                    operation: timeout,
                    timer: TimerKind::AcquireTimeout,
                })
                .iter()
                .find_map(|effect| match effect {
                    AcquisitionEffect::ArmTimer(request)
                        if request.timer() == TimerKind::AcquireTimeout =>
                    {
                        Some(request.operation())
                    }
                    _ => None,
                })
                .expect("sixth no-progress timeout still rearms");
        }
        assert_eq!(
            adapter.runner.session(session).unwrap().plan().timeouts(),
            6
        );
        (session, timeout)
    }

    #[test]
    fn acquire_timeout_drains_all_admitted_packets_before_consuming_interval() {
        let (mut adapter, _cache) = adapter_with_useful_packet_seed();
        let (session, timeout) = advance_to_seventh_timeout(&mut adapter);
        let node_id = SHAMapNodeId::default().get_raw_string().to_vec();
        let ordinary = wire_ledger_data(
            Uint256::from(9),
            2,
            vec![(Some(node_id), valid_inner_wire())],
        );
        for _ in 0..PACKET_EVENTS_PER_DRAIN {
            assert_eq!(
                adapter.route_ledger_data(1, &ordinary),
                LedgerDataIngressDisposition::Delivered
            );
        }
        assert_eq!(
            adapter.route_ledger_data(
                1,
                &wire_ledger_data(Uint256::from(9), 0, vec![(None, base_root_wire())]),
            ),
            LedgerDataIngressDisposition::Delivered
        );
        adapter.push(AcquisitionEvent::TimerFired {
            operation: timeout,
            timer: TimerKind::AcquireTimeout,
        });

        assert_eq!(adapter.drain(), PACKET_EVENTS_PER_DRAIN + 2);
        let live = adapter
            .runner
            .session(session)
            .expect("useful packet keeps session live");
        assert_eq!(
            live.plan().timeouts(),
            6,
            "the useful packet beyond the ordinary packet slice resets deadline progress"
        );
    }

    #[test]
    fn acquire_timeout_after_only_non_useful_packets_still_terminalizes() {
        let (mut adapter, _cache) = adapter_with_useful_packet_seed();
        adapter.connectivity(&[1]);
        let started = adapter.acquire_requested(target(9, SEQ), AcquireReason::Generic);
        let session = started
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("acquisition starts a session");
        let mut timeout = started
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::ArmTimer(request)
                    if request.timer() == TimerKind::AcquireTimeout =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("acquisition arms its timeout");
        settle_initial_header_miss(&mut adapter, &started);
        let base = wire_ledger_data(Uint256::from(9), 0, vec![(None, base_root_wire())]);
        assert_eq!(
            adapter.route_ledger_data(1, &base),
            LedgerDataIngressDisposition::Delivered
        );
        assert_eq!(adapter.drain(), 1, "the first Base packet seeds the plan");
        timeout = adapter
            .handle_fact(AcquisitionEvent::TimerFired {
                operation: timeout,
                timer: TimerKind::AcquireTimeout,
            })
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::ArmTimer(request)
                    if request.timer() == TimerKind::AcquireTimeout =>
                {
                    Some(request.operation())
                }
                _ => None,
            })
            .expect("seed progress rearms without consuming timeout budget");
        assert_eq!(
            adapter.runner.session(session).unwrap().plan().timeouts(),
            0
        );
        for expected in 1..=6 {
            let effects = adapter.handle_fact(AcquisitionEvent::TimerFired {
                operation: timeout,
                timer: TimerKind::AcquireTimeout,
            });
            timeout = effects
                .iter()
                .find_map(|effect| match effect {
                    AcquisitionEffect::ArmTimer(request)
                        if request.timer() == TimerKind::AcquireTimeout =>
                    {
                        Some(request.operation())
                    }
                    _ => None,
                })
                .expect("six no-progress intervals remain recoverable");
            let recovery_reads = effects
                .iter()
                .filter_map(|effect| match effect {
                    AcquisitionEffect::SubmitRead(request) => Some(request.operation()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            for operation in recovery_reads {
                adapter.handle_fact(AcquisitionEvent::ReadCompleted(ReadCompletion::new(
                    operation,
                    ReadOutcome::Settled { node: None },
                )));
            }
            assert_eq!(
                adapter.runner.session(session).unwrap().plan().timeouts(),
                expected
            );
        }

        let node_id = SHAMapNodeId::default().get_raw_string().to_vec();
        let non_useful = wire_ledger_data(
            Uint256::from(9),
            2,
            vec![(Some(node_id), valid_inner_wire())],
        );
        // The valid wire node does not match the retained 0x9001 hash, so it
        // is admitted but does not earn useful-node progress.
        for _ in 0..=PACKET_EVENTS_PER_DRAIN {
            assert_eq!(
                adapter.route_ledger_data(1, &non_useful),
                LedgerDataIngressDisposition::Delivered
            );
        }
        adapter.push(AcquisitionEvent::TimerFired {
            operation: timeout,
            timer: TimerKind::AcquireTimeout,
        });

        assert_eq!(adapter.drain(), PACKET_EVENTS_PER_DRAIN + 2);
        let failed = adapter
            .runner
            .session(session)
            .expect("failed session retained");
        assert_eq!(failed.plan().timeouts(), 7);
        assert!(matches!(
            failed.phase(),
            SessionPhase::Failed {
                reason: acquisition::FailureReason::AcquisitionTimeout
            }
        ));
        assert_eq!(adapter.cancellations.cancelled, vec![session]);
    }

    #[test]
    fn unmatched_and_terminal_packets_are_never_admitted() {
        let (mut adapter, _cache) = adapter();
        acquired(&mut adapter);

        let message = wire_ledger_data(Uint256::from(99), 0, vec![(None, vec![1, 2, 3])]);
        assert_eq!(
            adapter.route_ledger_data(1, &message),
            LedgerDataIngressDisposition::Unmatched
        );

        // Store rotation terminalizes the old exact owner and drops its route.
        // Sequence metadata alone never replaces a same-hash InboundLedger.
        let effects = adapter.handle_fact(AcquisitionEvent::StoreRotated(StoreGeneration::new(2)));
        assert!(
            effects
                .iter()
                .any(|effect| matches!(effect, AcquisitionEffect::CancelSession(_)))
        );
        assert!(
            adapter
                .routing_snapshot()
                .route(&Uint256::from(9))
                .is_none()
        );
        assert_eq!(
            adapter.route_ledger_data(
                1,
                &wire_ledger_data(Uint256::from(9), 0, vec![(None, vec![1, 2, 3])],),
            ),
            LedgerDataIngressDisposition::Unmatched
        );

        let _ = adapter.acquire_requested(target(9, SEQ + 1), AcquireReason::Consensus);
        let snapshot = adapter.routing_snapshot();
        let route = snapshot
            .route(&Uint256::from(9))
            .expect("replacement route");
        assert_ne!(route.session(), session(1));
    }

    #[test]
    fn packet_ingress_queue_full_defers_and_releases_its_lease() {
        let (mut adapter, _cache) = adapter();
        acquired(&mut adapter);
        let gate = adapter
            .routing_snapshot()
            .route(&Uint256::from(9))
            .expect("live route")
            .gate()
            .clone();
        let message = wire_ledger_data(Uint256::from(9), 0, vec![(None, vec![1, 2, 3])]);

        for _ in 0..PACKET_INGRESS_QUEUE_CAPACITY {
            assert_eq!(
                adapter.route_ledger_data(1, &message),
                LedgerDataIngressDisposition::Delivered
            );
        }
        assert_eq!(gate.current_packets(), PACKET_INGRESS_QUEUE_CAPACITY as u64);

        // The next packet can reserve the per-session gate, but the bounded
        // global ingress queue rejects it. Its lease is settled immediately,
        // so it cannot become a mailbox/session side effect.
        assert_eq!(
            adapter.route_ledger_data(1, &message),
            LedgerDataIngressDisposition::Deferred
        );
        assert_eq!(gate.current_packets(), PACKET_INGRESS_QUEUE_CAPACITY as u64);
        assert_eq!(adapter.snapshot().packets_admitted(), 0);
    }

    #[test]
    fn drain_prioritizes_and_bounds_control_then_packet_work() {
        let (mut adapter, _cache) = adapter();
        acquired(&mut adapter);
        let message = wire_ledger_data(Uint256::from(9), 0, vec![(None, vec![1, 2, 3])]);
        for _ in 0..(PACKET_EVENTS_PER_DRAIN + 1) {
            assert_eq!(
                adapter.route_ledger_data(1, &message),
                LedgerDataIngressDisposition::Delivered
            );
        }
        adapter.push(AcquisitionEvent::LclInstalled(
            acquisition::LedgerIdentity::new(Uint256::from(9), SEQ),
        ));

        assert_eq!(adapter.drain(), 1 + PACKET_EVENTS_PER_DRAIN);
        assert_eq!(
            adapter.snapshot().phase(),
            &SyncPhase::Tracking {
                lcl: acquisition::LedgerIdentity::new(Uint256::from(9), SEQ)
            },
            "the queued control fact runs before the bounded packet turn"
        );
        assert_eq!(adapter.drain(), 1, "one packet remains for the next slice");
    }

    #[test]
    fn control_queue_is_bounded_and_recovers_after_a_drain_slice() {
        assert_eq!(
            CONTROL_EVENTS_PER_DRAIN, 512,
            "one owner burst matches rippled's getMissingNodes read-batch width"
        );
        let (mut adapter, _cache) = adapter();
        let events = adapter.event_sender();
        for _ in 0..CONTROL_EVENT_QUEUE_CAPACITY {
            events
                .try_send(AcquisitionEvent::LclInstalled(
                    acquisition::LedgerIdentity::new(Uint256::from(9), SEQ),
                ))
                .expect("reserved control capacity");
        }
        assert!(matches!(
            events.try_send(AcquisitionEvent::LclInstalled(
                acquisition::LedgerIdentity::new(Uint256::from(9), SEQ),
            )),
            Err(mpsc::TrySendError::Full(_))
        ));

        assert_eq!(adapter.drain(), CONTROL_EVENT_QUEUE_CAPACITY);
        assert!(
            !adapter.drain_has_more(),
            "draining a sub-burst channel completely may return to the normal strand wait"
        );
        events
            .try_send(AcquisitionEvent::LclInstalled(
                acquisition::LedgerIdentity::new(Uint256::from(9), SEQ),
            ))
            .expect("draining restores reserved lifecycle capacity");
    }

    #[test]
    fn deferred_packet_has_no_actor_side_effect() {
        let (mut adapter, _cache) = adapter();
        acquired(&mut adapter);
        let snapshot = adapter.routing_snapshot();
        let gate = snapshot.route(&Uint256::from(9)).unwrap().gate().clone();

        // Fill the gate's packet budget with live in-flight leases.
        let leases = (0..128)
            .map(|_| match gate.try_reserve(1, 1) {
                BackpressureOutcome::Admitted(lease) => lease,
                other => panic!("expected a reservation, got {other:?}"),
            })
            .collect::<Vec<_>>();
        assert_eq!(leases.len(), 128);
        let message = wire_ledger_data(Uint256::from(9), 0, vec![(None, vec![1, 2, 3])]);
        assert_eq!(
            adapter.route_ledger_data(1, &message),
            LedgerDataIngressDisposition::Deferred
        );
        assert_eq!(adapter.drain(), 0, "a deferred packet enqueues nothing");
    }

    #[test]
    fn fetch_pack_stash_does_not_enter_a_session() {
        let (mut adapter, cache) = adapter();
        acquired(&mut adapter);
        let data = Bytes::from_static(&[9, 9, 9]);
        let hash = protocol::sha512_half(&data);
        adapter.stash_fetch_pack(hash, data.clone());
        assert_eq!(adapter.drain(), 0, "a by-hash reply enqueues no event");
        assert_eq!(
            cache.get_fetch_pack(hash),
            Some(data.to_vec()),
            "the pack is retrievable by its content hash"
        );
    }

    #[test]
    fn get_ledger_requests_are_framed_with_li_base() {
        let mut counter = IdCounter::new();
        let session = session(1);
        let request = PeerRequest::new(
            session,
            OperationRef::new(
                session,
                OperationKind::PeerRequest,
                counter.next_id(),
                counter.next_id(),
            ),
            PeerId::new(7),
            LedgerDataRequest::GetLedger {
                sequence: Some(SEQ),
            },
        );
        let frame = frame_ledger_request(&BTreeMap::new(), &request).expect("GetLedger must frame");
        match frame.payload {
            overlay::ProtocolPayload::GetLedger(tm) => {
                assert_eq!(tm.itype, LI_BASE);
                assert_eq!(tm.ledger_seq, Some(SEQ));
                assert_eq!(
                    tm.ledger_hash.as_deref(),
                    Some(session.target_hash().data().as_slice())
                );
            }
            other => panic!("expected GetLedger, got {other:?}"),
        }
    }

    #[test]
    fn ledger_node_requests_preserve_node_ids_and_frame_as_state_ledger_data() {
        let mut counter = IdCounter::new();
        let session = session(1);
        let node_id = SHAMapNodeId::default();
        let request = PeerRequest::new(
            session,
            OperationRef::new(
                session,
                OperationKind::PeerRequest,
                counter.next_id(),
                counter.next_id(),
            ),
            PeerId::new(7),
            LedgerDataRequest::GetLedgerNodes {
                kind: ledger::TreeKind::State,
                node_ids: vec![node_id],
                sequence: SEQ,
                query_depth: 1,
                indirect: true,
            },
        );
        let frame =
            frame_ledger_request(&BTreeMap::new(), &request).expect("node request must frame");
        match frame.payload {
            overlay::ProtocolPayload::GetLedger(tm) => {
                assert_eq!(tm.itype, LI_AS_NODE);
                assert_eq!(tm.ledger_seq, Some(SEQ));
                assert_eq!(tm.node_i_ds, vec![node_id.get_raw_string()]);
                assert_eq!(tm.query_depth, Some(1));
                assert_eq!(tm.query_type, Some(QT_INDIRECT));
            }
            other => panic!("expected GetLedger, got {other:?}"),
        }
    }

    #[test]
    fn get_nodes_requests_are_framed_with_the_promoted_sequence() {
        let mut counter = IdCounter::new();
        let session = session(1);
        let hashes = vec![Uint256::from(0xAB), Uint256::from(0xCD)];
        let nodes = vec![
            acquisition::LedgerNodeRequest::new(hashes[0], ledger::TreeKind::State),
            acquisition::LedgerNodeRequest::new(hashes[1], ledger::TreeKind::State),
        ];
        let request = PeerRequest::new(
            session,
            OperationRef::new(
                session,
                OperationKind::PeerRequest,
                counter.next_id(),
                counter.next_id(),
            ),
            PeerId::new(7),
            LedgerDataRequest::GetNodes {
                nodes,
                sequence: Some(SEQ),
            },
        );
        let frame = frame_ledger_request(&BTreeMap::new(), &request).expect("GetNodes must frame");
        match frame.payload {
            overlay::ProtocolPayload::GetObjects(tm) => {
                assert!(tm.query, "a GetNodes request is a query");
                assert_eq!(
                    tm.ledger_hash.as_deref(),
                    Some(session.target_hash().data().as_slice())
                );
                assert_eq!(tm.objects.len(), 2);
                assert_eq!(
                    tm.objects[0].hash.as_deref(),
                    Some(hashes[0].data().as_slice())
                );
                assert_eq!(
                    tm.objects[1].hash.as_deref(),
                    Some(hashes[1].data().as_slice())
                );
                assert_eq!(tm.objects[0].ledger_seq, Some(SEQ));
                assert_eq!(tm.r#type, 4, "state-node object-by-hash type");
            }
            other => panic!("expected GetObjects, got {other:?}"),
        }
    }

    #[test]
    fn mixed_tree_kind_request_is_rejected_before_wire_framing() {
        let mut counter = IdCounter::new();
        let session = session(1);
        let request = PeerRequest::new(
            session,
            OperationRef::new(
                session,
                OperationKind::PeerRequest,
                counter.next_id(),
                counter.next_id(),
            ),
            PeerId::new(7),
            LedgerDataRequest::GetNodes {
                nodes: vec![
                    acquisition::LedgerNodeRequest::new(Uint256::from(1), ledger::TreeKind::State),
                    acquisition::LedgerNodeRequest::new(
                        Uint256::from(2),
                        ledger::TreeKind::Transaction,
                    ),
                ],
                sequence: Some(SEQ),
            },
        );
        assert!(frame_ledger_request(&BTreeMap::new(), &request).is_none());
    }
    #[test]
    fn unknown_sequence_still_frames_a_base_request() {
        let mut counter = IdCounter::new();
        let session = session(1);
        let request = PeerRequest::new(
            session,
            OperationRef::new(
                session,
                OperationKind::PeerRequest,
                counter.next_id(),
                counter.next_id(),
            ),
            PeerId::new(7),
            LedgerDataRequest::GetLedger { sequence: None },
        );
        let frame = frame_ledger_request(&BTreeMap::new(), &request)
            .expect("unknown target must frame a Base request");
        match frame.payload {
            overlay::ProtocolPayload::GetLedger(tm) => {
                assert_eq!(tm.itype, LI_BASE);
                assert_eq!(tm.ledger_seq, None);
            }
            other => panic!("expected GetLedger Base, got {other:?}"),
        }
    }

    #[test]
    fn transaction_node_request_frames_a_transaction_object_type() {
        let mut counter = IdCounter::new();
        let session = session(1);
        let request = PeerRequest::new(
            session,
            OperationRef::new(
                session,
                OperationKind::PeerRequest,
                counter.next_id(),
                counter.next_id(),
            ),
            PeerId::new(7),
            LedgerDataRequest::GetNodes {
                nodes: vec![acquisition::LedgerNodeRequest::new(
                    Uint256::from(1),
                    ledger::TreeKind::Transaction,
                )],
                sequence: Some(SEQ),
            },
        );
        let frame =
            frame_ledger_request(&BTreeMap::new(), &request).expect("transaction node must frame");
        match frame.payload {
            overlay::ProtocolPayload::GetObjects(tm) => {
                assert_eq!(tm.r#type, 3, "transaction-node object-by-hash type");
            }
            other => panic!("expected GetObjects, got {other:?}"),
        }
    }

    #[test]
    fn coordinator_request_reaches_a_refreshed_peer_without_legacy_membership() {
        use std::net::{IpAddr, Ipv4Addr, SocketAddr};

        use protocol::{KeyType, SecretKey, derive_public_key};

        let peer = overlay::PeerImp::new(
            7,
            SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), 6007),
            derive_public_key(KeyType::Secp256k1, &SecretKey::from_bytes([7; 32]))
                .expect("peer public key"),
            "coordinator-available-peer",
        );
        let peers = SimplePeerSet::new(Vec::new());
        let mut port = OverlayLedgerRequestPort::new(peers);
        port.refresh_peers(vec![Arc::clone(&peer) as Arc<dyn Peer>]);

        let session = session(7);
        let mut counter = IdCounter::new();
        port.send_ledger_request(PeerRequest::new(
            session,
            OperationRef::new(
                session,
                OperationKind::PeerRequest,
                counter.next_id(),
                counter.next_id(),
            ),
            PeerId::new(7),
            LedgerDataRequest::GetLedger {
                sequence: Some(SEQ),
            },
        ));

        assert_eq!(
            peer.queued_messages().len(),
            1,
            "coordinator-targeted delivery must not depend on legacy add_peers membership"
        );
    }

    fn broker_test_node_store_with(
        path: &str,
        scheduler: Arc<dyn nodestore::Scheduler>,
    ) -> SHAMapStoreNodeStore {
        use basics::basic_config::Section;
        use nodestore::{Manager as _, ManagerImp, NullJournal};

        let manager = ManagerImp::new();
        let mut config = Section::new("node_db");
        config.set("type", "Memory");
        config.set("path", path);
        SHAMapStoreNodeStore::Single(
            manager
                .make_database(0, scheduler, 1, &config, Arc::new(NullJournal))
                .expect("memory node store"),
        )
    }

    fn broker_test_node_store(path: &str) -> SHAMapStoreNodeStore {
        broker_test_node_store_with(path, Arc::new(nodestore::DummyScheduler))
    }

    /// Retains scheduled NodeStore tasks so a test can prove read submission
    /// occurred without racing its typed completion against cancellation.
    #[derive(Default)]
    struct BrokerCaptureScheduler {
        queued: Mutex<VecDeque<Arc<dyn nodestore::Task>>>,
    }

    impl BrokerCaptureScheduler {
        fn pending(&self) -> usize {
            self.queued.lock().expect("captured task lock").len()
        }

        fn run_next(&self) -> bool {
            let task = self.queued.lock().expect("captured task lock").pop_front();
            if let Some(task) = task {
                task.perform_scheduled_task();
                true
            } else {
                false
            }
        }
    }

    impl nodestore::Scheduler for BrokerCaptureScheduler {
        fn schedule_task(&self, task: Arc<dyn nodestore::Task>) {
            self.queued
                .lock()
                .expect("captured task lock")
                .push_back(task);
        }

        fn on_fetch(&self, _report: nodestore::FetchReport) {}

        fn on_batch_write(&self, _report: nodestore::BatchWriteReport) {}
    }

    #[test]
    fn broker_read_maps_completions_and_cancellation_releases_tickets() {
        let broker = NodeReadBroker::new(ReadBrokerConfig::default()).expect("broker");
        let tickets = BrokerTicketState::default();
        let (tx, rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let scheduler = Arc::new(BrokerCaptureScheduler::default());
        let mut port = BrokerReadPort::new(
            broker.clone(),
            tickets.clone(),
            broker_test_node_store_with("broker-read-cancel", scheduler.clone()),
            tx,
        );

        let session = session(2);
        let mut counter = IdCounter::new();
        let operation = OperationRef::new(
            session,
            OperationKind::Read,
            counter.next_id(),
            counter.next_id(),
        );
        let request = ReadRequest::new(
            operation,
            SHAMapHash::new(Uint256::from(0x11)),
            1,
            StoreGeneration::new(1),
            ReadPriority::Consensus,
        );

        let mut dispatcher = BrokerCancellationDispatcher::new(
            broker.clone(),
            tickets.clone(),
            port.node_store.clone(),
        );
        port.submit_read(request);
        assert_eq!(
            broker.snapshot().in_flight_keys,
            1,
            "accepted broker work is physically submitted after broker admission"
        );
        assert_eq!(
            tickets
                .tickets
                .lock()
                .unwrap()
                .get(&session)
                .map(|set| set.len()),
            Some(1),
            "an in-flight read retains exactly one ticket"
        );

        // Once broker admission has submitted physical I/O, cancellation races
        // a fast store miss. Either terminal outcome is valid for this exact
        // operation; the coordinator rejects it as stale after cancellation.
        dispatcher.session_cancelled(session);
        assert!(
            tickets.tickets.lock().unwrap().get(&session).is_none(),
            "cancellation releases every ticket for the session"
        );
        port.flush_completions();
        let event = rx
            .recv_timeout(std::time::Duration::from_secs(1))
            .expect("completion");
        match event {
            AcquisitionEvent::ReadCompleted(completion) => {
                assert_eq!(completion.operation(), operation);
                assert!(
                    matches!(
                        completion.outcome(),
                        ReadOutcome::Cancelled | ReadOutcome::Settled { node: None }
                    ),
                    "a submitted read may be cancelled or win the cancellation race as a miss"
                );
            }
            other => panic!("expected a read completion, got {other:?}"),
        }
    }

    #[test]
    fn broker_submitted_read_settles_as_an_exact_typed_completion() {
        let broker = NodeReadBroker::new(ReadBrokerConfig::default()).expect("broker");
        let tickets = BrokerTicketState::default();
        let (tx, rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let scheduler = Arc::new(BrokerCaptureScheduler::default());
        let mut port = BrokerReadPort::new(
            broker.clone(),
            tickets,
            broker_test_node_store_with("broker-read-submit", scheduler.clone()),
            tx,
        );
        let session = session(4);
        let mut counter = IdCounter::new();
        let operation = OperationRef::new(
            session,
            OperationKind::Read,
            counter.next_id(),
            counter.next_id(),
        );

        port.submit_read(ReadRequest::new(
            operation,
            SHAMapHash::new(Uint256::from(0x44)),
            1,
            StoreGeneration::new(1),
            ReadPriority::Consensus,
        ));
        assert_eq!(
            broker.snapshot().in_flight_keys,
            1,
            "ready dispatch reaches the NodeStore asynchronous read queue"
        );
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(1);
        let event = loop {
            port.flush_completions();
            match rx.try_recv() {
                Ok(event) => break event,
                Err(mpsc::TryRecvError::Empty) if std::time::Instant::now() < deadline => {
                    std::thread::yield_now();
                }
                Err(error) => panic!("typed NodeStore completion: {error:?}"),
            }
        };
        match event {
            AcquisitionEvent::ReadCompleted(completion) => {
                assert_eq!(completion.operation(), operation);
                assert_eq!(completion.outcome(), &ReadOutcome::Settled { node: None });
            }
            other => panic!("expected a read completion, got {other:?}"),
        }
    }

    #[test]
    fn broker_capacity_backlog_waits_for_real_progress_without_completion_spin() {
        let broker = NodeReadBroker::new(ReadBrokerConfig {
            global_in_flight: 1,
            max_global_retained_logical_subscriptions: 1,
            max_retained_logical_subscriptions: 1,
        })
        .expect("broker");
        let tickets = BrokerTicketState::default();
        let (tx, rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let scheduler = Arc::new(BrokerCaptureScheduler::default());
        let mut port = BrokerReadPort::new(
            broker.clone(),
            tickets.clone(),
            broker_test_node_store_with("broker-capacity-backlog", scheduler),
            tx,
        );
        let mut counter = IdCounter::new();
        let first_session = session(40);
        let second_session = session(41);
        let request = |session, hash, counter: &mut IdCounter| {
            ReadRequest::new(
                OperationRef::new(
                    session,
                    OperationKind::Read,
                    counter.next_id(),
                    counter.next_id(),
                ),
                SHAMapHash::new(Uint256::from(hash)),
                1,
                StoreGeneration::new(1),
                ReadPriority::Consensus,
            )
        };
        port.submit_read(request(first_session, 0x40, &mut counter));
        port.submit_read(request(second_session, 0x41, &mut counter));
        assert_eq!(broker.snapshot().logical_tickets, 1);
        assert_eq!(
            tickets
                .capacity_backlog
                .lock()
                .expect("capacity backlog")
                .len(),
            1
        );
        assert!(
            rx.try_recv().is_err(),
            "capacity pressure must not synthesize a self-waking stale event"
        );

        let mut dispatcher = BrokerCancellationDispatcher::new(
            broker.clone(),
            tickets.clone(),
            port.node_store.clone(),
        );
        dispatcher.session_cancelled(first_session);
        port.flush_completions();
        assert!(
            tickets
                .capacity_backlog
                .lock()
                .expect("capacity backlog")
                .is_empty(),
            "a real settlement reopens capacity for the retained FIFO"
        );
        assert_eq!(broker.snapshot().logical_tickets, 1);
    }

    #[test]
    fn broker_port_consensus_bypasses_retained_history_capacity_backlog() {
        let broker = NodeReadBroker::new(ReadBrokerConfig {
            global_in_flight: ACQ_READS_PER_SCAN + 1,
            max_global_retained_logical_subscriptions: ACQ_READS_PER_SCAN + 1,
            max_retained_logical_subscriptions: ACQ_READS_PER_SCAN + 1,
        })
        .expect("broker");
        let tickets = BrokerTicketState::default();
        let (tx, _rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let scheduler = Arc::new(BrokerCaptureScheduler::default());
        let mut port = BrokerReadPort::new(
            broker.clone(),
            tickets.clone(),
            broker_test_node_store_with("broker-priority-backlog", scheduler),
            tx,
        );
        let mut counter = IdCounter::new();
        let request = |session, hash, priority, counter: &mut IdCounter| {
            ReadRequest::new(
                OperationRef::new(
                    session,
                    OperationKind::Read,
                    counter.next_id(),
                    counter.next_id(),
                ),
                SHAMapHash::new(Uint256::from(hash)),
                1,
                StoreGeneration::new(1),
                priority,
            )
        };
        let first_history = session(50);
        let queued_history = session(51);
        let consensus = session(52);
        port.submit_read(request(
            first_history,
            0x50,
            ReadPriority::History,
            &mut counter,
        ));
        port.submit_read(request(
            queued_history,
            0x51,
            ReadPriority::History,
            &mut counter,
        ));
        port.submit_read(request(
            consensus,
            0x52,
            ReadPriority::Consensus,
            &mut counter,
        ));

        let backlog = tickets.capacity_backlog.lock().expect("capacity backlog");
        assert_eq!(backlog.history.len(), 1);
        assert!(backlog.consensus.is_empty());
        drop(backlog);
        assert_eq!(
            tickets
                .tickets
                .lock()
                .expect("broker tickets")
                .get(&consensus)
                .map(Vec::len),
            Some(1),
            "Consensus must use its reserved broker lane instead of queueing behind History"
        );
        assert!(broker.snapshot().in_flight_keys <= ACQ_READS_PER_SCAN + 1);
    }

    #[test]
    fn exact_binding_promotes_generic_capacity_backlog_before_retry() {
        let broker = NodeReadBroker::new(ReadBrokerConfig {
            global_in_flight: 1,
            max_global_retained_logical_subscriptions: 1,
            max_retained_logical_subscriptions: 1,
        })
        .expect("broker");
        let tickets = BrokerTicketState::default();
        let (tx, _rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let scheduler = Arc::new(BrokerCaptureScheduler::default());
        let mut port = BrokerReadPort::new(
            broker.clone(),
            tickets.clone(),
            broker_test_node_store_with("broker-exact-promotion", scheduler),
            tx,
        );
        let mut counter = IdCounter::new();
        let request = |session, hash, priority, counter: &mut IdCounter| {
            ReadRequest::new(
                OperationRef::new(
                    session,
                    OperationKind::Read,
                    counter.next_id(),
                    counter.next_id(),
                ),
                SHAMapHash::new(Uint256::from(hash)),
                1,
                StoreGeneration::new(1),
                priority,
            )
        };
        let blocker = session(60);
        let exact = session(61);
        port.submit_read(request(
            blocker,
            0x60,
            ReadPriority::Consensus,
            &mut counter,
        ));
        port.submit_read(request(exact, 0x61, ReadPriority::History, &mut counter));
        assert_eq!(
            tickets
                .capacity_backlog
                .lock()
                .expect("capacity backlog")
                .history
                .len(),
            1
        );
        assert_eq!(port.promote_session_priority(exact), 1);
        let backlog = tickets.capacity_backlog.lock().expect("capacity backlog");
        assert!(backlog.history.is_empty());
        assert_eq!(backlog.consensus.len(), 1);
        drop(backlog);

        let mut dispatcher = BrokerCancellationDispatcher::new(
            broker.clone(),
            tickets.clone(),
            port.node_store.clone(),
        );
        dispatcher.session_cancelled(blocker);
        port.flush_completions();
        assert!(
            tickets
                .capacity_backlog
                .lock()
                .expect("capacity backlog")
                .is_empty()
        );
        assert!(
            broker.snapshot().logical_tickets <= 1,
            "the promoted retry must remain within the physical/logical bound"
        );
    }

    #[test]
    fn retained_generic_promotion_submits_newly_admitted_physical_read() {
        let broker = NodeReadBroker::new(ReadBrokerConfig {
            global_in_flight: ACQ_READS_PER_SCAN + 1,
            max_global_retained_logical_subscriptions: ACQ_READS_PER_SCAN * 2 + 1,
            max_retained_logical_subscriptions: ACQ_READS_PER_SCAN + 1,
        })
        .expect("broker");
        let tickets = BrokerTicketState::default();
        let (tx, _rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let scheduler = Arc::new(BrokerCaptureScheduler::default());
        let mut port = BrokerReadPort::new(
            broker.clone(),
            tickets.clone(),
            broker_test_node_store_with("broker-promote-submit", scheduler.clone()),
            tx,
        );
        let mut counter = IdCounter::new();
        let request = |session, hash, counter: &mut IdCounter| {
            ReadRequest::new(
                OperationRef::new(
                    session,
                    OperationKind::Read,
                    counter.next_id(),
                    counter.next_id(),
                ),
                SHAMapHash::new(Uint256::from(hash)),
                1,
                StoreGeneration::new(1),
                ReadPriority::History,
            )
        };
        let blocker = session(70);
        let exact = session(71);
        port.submit_read(request(blocker, 0x70, &mut counter));
        port.submit_read(request(exact, 0x71, &mut counter));
        assert_eq!(broker.snapshot().in_flight_keys, 1);
        assert_eq!(broker.snapshot().queued_keys, 1);
        assert!(
            tickets
                .capacity_backlog
                .lock()
                .expect("capacity backlog")
                .is_empty(),
            "the Generic read must be retained inside the broker, not the port backlog"
        );

        assert_eq!(port.promote_session_priority(exact), 1);
        assert_eq!(broker.snapshot().queued_keys, 0);
        assert_eq!(broker.snapshot().metrics.physical_dispatched, 2);
        assert_eq!(
            broker.ready_dispatch_count(),
            0,
            "the production port must hand the newly admitted dispatch to NodeStore"
        );
    }

    #[test]
    fn cancellation_submits_next_broker_retained_physical_read() {
        let broker = NodeReadBroker::new(ReadBrokerConfig {
            global_in_flight: 1,
            max_global_retained_logical_subscriptions: 2,
            max_retained_logical_subscriptions: 2,
        })
        .expect("broker");
        let tickets = BrokerTicketState::default();
        let (tx, _rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let scheduler = Arc::new(BrokerCaptureScheduler::default());
        let mut port = BrokerReadPort::new(
            broker.clone(),
            tickets.clone(),
            broker_test_node_store_with("broker-cancel-submit", scheduler.clone()),
            tx,
        );
        let mut counter = IdCounter::new();
        let request = |session, hash, counter: &mut IdCounter| {
            ReadRequest::new(
                OperationRef::new(
                    session,
                    OperationKind::Read,
                    counter.next_id(),
                    counter.next_id(),
                ),
                SHAMapHash::new(Uint256::from(hash)),
                1,
                StoreGeneration::new(1),
                ReadPriority::Consensus,
            )
        };
        let first = session(72);
        let next = session(73);
        port.submit_read(request(first, 0x72, &mut counter));
        port.submit_read(request(next, 0x73, &mut counter));
        assert_eq!(broker.snapshot().in_flight_keys, 1);
        assert_eq!(broker.snapshot().queued_keys, 1);

        let mut dispatcher =
            BrokerCancellationDispatcher::new(broker.clone(), tickets, port.node_store.clone());
        dispatcher.session_cancelled(first);
        assert_eq!(
            broker.snapshot().in_flight_keys,
            1,
            "the uncancellable physical read must retain its capacity tombstone"
        );
        assert_eq!(broker.snapshot().queued_keys, 1);
        assert_eq!(
            broker.ready_dispatch_count(),
            0,
            "cancellation must not over-admit while the physical callback is outstanding"
        );
        assert!(broker.complete(
            ReadKey::new(Uint256::from(0x72), 1, 1),
            BrokerReadOutcome::Miss,
        ));
        assert_eq!(broker.ready_dispatch_count(), 1);
        port.flush_completions();
        assert_eq!(
            broker.ready_dispatch_count(),
            0,
            "settling the tombstone must admit and submit the retained successor"
        );
    }

    #[test]
    fn validation_recovery_binding_promotes_existing_generic_session_once() {
        let (mut adapter, _) = adapter();
        adapter.connectivity(&[1]);
        let ledger = target(0x81, 81);
        let effects = adapter.acquire_requested(ledger, AcquireReason::Generic);
        let session = effects
            .iter()
            .find_map(|effect| match effect {
                AcquisitionEffect::SessionStarted(session) => Some(*session),
                _ => None,
            })
            .expect("Generic session");
        assert!(adapter.reads.promoted_sessions.is_empty());

        adapter.validation_recovery_target(Some(ledger));
        assert_eq!(adapter.runner.validation_recovery_session(), Some(session));
        assert_eq!(adapter.reads.promoted_sessions, vec![session]);

        adapter.validation_recovery_target(Some(ledger));
        assert_eq!(
            adapter.reads.promoted_sessions,
            vec![session],
            "a stable exact owner must not repeatedly rescan broker tickets"
        );
    }

    #[test]
    fn rejected_broker_admission_reports_a_terminal_read() {
        let broker = NodeReadBroker::new(ReadBrokerConfig::default()).expect("broker");
        broker.stop();
        let tickets = BrokerTicketState::default();
        let (tx, rx) = mpsc::sync_channel(CONTROL_EVENT_QUEUE_CAPACITY);
        let mut port = BrokerReadPort::new(
            broker,
            tickets,
            broker_test_node_store("broker-read-rejected"),
            tx,
        );

        let session = session(3);
        let mut counter = IdCounter::new();
        let operation = OperationRef::new(
            session,
            OperationKind::Read,
            counter.next_id(),
            counter.next_id(),
        );
        let request = ReadRequest::new(
            operation,
            SHAMapHash::new(Uint256::from(0x22)),
            1,
            StoreGeneration::new(1),
            ReadPriority::Consensus,
        );
        port.submit_read(request);
        port.flush_completions();
        let event = rx
            .recv_timeout(std::time::Duration::from_secs(1))
            .expect("terminal completion");
        match event {
            AcquisitionEvent::ReadCompleted(completion) => {
                assert_eq!(completion.operation(), operation);
                assert_eq!(completion.outcome(), &ReadOutcome::Stale);
            }
            other => panic!("expected a read completion, got {other:?}"),
        }
    }

    #[test]
    fn broker_read_key_matches_route_generation_scope() {
        // The read key isolates by (hash, ledger sequence, store generation), so
        // two sessions at different generations never coalesce.
        let session_a = SessionRef::new(
            RunEpoch::new(1),
            SessionId::new(1),
            Uint256::from(5),
            PlanEpoch::new(1),
            StoreGeneration::new(1),
        );
        let session_b = SessionRef::new(
            RunEpoch::new(1),
            SessionId::new(2),
            Uint256::from(5),
            PlanEpoch::new(1),
            StoreGeneration::new(2),
        );
        assert_ne!(session_a.store_generation(), session_b.store_generation());
        let key_a = ReadKey::new(
            *SHAMapHash::new(Uint256::from(0x33)).as_uint256(),
            1,
            session_a.store_generation().get(),
        );
        let key_b = ReadKey::new(
            *SHAMapHash::new(Uint256::from(0x33)).as_uint256(),
            1,
            session_b.store_generation().get(),
        );
        assert_ne!(key_a, key_b);
    }

    #[test]
    fn node_id_preservation_round_trips_the_wire() {
        // Root node ids survive wire -> InboundLedgerNodeData unchanged.
        let raw = SHAMapNodeId::default().get_raw_string().to_vec();
        assert_eq!(
            deserialize_shamap_node_id(&raw).expect("default root id deserializes"),
            SHAMapNodeId::default()
        );
        let node = decode_wire_ledger_node(
            &TmLedgerNode {
                nodedata: valid_inner_wire(),
                nodeid: Some(raw.clone()),
                ..TmLedgerNode::default()
            },
            InboundLedgerDataType::StateNode,
            0,
        )
        .expect("a node with an id decodes");
        assert_eq!(node.node_id.as_deref(), Some(raw.as_slice()));
    }
}
